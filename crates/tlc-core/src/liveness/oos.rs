//! Port of `tlc2.tool.liveness.{OrderOfSolution, PossibleErrorModel}` and `Liveness.processLiveness`: normalize the
//! formula `livespec /\ ~livecheck` into "orders of solution" (a tableau, its promises and the state / action
//! predicates the behavior graph has to record).

use super::ln::*;
use super::tableau::TbGraph;
use super::translate::{TrErr, Translator};
use crate::ec;
use crate::eval::Ev;
use crate::spec::Setup;
use crate::value::*;

/// `PossibleErrorModel`: indexes into `Oos::check_state` / `Oos::check_action`
pub struct Pem {
    /// `<>[]A`
    pub ea_action: Vec<usize>,
    /// `[]<>S`
    pub ae_state: Vec<usize>,
    /// `[]<>A`
    pub ae_action: Vec<usize>,
}

impl Pem {
    pub fn is_empty(&self) -> bool {
        self.ea_action.is_empty() && self.ae_state.is_empty() && self.ae_action.is_empty()
    }
}

/// everything the model checker needs for the temporal properties
#[derive(Default)]
pub struct LiveSpec {
    pub oss: Vec<Oos>,
    /// the translated PROPERTY formulas (positive form, for `Liveness.findViolatedProperties`)
    pub props: Vec<(String, Ln)>,
}

pub struct Oos {
    pub tableau: Option<TbGraph>,
    pub promises: Vec<Ln>,
    pub contains_box_in_promise: bool,
    pub check_state: Vec<Ln>,
    pub check_action: Vec<Ln>,
    pub pems: Vec<Pem>,
}

impl Oos {
    /// `checkState(tool, state)`
    pub fn check_state_res(&self, ev: &Ev, s: &[Value]) -> R<Vec<bool>> {
        let mut r = Vec::with_capacity(self.check_state.len());
        for c in &self.check_state {
            r.push(c.eval(ev, s, &[])?);
        }
        Ok(r)
    }

    /// `checkAction(tool, s0, s1)`
    pub fn check_action_res(&self, ev: &Ev, s0: &[Value], s1: &[Value]) -> R<Vec<bool>> {
        let mut r = Vec::with_capacity(self.check_action.len());
        for c in &self.check_action {
            r.push(c.eval(ev, s0, s1)?);
        }
        Ok(r)
    }

    pub fn has_empty_pem(&self) -> bool {
        self.pems.iter().any(|p| p.is_empty())
    }

    /// `hasEmptyPEMAndBoxFreePromises`
    pub fn has_empty_pem_and_box_free_promises(&self) -> bool {
        if self.contains_box_in_promise {
            return false;
        }
        self.pems.iter().all(|p| p.is_empty())
    }
}

fn contains_box(n: &Ln) -> bool {
    match &*n.0 {
        LnNode::All(_) => true,
        LnNode::Even(b) | LnNode::Neg(b) | LnNode::Next(b) => contains_box(b),
        LnNode::Conj(v) | LnNode::Disj(v) => v.iter().any(contains_box),
        _ => false,
    }
}

#[derive(Default)]
struct OsExprPem {
    ea_action: Vec<Ln>,
    ae_state: Vec<Ln>,
    ae_action: Vec<Ln>,
    tfs: Vec<Ln>,
}

impl OsExprPem {
    fn to_tfs(&self) -> Option<Ln> {
        match self.tfs.len() {
            0 => None,
            1 => Some(self.tfs[0].clone()),
            _ => Some(Ln::conj_flat(self.tfs.iter().cloned())),
        }
    }
}

/// `Liveness.classifyExpr`
fn classify_expr(ln: &Ln, pem: &mut OsExprPem) -> Result<(), TrErr> {
    match &*ln.0 {
        LnNode::Even(b1) => {
            if let LnNode::All(b2) = &*b1.0 {
                if b2.level() < LEVEL_TEMPORAL {
                    pem.ea_action.push(b2.clone());
                    return Ok(());
                }
            }
        }
        LnNode::All(b1) => {
            if let LnNode::Even(b2) = &*b1.0 {
                let level = b2.level();
                if level <= LEVEL_VAR {
                    pem.ae_state.push(b2.clone());
                    return Ok(());
                }
                if level == LEVEL_ACTION {
                    pem.ae_action.push(b2.clone());
                    return Ok(());
                }
            }
        }
        _ => {}
    }
    if ln.contains_action() {
        return Err(TrErr::Code(ec::TLC_LIVE_WRONG_FORMULA_FORMAT, "Temporal formulas containing actions must be of forms <>[]A or []<>A.".into()));
    }
    pem.tfs.push(ln.clone());
    Ok(())
}

fn add_to_bin(check: &Ln, bin: &mut Vec<Ln>) -> usize {
    for (i, ln) in bin.iter().enumerate() {
        if check.equals(ln) {
            return i;
        }
    }
    bin.push(check.clone());
    bin.len() - 1
}

/// `Liveness.parseLiveness`: `livespec /\ ~livecheck`; `None` when there is nothing to check
fn parse_liveness(tr: &mut Translator, fairs: &[tla_sany::sem::Expr], checks: &[tla_sany::sem::Expr], bounds: &[Vec<(std::rc::Rc<tla_sany::sem::Param>, Value)>]) -> Result<Option<Ln>, TrErr> {
    let mut lnc: Vec<Ln> = vec![];
    for f in fairs {
        let ln = tr.translate(f)?;
        add_conj(&mut lnc, ln);
    }
    if checks.is_empty() {
        if fairs.is_empty() {
            return Ok(None);
        }
    } else if checks.len() == 1 {
        tr.set_bound(bounds[0].clone());
        let ln = tr.translate(&checks[0])?;
        tr.set_bound(vec![]);
        if lnc.is_empty() {
            return Ok(Some(Ln::neg(ln)));
        }
        add_conj(&mut lnc, Ln::neg(ln));
    } else {
        let mut lnd: Vec<Ln> = vec![];
        for (c, bd) in checks.iter().zip(bounds.iter()) {
            tr.set_bound(bd.clone());
            let ln = tr.translate(c)?;
            tr.set_bound(vec![]);
            add_disj(&mut lnd, Ln::neg(ln));
        }
        if lnc.is_empty() {
            return Ok(Some(Ln::new(LnNode::Disj(lnd))));
        }
        add_conj(&mut lnc, Ln::new(LnNode::Disj(lnd)));
    }
    Ok(Some(Ln::new(LnNode::Conj(lnc))))
}

/// `Liveness.processLiveness` (+ the positive translation of each property)
pub fn process_liveness(setup: &mut Setup) -> Result<LiveSpec, TrErr> {
    let oss = process_oss(setup)?;
    let mut props = vec![];
    let named: Vec<(String, tla_sany::sem::Expr)> = setup.properties.clone();
    let bounds: Vec<_> = setup.properties_bound.clone();
    for ((name, e), bd) in named.into_iter().zip(bounds.into_iter()) {
        let mut tr = Translator::new(setup);
        tr.set_bound(bd);
        if let Ok(ln) = tr.translate(&e) {
            props.push((name, ln));
        }
    }
    Ok(LiveSpec { oss, props })
}

fn process_oss(setup: &mut Setup) -> Result<Vec<Oos>, TrErr> {
    let fairs: Vec<_> = setup.spec_temporal.clone();
    let checks: Vec<_> = setup.properties.iter().map(|(_, e)| e.clone()).collect();
    let bounds: Vec<_> = setup.properties_bound.clone();
    let mut tr = Translator::new(setup);
    let lexpr = match parse_liveness(&mut tr, &fairs, &checks, &bounds)? {
        None => return Ok(vec![]),
        Some(l) => l,
    };
    drop(tr);
    // I: tag the state and action predicates (equality)
    lexpr.tag_expr(1);
    // II & III: negations to the leaves, simplify, disjunctive normal form
    let dnf_err = || TrErr::Handle("because it exceeds the maximum supported size in disjunctive normal form.".into());
    let lexpr = lexpr.push_neg_b(false).simplify().to_dnf().map_err(|_| dnf_err())?;
    if let LnNode::Bool(false) = &*lexpr.0 {
        return Ok(vec![]);
    }
    let dnf: Vec<Ln> = match &*lexpr.0 {
        LnNode::Disj(v) => v.clone(),
        _ => vec![lexpr.clone()],
    };
    // IV: classify every disjunct
    let mut pems: Vec<OsExprPem> = vec![];
    let mut tfs: Vec<Option<Ln>> = vec![];
    for body in &dnf {
        let ln = body.flatten_single();
        let mut pem = OsExprPem::default();
        if let LnNode::Conj(v) = &*ln.0 {
            for x in v {
                classify_expr(x, &mut pem)?;
            }
        } else {
            classify_expr(&ln, &mut pem)?;
        }
        tfs.push(pem.to_tfs());
        pems.push(pem);
    }
    // V: lump together the disjuncts with the same temporal formula
    let mut tfbin: Vec<Option<Ln>> = vec![];
    let mut pembin: Vec<Vec<usize>> = vec![];
    for (i, tf) in tfs.iter().enumerate() {
        let mut found = None;
        for (j, tf0) in tfbin.iter().enumerate() {
            let same = match (tf, tf0) {
                (None, None) => true,
                (Some(a), Some(b)) => a.equals(b),
                _ => false,
            };
            if same {
                found = Some(j);
                break;
            }
        }
        let j = match found {
            Some(j) => j,
            None => {
                tfbin.push(tf.clone());
                pembin.push(vec![]);
                tfbin.len() - 1
            }
        };
        pembin[j].push(i);
    }
    // VI: an order of solution for each temporal formula
    let mut oss: Vec<Oos> = vec![];
    for (i, tf) in tfbin.iter().enumerate() {
        let (tableau, promises) = match tf {
            None => (None, vec![]),
            Some(tf) => {
                let tf1 = tf.make_binary();
                let tbg = TbGraph::new(tf1.clone())?;
                let mut promises = vec![];
                tf1.extract_promises(&mut promises);
                (Some(tbg), promises)
            }
        };
        let contains_box_in_promise = promises.iter().any(|p| match &*p.0 {
            LnNode::Even(b) => contains_box(b),
            _ => false,
        });
        // VII: the state / action predicates to be recorded in the behavior graph
        let mut state_bin: Vec<Ln> = vec![];
        let mut action_bin: Vec<Ln> = vec![];
        let mut oos_pems = vec![];
        for &pi in &pembin[i] {
            let pem = &pems[pi];
            let ae_action: Vec<usize> = pem.ae_action.iter().map(|c| add_to_bin(c, &mut action_bin)).collect();
            let ae_state: Vec<usize> = pem.ae_state.iter().map(|c| add_to_bin(c, &mut state_bin)).collect();
            let ea_action: Vec<usize> = pem.ea_action.iter().map(|c| add_to_bin(c, &mut action_bin)).collect();
            oos_pems.push(Pem { ea_action, ae_state, ae_action });
        }
        oss.push(Oos { tableau, promises, contains_box_in_promise, check_state: state_bin, check_action: action_bin, pems: oos_pems });
    }
    Ok(oss)
}
