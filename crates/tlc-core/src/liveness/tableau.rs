//! Port of `tlc2.tool.liveness.{TBPar, TBParVec, TBGraph, TBGraphNode, TBTriple}`: the tableau of a temporal formula
//! (Manna & Pnueli, "Temporal Verification of Reactive Systems: Safety", Sec. 5.5 particle tableaux).

use super::ln::*;
use crate::eval::Ev;
use crate::value::*;

/// a set of formulas (`TBPar`); membership is `LiveExprNode.equals`
#[derive(Clone, Default)]
pub struct TbPar(pub Vec<Ln>);

struct Triple {
    a: Ln,
    b: Ln,
    c: Ln,
}

impl TbPar {
    pub fn member(&self, e: &Ln) -> bool {
        self.0.iter().any(|x| e.equals(x))
    }
    fn contains(&self, o: &TbPar) -> bool {
        o.0.iter().all(|x| self.member(x))
    }
    pub fn equals(&self, o: &TbPar) -> bool {
        self.contains(o) && o.contains(self)
    }
    fn append(&self, ln: Ln) -> TbPar {
        let mut v = self.0.clone();
        v.push(ln);
        TbPar(v)
    }
    fn append2(&self, a: Ln, b: Ln) -> TbPar {
        let mut v = self.0.clone();
        v.push(a);
        v.push(b);
        TbPar(v)
    }

    /// `particleClosure()`
    pub fn particle_closure(&self) -> R<Vec<TbPar>> {
        let pos = self.positive_closure()?;
        let alphas = pos.alpha_triples();
        let betas = pos.beta_triples();
        Ok(self.particle_closure3(self, &alphas, &betas))
    }

    fn particle_closure3(&self, terms: &TbPar, alphas: &[Triple], betas: &[Triple]) -> Vec<TbPar> {
        if !terms.is_locally_consistent() {
            return vec![];
        }
        // Java: `terms1 = terms` aliases `terms` until the first `append`
        let mut terms1 = terms.clone();
        let mut aliased = true;
        let mut i = 0;
        while i < terms1.0.len() {
            let ln = terms1.0[i].clone();
            let (mut k1, mut k2): (Option<Ln>, Option<Ln>) = (None, None);
            match &*ln.0 {
                LnNode::All(b) => {
                    k1 = Some(b.clone());
                    k2 = Some(Ln::next(ln.clone()));
                }
                LnNode::Conj(v) => {
                    k1 = Some(v[0].clone());
                    k2 = Some(v[1].clone());
                }
                _ => {}
            }
            if let (Some(k1), Some(k2)) = (k1, k2) {
                if terms1.member(&k1) {
                    if !terms1.member(&k2) {
                        terms1 = terms1.append(k2);
                        aliased = false;
                    }
                } else if terms1.member(&k2) {
                    terms1 = terms1.append(k1);
                    aliased = false;
                } else {
                    terms1 = terms1.append2(k1, k2);
                    aliased = false;
                }
            }
            i += 1;
        }
        loop {
            let mut done = true;
            for al in alphas {
                if terms1.member(&al.b) && terms1.member(&al.c) && !terms1.member(&al.a) {
                    terms1.0.push(al.a.clone());
                    done = false;
                }
            }
            if done {
                break;
            }
        }
        let grew = !aliased && terms1.0.len() > terms.0.len();
        if grew && !terms1.is_locally_consistent() {
            return vec![];
        }
        self.particle_closure_beta(&terms1, alphas, betas)
    }

    fn particle_closure_beta(&self, terms: &TbPar, alphas: &[Triple], betas: &[Triple]) -> Vec<TbPar> {
        for ln in terms.0.iter() {
            let (k1, k2): (Option<Ln>, Option<Ln>) = match &*ln.0 {
                LnNode::Even(b) => (Some(b.clone()), Some(Ln::next(ln.clone()))),
                LnNode::Disj(v) => (Some(v[0].clone()), Some(v[1].clone())),
                _ => (None, None),
            };
            if let (Some(k1), Some(k2)) = (k1, k2) {
                if !terms.member(&k1) && !terms.member(&k2) {
                    let ps1 = self.particle_closure3(&terms.append(k1), alphas, betas);
                    let ps2 = self.particle_closure3(&terms.append(k2), alphas, betas);
                    return par_vec_union(ps1, ps2);
                }
            }
        }
        for be in betas {
            if (terms.member(&be.b) || terms.member(&be.c)) && !terms.member(&be.a) {
                return self.particle_closure3(&terms.append(be.a.clone()), alphas, betas);
            }
        }
        vec![terms.clone()]
    }

    fn alpha_triples(&self) -> Vec<Triple> {
        let mut ts = vec![];
        for ln in &self.0 {
            match &*ln.0 {
                LnNode::All(b) => ts.push(Triple { a: ln.clone(), b: b.clone(), c: Ln::next(ln.clone()) }),
                LnNode::Conj(v) => ts.push(Triple { a: ln.clone(), b: v[0].clone(), c: v[1].clone() }),
                _ => {}
            }
        }
        ts
    }

    fn beta_triples(&self) -> Vec<Triple> {
        let mut ts = vec![];
        for ln in &self.0 {
            match &*ln.0 {
                LnNode::Even(b) => ts.push(Triple { a: ln.clone(), b: b.clone(), c: Ln::next(ln.clone()) }),
                LnNode::Disj(v) => ts.push(Triple { a: ln.clone(), b: v[0].clone(), c: v[1].clone() }),
                _ => {}
            }
        }
        ts
    }

    fn is_locally_consistent(&self) -> bool {
        let mut pos: Vec<&Ln> = vec![];
        let mut neg: Vec<&Ln> = vec![];
        for ln in &self.0 {
            match &*ln.0 {
                LnNode::State(_) | LnNode::Bool(_) => pos.push(ln),
                LnNode::Neg(b) => {
                    if b.is_state() || b.is_bool() {
                        neg.push(b);
                    }
                }
                _ => {}
            }
        }
        for p in pos {
            if neg.iter().any(|n| p.equals(n)) {
                return false;
            }
        }
        true
    }

    fn positive_closure(&self) -> R<TbPar> {
        let mut tps: Vec<Ln> = self.0.clone();
        let mut result: Vec<Ln> = vec![];
        while let Some(ln) = tps.pop() {
            match &*ln.0 {
                LnNode::Neg(b) => tps.push(b.clone()),
                LnNode::Next(b) => {
                    result.push(ln.clone());
                    tps.push(b.clone());
                }
                LnNode::Even(b) | LnNode::All(b) => {
                    result.push(ln.clone());
                    result.push(Ln::next(ln.clone()));
                    tps.push(b.clone());
                }
                LnNode::Conj(v) | LnNode::Disj(v) => {
                    for x in v {
                        tps.push(x.clone());
                    }
                    result.push(ln.clone());
                }
                LnNode::State(_) | LnNode::Bool(_) => result.push(ln.clone()),
                LnNode::Action(_) => {
                    return fail_code(crate::ec::TLC_LIVE_ENCOUNTERED_ACTIONS, "TLC encountered actions in a temporal formula where only state predicates are allowed.");
                }
            }
        }
        Ok(TbPar(result))
    }

    /// `impliedSuccessors`: the bodies of the `()f` members
    fn implied_successors(&self) -> TbPar {
        TbPar(
            self.0
                .iter()
                .filter_map(|ln| match &*ln.0 {
                    LnNode::Next(b) => Some(b.clone()),
                    _ => None,
                })
                .collect(),
        )
    }

    /// `isFulfilling(promise)`
    pub fn is_fulfilling(&self, promise: &Ln) -> bool {
        if let LnNode::Even(body) = &*promise.0 {
            !self.member(promise) || self.member(body)
        } else {
            true
        }
    }
}

/// `TBParVec.union`
fn par_vec_union(a: Vec<TbPar>, b: Vec<TbPar>) -> Vec<TbPar> {
    let mut res = vec![];
    for x in a.iter() {
        if !b.iter().any(|y| x.equals(y)) {
            res.push(x.clone());
        }
    }
    res.extend(b);
    res
}

pub struct TbNode {
    pub par: TbPar,
    pub nexts: Vec<usize>,
    /// state predicates of the particle (level <= variable level)
    state_preds: Vec<Ln>,
}

impl TbNode {
    fn new(par: TbPar) -> TbNode {
        let state_preds = par.0.iter().filter(|ln| ln.level() <= LEVEL_VAR).cloned().collect();
        TbNode { par, nexts: vec![], state_preds }
    }

    /// `isConsistent(state)`
    pub fn is_consistent(&self, ev: &Ev, s: &[Value]) -> R<bool> {
        for p in &self.state_preds {
            if !p.eval(ev, s, &[])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// `isAccepting`: the empty particle with a self loop only
    pub fn is_accepting(&self, me: usize) -> bool {
        self.par.0.is_empty() && self.nexts.len() == 1 && self.nexts[0] == me
    }
}

pub struct TbGraph {
    pub tf: Ln,
    pub nodes: Vec<TbNode>,
    pub init_cnt: usize,
}

impl TbGraph {
    /// `new TBGraph(tf)`
    pub fn new(tf: Ln) -> R<TbGraph> {
        let init_terms = TbPar(vec![tf.clone()]);
        let pars = init_terms.particle_closure()?;
        let mut g = TbGraph { tf, nodes: pars.into_iter().map(TbNode::new).collect(), init_cnt: 0 };
        g.init_cnt = g.nodes.len();
        let mut i = 0;
        while i < g.nodes.len() {
            let imps = g.nodes[i].par.implied_successors();
            let succs = imps.particle_closure()?;
            for par in succs {
                let dst = g.find_or_create(par);
                g.nodes[i].nexts.push(dst);
            }
            i += 1;
        }
        Ok(g)
    }

    fn find_or_create(&mut self, par: TbPar) -> usize {
        for (i, gn) in self.nodes.iter().enumerate() {
            if par.equals(&gn.par) {
                return i;
            }
        }
        self.nodes.push(TbNode::new(par));
        self.nodes.len() - 1
    }

    pub fn size(&self) -> usize {
        self.nodes.len()
    }
}
