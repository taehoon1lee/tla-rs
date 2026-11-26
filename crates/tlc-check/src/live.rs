//! Port of `tlc2.tool.liveness.{LiveCheck, LiveWorker, TableauDiskGraph, DiskGraph}` (in memory): the behavior graph (the
//! product of the state graph and the tableau), the SCC search that looks for a counterexample of an order of solution
//! and the construction of the lasso (`LiveWorker.printTrace`: prefix, DFS/BFS postfix).

use std::collections::VecDeque;
use std::rc::Rc;
use tlc_core::eval::Ev;
use tlc_core::liveness::oos::{Oos, Pem};
use tlc_core::value::*;

/// Multiplicative hasher for the small integer keys of the graph maps (`(state, tableau node)`, fingerprints, ...): the default
/// SipHash was 4 % of a liveness run (H16).  The iteration order of these maps is never observable (it was random before).
#[derive(Default, Clone, Copy)]
pub struct FxHasher(u64);

const FX_K: u64 = 0x517c_c1b7_2722_0a95;

impl FxHasher {
    #[inline(always)]
    fn add(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(FX_K);
    }
}

impl std::hash::Hasher for FxHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.add(*b as u64);
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_i32(&mut self, i: i32) {
        self.add(i as u32 as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
}

pub type HashMap<K, V> = std::collections::HashMap<K, V, std::hash::BuildHasherDefault<FxHasher>>;
pub type HashSet<K> = std::collections::HashSet<K, std::hash::BuildHasherDefault<FxHasher>>;

/// access to the stored states of the breadth-first search
pub trait States {
    fn vals(&self, i: u32) -> &[Value];
    /// the successor state actually produced by the `i`-th transition of `s` (with a VIEW a node stands for several states)
    fn edge_vals(&self, s: u32, i: usize) -> Option<&[Value]>;
}

struct GNode {
    state: u32,
    tidx: i32,
    succ: Vec<u32>,
    check_state: Vec<bool>,
    /// `succ.len() * alen` bits (`AbstractGraphNode.checks`)
    check_action: Vec<bool>,
}

pub struct Graph {
    nodes: Vec<GNode>,
    init: Vec<u32>,
    alen: usize,
}

impl Graph {
    pub fn size(&self) -> usize {
        self.nodes.len()
    }
    fn check_action_all(&self, n: u32, i: usize, idxs: &[usize]) -> bool {
        let nd = &self.nodes[n as usize];
        idxs.iter().all(|&j| nd.check_action[i * self.alen + j])
    }
    fn check_action_one(&self, n: u32, i: usize, j: usize) -> bool {
        self.nodes[n as usize].check_action[i * self.alen + j]
    }
}

/// the counterexample: states (indices into the BFS state table) and the position the last state loops back to
pub struct Lasso {
    pub states: Vec<u32>,
    pub cycle_pos: usize,
    pub stuttering: bool,
}

/// build the behavior graph of one order of solution (Java: `LiveChecker` / `TableauLiveChecker` fed by `addNextState`)
pub fn build_graph(ev: &Ev, store: &dyn States, succ: &[Vec<u32>], gen: Option<&[Vec<u32>]>, gen_fn: Option<GenFn>, inits: &[u32], oos: &Oos, pre: &[Option<Vec<bool>>]) -> R<Graph> {
    if let (Some(gen), true) = (gen, oos.tableau.is_some()) {
        return build_graph_incr(ev, store, succ, gen, gen_fn, inits, oos, pre);
    }
    let alen = oos.check_action.len();
    let nstates = succ.len();
    // per state: results of the state predicates
    // the state predicates were evaluated when the state was expanded (`pre`)
    let mut state_checks: Vec<Option<Vec<bool>>> = (0..nstates).map(|i| pre.get(i).cloned().flatten()).collect();
    let mut ensure_state = |s: u32, state_checks: &mut Vec<Option<Vec<bool>>>| -> R<()> {
        if state_checks[s as usize].is_none() {
            state_checks[s as usize] = Some(oos.check_state_res(ev, store.vals(s))?);
        }
        Ok(())
    };
    // per (state, successor position): results of the action predicates.  A state-level subformula (e.g.
    // `ENABLED <<A>>_v` of a fairness condition) depends on the source state only: it is evaluated once per state.
    let mut edge_checks: HashMap<(u32, u32), Vec<bool>> = HashMap::default();
    let mut leaf_memo: HashMap<(u32, u32), bool> = HashMap::default();
    let mut action_bits = |s: u32, i: usize, edge_checks: &mut HashMap<(u32, u32), Vec<bool>>| -> R<Vec<bool>> {
        if let Some(v) = edge_checks.get(&(s, i as u32)) {
            return Ok(v.clone());
        }
        let t = succ[s as usize][i];
        let s0 = store.vals(s);
        let s1 = store.edge_vals(s, i).unwrap_or_else(|| store.vals(t));
        let mut v = Vec::with_capacity(oos.check_action.len());
        for c in oos.check_action.iter() {
            v.push(eval_memo(c, ev, s, s0, s1, &mut leaf_memo)?);
        }
        edge_checks.insert((s, i as u32), v.clone());
        Ok(v)
    };
    let mut g = Graph { nodes: vec![], init: vec![], alen };
    match &oos.tableau {
        None => {
            for s in 0..nstates as u32 {
                ensure_state(s, &mut state_checks)?;
                let mut ca = Vec::with_capacity(succ[s as usize].len() * alen);
                for i in 0..succ[s as usize].len() {
                    ca.extend(action_bits(s, i, &mut edge_checks)?);
                }
                g.nodes.push(GNode { state: s, tidx: -1, succ: succ[s as usize].clone(), check_state: state_checks[s as usize].take().unwrap(), check_action: ca });
            }
            g.init = inits.to_vec();
        }
        Some(tb) => {
            let mut index: HashMap<(u32, i32), u32> = HashMap::default();
            // memo: (successor state, tableau node) -> consistent?  (keyed by the edge when edges carry their own states)
            let mut consistent: HashMap<(u64, usize), bool> = HashMap::default();
            let mut is_consistent = |s: u32, vals: Option<&[Value]>, key: u64, t: usize, consistent: &mut HashMap<(u64, usize), bool>| -> R<bool> {
                if let Some(b) = consistent.get(&(key, t)) {
                    return Ok(*b);
                }
                let b = tb.nodes[t].is_consistent(ev, vals.unwrap_or_else(|| store.vals(s)))?;
                consistent.insert((key, t), b);
                Ok(b)
            };
            let mut queue: VecDeque<u32> = VecDeque::new();
            for &s in inits {
                for t in 0..tb.init_cnt {
                    if is_consistent(s, None, s as u64, t, &mut consistent)? {
                        let id = *index.entry((s, t as i32)).or_insert_with(|| {
                            g.nodes.push(GNode { state: s, tidx: t as i32, succ: vec![], check_state: vec![], check_action: vec![] });
                            let id = g.nodes.len() as u32 - 1;
                            queue.push_back(id);
                            id
                        });
                        g.init.push(id);
                    }
                }
            }
            while let Some(n) = queue.pop_front() {
                let (s, t) = (g.nodes[n as usize].state, g.nodes[n as usize].tidx as usize);
                ensure_state(s, &mut state_checks)?;
                let cs = state_checks[s as usize].clone().unwrap();
                let mut succ_nodes: Vec<u32> = vec![];
                let mut ca: Vec<bool> = vec![];
                for (i, &s1) in succ[s as usize].iter().enumerate() {
                    let ev_vals = store.edge_vals(s, i);
                    let key = if ev_vals.is_some() { ((s as u64) << 32 | i as u64) | (1u64 << 63) } else { s1 as u64 };
                    for &t1 in &tb.nodes[t].nexts {
                        if !is_consistent(s1, ev_vals, key, t1, &mut consistent)? {
                            continue;
                        }
                        let id = match index.get(&(s1, t1 as i32)) {
                            Some(&id) => id,
                            None => {
                                g.nodes.push(GNode { state: s1, tidx: t1 as i32, succ: vec![], check_state: vec![], check_action: vec![] });
                                let id = g.nodes.len() as u32 - 1;
                                index.insert((s1, t1 as i32), id);
                                queue.push_back(id);
                                id
                            }
                        };
                        succ_nodes.push(id);
                        ca.extend(action_bits(s, i, &mut edge_checks)?);
                    }
                }
                let nd = &mut g.nodes[n as usize];
                nd.succ = succ_nodes;
                nd.check_state = cs;
                nd.check_action = ca;
            }
        }
    }
    Ok(g)
}

/// the successors of an actual state in generation order: (node, the actual successor state)
pub type GenFn<'a> = &'a dyn Fn(&[Value]) -> R<Vec<(u32, Rc<Vec<Value>>)>>;

/// Port of `LiveCheck.TableauLiveChecker.addNextState` (both variants): the behavior graph of a formula with a tableau is built the
/// way Java builds it while the states are explored: the states are processed in BFS order; the successors of a state come in the
/// slot order of its `SetOfStates` (`slot`); a node `<s, t>` that is created after `s` was processed is expanded at once by the
/// recursive variant, which adds the self-loops first and then the successors in generation order (`gen`).  The order of the
/// edges of a node decides which counterexample the SCC search finds.
///
/// With SYMMETRY a node stands for all the states of an orbit: the predicates are evaluated on the actual successor state of the edge
/// (`store.edge_vals`), and the recursive variant expands the actual state it was reached with (`gen_fn` generates its successors).
fn build_graph_incr(
    ev: &Ev,
    store: &dyn States,
    slot: &[Vec<u32>],
    gen: &[Vec<u32>],
    gen_fn: Option<GenFn>,
    inits: &[u32],
    oos: &Oos,
    pre: &[Option<Vec<bool>>],
) -> R<Graph> {
    struct B<'a> {
        ev: &'a Ev,
        store: &'a dyn States,
        oos: &'a Oos,
        tb: &'a tlc_core::liveness::tableau::TbGraph,
        gen: &'a [Vec<u32>],
        gen_fn: Option<GenFn<'a>>,
        g: Graph,
        index: HashMap<(u32, usize), u32>,
        rec: Vec<Vec<usize>>,
        done: Vec<bool>,
        texist: HashSet<(u32, u32)>,
        cons: HashMap<(u32, usize), bool>,
        sc: Vec<Option<Vec<bool>>>,
        bits: HashMap<(u32, u32), Vec<bool>>,
        leaf: HashMap<(u32, u32), bool>,
        fresh: u32,
    }
    impl<'a> B<'a> {
        /// does the tableau node `t` accept the state `s` (`vals`: the actual state when it is not the one the node stores)?
        fn consistent(&mut self, s: u32, vals: Option<&[Value]>, t: usize) -> R<bool> {
            match vals {
                Some(v) => self.tb.nodes[t].is_consistent(self.ev, v),
                None => {
                    if let Some(&b) = self.cons.get(&(s, t)) {
                        return Ok(b);
                    }
                    let b = self.tb.nodes[t].is_consistent(self.ev, self.store.vals(s))?;
                    self.cons.insert((s, t), b);
                    Ok(b)
                }
            }
        }
        fn state_checks(&mut self, s: u32) -> R<Vec<bool>> {
            if self.sc[s as usize].is_none() {
                self.sc[s as usize] = Some(self.oos.check_state_res(self.ev, self.store.vals(s))?);
            }
            Ok(self.sc[s as usize].clone().unwrap())
        }
        /// the results of the action predicates on `v0 -> v1`; `mid` identifies the source state for the memo of the state-level leaves
        fn action_bits(&mut self, mid: u32, key: u32, v0: &[Value], v1: &[Value]) -> R<Vec<bool>> {
            if let Some(v) = self.bits.get(&(mid, key)) {
                return Ok(v.clone());
            }
            let mut v = Vec::with_capacity(self.oos.check_action.len());
            for c in self.oos.check_action.iter() {
                v.push(eval_memo(c, self.ev, mid, v0, v1, &mut self.leaf)?);
            }
            self.bits.insert((mid, key), v.clone());
            Ok(v)
        }
        fn create(&mut self, s: u32, t: usize) -> u32 {
            self.g.nodes.push(GNode { state: s, tidx: t as i32, succ: vec![], check_state: vec![], check_action: vec![] });
            let id = self.g.nodes.len() as u32 - 1;
            self.index.insert((s, t), id);
            self.rec[s as usize].push(t);
            id
        }
        fn add(&mut self, from: u32, to: u32, bits: &[bool]) {
            self.texist.insert((from, to));
            let n = &mut self.g.nodes[from as usize];
            n.succ.push(to);
            n.check_action.extend_from_slice(bits);
        }
        /// the recursive `addNextState(tool, s, fp, tnode, oos, dgraph)`: the node `<s, t>` is new and `s` is done; `actual` is the state
        /// the node was reached with when that is not the state the node stores
        fn late(&mut self, s: u32, t: usize, actual: Option<Rc<Vec<Value>>>) -> R<()> {
            let n = self.index[&(s, t)];
            let st: &'a dyn States = self.store;
            let sv: &[Value] = match &actual {
                Some(a) => &a[..],
                None => st.vals(s),
            };
            let cs = match &actual {
                Some(a) => self.oos.check_state_res(self.ev, a)?,
                None => self.state_checks(s)?,
            };
            self.g.nodes[n as usize].check_state = cs;
            // the memo of the state-level leaves is keyed by the source state: an actual state of its own gets an id of its own
            let mid = if actual.is_some() {
                self.fresh += 1;
                self.fresh
            } else {
                s
            };
            let nexts = self.tb.nodes[t].nexts.clone();
            if !nexts.is_empty() {
                let bits = self.action_bits(mid, 0x4000_0000, sv, sv)?;
                for &t1 in &nexts {
                    if self.consistent(s, actual.as_ref().map(|a| &a[..]), t1)? {
                        let exists = self.index.get(&(s, t1)).copied();
                        let missing = match exists {
                            None => true,
                            Some(d) => !self.texist.contains(&(n, d)),
                        };
                        if missing {
                            let d = match exists {
                                Some(d) => d,
                                None => self.create(s, t1),
                            };
                            self.add(n, d, &bits);
                            if exists.is_none() {
                                self.late(s, t1, actual.clone())?;
                            }
                        }
                    }
                }
            }
            // the successors in generation order (those of the actual state when SYMMETRY makes it differ from the stored one)
            let succs: Vec<(u32, Option<Rc<Vec<Value>>>)> = match (&self.gen_fn, &actual) {
                (Some(f), Some(a)) => f(a)?.into_iter().map(|(n, v)| (n, Some(v))).collect(),
                (Some(f), None) => f(sv)?.into_iter().map(|(n, v)| (n, Some(v))).collect(),
                _ => self.gen[s as usize].iter().map(|&n| (n, None)).collect(),
            };
            for (k, (s1, a1)) in succs.iter().enumerate() {
                let s1 = *s1;
                let bits = {
                    let v1: &[Value] = match a1 {
                        Some(v) => &v[..],
                        None => st.vals(s1),
                    };
                    self.action_bits(mid, (k as u32) | 0x8000_0000, sv, v1)?
                };
                let is_done = self.done[s1 as usize];
                for &t1 in &nexts {
                    if self.consistent(s1, a1.as_ref().map(|a| &a[..]), t1)? {
                        let exists = self.index.get(&(s1, t1)).copied();
                        let missing = match exists {
                            None => true,
                            Some(d) => !self.texist.contains(&(n, d)),
                        };
                        if missing {
                            let d = match exists {
                                Some(d) => d,
                                None => self.create(s1, t1),
                            };
                            self.add(n, d, &bits);
                            if exists.is_none() && is_done {
                                self.late(s1, t1, a1.clone())?;
                            }
                        }
                    }
                }
            }
            Ok(())
        }
    }
    let tb = oos.tableau.as_ref().unwrap();
    let n = slot.len();
    let mut b = B {
        ev,
        store,
        oos,
        tb,
        gen,
        gen_fn,
        g: Graph { nodes: vec![], init: vec![], alen: oos.check_action.len() },
        index: HashMap::default(),
        rec: vec![vec![]; n],
        done: vec![false; n],
        texist: HashSet::default(),
        cons: HashMap::default(),
        sc: (0..n).map(|i| pre.get(i).cloned().flatten()).collect(),
        bits: HashMap::default(),
        leaf: HashMap::default(),
        fresh: n as u32,
    };
    // addInitState: (state, tnode) is a root node if tnode is an initial tableau node consistent with the state
    for &s in inits {
        for t in 0..tb.init_cnt {
            if b.consistent(s, None, t)? {
                let id = match b.index.get(&(s, t)).copied() {
                    Some(id) => id,
                    None => b.create(s, t),
                };
                b.g.init.push(id);
            }
        }
    }
    for s0 in 0..n as u32 {
        b.done[s0 as usize] = true;
        let snapshot = b.rec[s0 as usize].clone();
        let succs = slot[s0 as usize].clone();
        let v0: &[Value] = store.vals(s0);
        for &t0 in &snapshot {
            let n0 = b.index[&(s0, t0)];
            let cs = b.state_checks(s0)?;
            b.g.nodes[n0 as usize].check_state = cs;
            let nexts = tb.nodes[t0].nexts.clone();
            for (i, &s1) in succs.iter().enumerate() {
                let actual: Option<&[Value]> = store.edge_vals(s0, i);
                let is_done = b.done[s1 as usize];
                for &t1 in &nexts {
                    if b.consistent(s1, actual, t1)? {
                        let exists = b.index.get(&(s1, t1)).copied();
                        let missing = match exists {
                            None => true,
                            Some(d) => !b.texist.contains(&(n0, d)),
                        };
                        if missing {
                            let v1: &[Value] = match actual {
                                Some(a) => a,
                                None => store.vals(s1),
                            };
                            let bits = b.action_bits(s0, i as u32, v0, v1)?;
                            let d = match exists {
                                Some(d) => d,
                                None => b.create(s1, t1),
                            };
                            b.add(n0, d, &bits);
                            if exists.is_none() && is_done {
                                b.late(s1, t1, actual.map(|a| Rc::new(a.to_vec())))?;
                            }
                        }
                    }
                }
            }
        }
    }
    // a node whose state was never processed keeps the results of its state predicates
    for i in 0..b.g.nodes.len() {
        if b.g.nodes[i].check_state.is_empty() {
            let s = b.g.nodes[i].state;
            let cs = b.state_checks(s)?;
            b.g.nodes[i].check_state = cs;
        }
    }
    Ok(b.g)
}

/// `Ln::eval` on the step `s0 -> s1` of the state `s`, remembering the value of every state predicate per state
fn eval_memo(ln: &tlc_core::liveness::ln::Ln, ev: &Ev, s: u32, s0: &[Value], s1: &[Value], memo: &mut HashMap<(u32, u32), bool>) -> R<bool> {
    use tlc_core::liveness::ln::LnNode;
    match &*ln.0 {
        LnNode::State(l) => {
            let key = (s, l.tag.get());
            if let Some(b) = memo.get(&key) {
                return Ok(*b);
            }
            let b = ln.eval(ev, s0, s1)?;
            memo.insert(key, b);
            Ok(b)
        }
        LnNode::Neg(b) => Ok(!eval_memo(b, ev, s, s0, s1, memo)?),
        LnNode::Conj(v) => {
            for x in v {
                if !eval_memo(x, ev, s, s0, s1, memo)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LnNode::Disj(v) => {
            for x in v {
                if eval_memo(x, ev, s, s0, s1, memo)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => ln.eval(ev, s0, s1),
    }
}

const MAX_PTR: u64 = 1 << 62;
const MAX_LINK: u64 = u64::MAX >> 1;

enum Item {
    Node(u32),
    Low(u64),
    Marker(u32),
}

/// `LiveWorker.checkSccs` for one possible error model: `Some(lasso)` when a counterexample exists
pub fn check_sccs(ev: &Ev, store: &dyn States, g: &Graph, oos: &Oos, pem: &Pem) -> R<Option<Lasso>> {
    let n = g.nodes.len();
    let mut link: Vec<u64> = vec![0; n];
    let mut node_queue: VecDeque<u32> = g.init.iter().copied().collect();
    let mut com_stack: Vec<u32> = vec![];
    let eaaction = &pem.ea_action;
    while let Some(root) = node_queue.pop_front() {
        let mut dfs: Vec<Item> = vec![Item::Node(root), Item::Low(MAX_PTR)];
        let mut new_link = MAX_PTR;
        while dfs.len() >= 2 {
            let low = match dfs.pop() {
                Some(Item::Low(l)) => l,
                _ => unreachable!("dfs stack layout"),
            };
            match dfs.pop().unwrap() {
                Item::Marker(cur) => {
                    if link[cur as usize] == low {
                        if let Some(l) = check_component(ev, store, g, oos, pem, cur, &mut com_stack, &mut link)? {
                            return Ok(Some(l));
                        }
                    }
                    let plow = match dfs.pop() {
                        Some(Item::Low(l)) => l,
                        _ => unreachable!("dfs stack layout"),
                    };
                    dfs.push(Item::Low(plow.min(low)));
                }
                Item::Node(cur) => {
                    let old = link[cur as usize];
                    if old < MAX_PTR {
                        link[cur as usize] = new_link;
                        dfs.push(Item::Low(low));
                        dfs.push(Item::Marker(cur));
                        com_stack.push(cur);
                        let mut next_low = new_link;
                        new_link += 1;
                        let gn = &g.nodes[cur as usize];
                        for i in 0..gn.succ.len() {
                            let next = gn.succ[i];
                            let next_link = link[next as usize];
                            if g.check_action_all(cur, i, eaaction) {
                                if next_link < MAX_PTR {
                                    dfs.push(Item::Node(next));
                                } else {
                                    next_low = next_low.min(next_link);
                                }
                            } else if next_link < MAX_PTR {
                                node_queue.push_back(next);
                            }
                        }
                        dfs.push(Item::Low(next_low));
                    } else {
                        dfs.push(Item::Low(low.min(old)));
                    }
                }
                Item::Low(_) => unreachable!("dfs stack layout"),
            }
        }
    }
    Ok(None)
}

/// a node has a self loop satisfying the EA actions
fn is_stuttering(g: &Graph, n: u32, eaaction: &[usize]) -> bool {
    let nd = &g.nodes[n as usize];
    for i in 0..nd.succ.len() {
        if nd.succ[i] == n {
            return g.check_action_all(n, i, eaaction);
        }
    }
    false
}

/// `LiveWorker.checkComponent`
#[allow(clippy::too_many_arguments)]
fn check_component(
    ev: &Ev,
    store: &dyn States,
    g: &Graph,
    oos: &Oos,
    pem: &Pem,
    node: u32,
    com_stack: &mut Vec<u32>,
    link: &mut [u64],
) -> R<Option<Lasso>> {
    let mut n1 = com_stack.pop().unwrap();
    if n1 == node && !is_stuttering(g, n1, &pem.ea_action) {
        link[node as usize] = MAX_LINK;
        return Ok(None);
    }
    // the component (in the order the nodes are popped)
    let mut com: Vec<u32> = vec![];
    loop {
        com.push(n1);
        link[n1 as usize] = MAX_LINK;
        if n1 == node {
            break;
        }
        n1 = com_stack.pop().unwrap();
    }
    let in_com: HashSet<u32> = com.iter().copied().collect();
    let mut ae_state = vec![false; pem.ae_state.len()];
    let mut ae_action = vec![false; pem.ae_action.len()];
    let mut promise_res = vec![false; oos.promises.len()];
    for &c in &com {
        let nd = &g.nodes[c as usize];
        for (i, &idx) in pem.ae_state.iter().enumerate() {
            if !ae_state[i] {
                ae_state[i] = nd.check_state[idx];
            }
        }
        if !pem.ae_action.is_empty() {
            for (i, &nx) in nd.succ.iter().enumerate() {
                if !in_com.contains(&nx) {
                    continue;
                }
                if !g.check_action_all(c, i, &pem.ea_action) {
                    continue;
                }
                for (j, &idx) in pem.ae_action.iter().enumerate() {
                    if !ae_action[j] {
                        ae_action[j] = g.check_action_one(c, i, idx);
                    }
                }
            }
        }
        if let Some(tb) = &oos.tableau {
            let par = &tb.nodes[nd.tidx as usize].par;
            for (i, p) in oos.promises.iter().enumerate() {
                if par.is_fulfilling(p) {
                    promise_res[i] = true;
                }
            }
        }
    }
    if ae_state.iter().any(|b| !b) || ae_action.iter().any(|b| !b) || promise_res.iter().any(|b| !b) {
        return Ok(None);
    }
    let _ = ev;
    Ok(Some(build_lasso(g, oos, pem, node, &com, store)))
}

/// `AbstractDiskGraph.getPath`: breadth-first search from the initial nodes; the path (init .. target) as nodes
fn get_path(g: &Graph, target: u32) -> Vec<u32> {
    if g.init.contains(&target) {
        return vec![target];
    }
    let mut parent: Vec<u32> = vec![u32::MAX; g.nodes.len()];
    let mut seen = vec![false; g.nodes.len()];
    let mut queue: VecDeque<u32> = VecDeque::new();
    for &i in &g.init {
        if !seen[i as usize] {
            seen[i as usize] = true;
            queue.push_back(i);
        }
    }
    while let Some(cur) = queue.pop_front() {
        for &nx in &g.nodes[cur as usize].succ {
            if nx == cur {
                continue;
            }
            if nx == target {
                let mut path = vec![target, cur];
                let mut c = cur;
                while parent[c as usize] != u32::MAX {
                    c = parent[c as usize];
                    path.push(c);
                }
                path.reverse();
                return path;
            }
            if !seen[nx as usize] {
                seen[nx as usize] = true;
                parent[nx as usize] = cur;
                queue.push_back(nx);
            }
        }
    }
    vec![target]
}

/// `LiveWorker.printTrace` without the printing: the states of the lasso
fn build_lasso(g: &Graph, oos: &Oos, pem: &Pem, root: u32, com: &[u32], _store: &dyn States) -> Lasso {
    // prefix: the shortest path from an initial node to the root (consecutive equal states are merged)
    let path = get_path(g, root);
    let mut states: Vec<u32> = vec![];
    for n in &path {
        let s = g.nodes[*n as usize].state;
        if states.last() != Some(&s) {
            states.push(s);
        }
    }
    let cycle_pos = states.len() - 1;
    let cycle_state = states[cycle_pos];
    // component members per state (in the order of insertion into the component table)
    let mut state_order: Vec<u32> = vec![];
    let mut by_state: HashMap<u32, Vec<u32>> = HashMap::default();
    for &c in com {
        let s = g.nodes[c as usize].state;
        by_state.entry(s).or_insert_with(|| {
            state_order.push(s);
            vec![]
        });
        by_state.get_mut(&s).unwrap().push(c);
    }
    let in_com: HashSet<u32> = com.iter().copied().collect();
    let eaaction = &pem.ea_action;
    // ---- dfsPostFix
    let mut cycle_stack: Vec<u32> = vec![];
    let mut seen: HashSet<u32> = HashSet::default();
    let mut ae_state_res = vec![false; pem.ae_state.len()];
    let mut ae_action_res = vec![false; pem.ae_action.len()];
    let mut promise_res = vec![false; oos.promises.len()];
    let mut cnt = ae_state_res.len() + ae_action_res.len() + promise_res.len();
    seen.insert(root);
    let mut cur = root;
    while cnt > 0 {
        let cnt0 = cnt;
        'next: loop {
            let nd = &g.nodes[cur as usize];
            for (i, &idx) in pem.ae_state.iter().enumerate() {
                if !ae_state_res[i] && nd.check_state[idx] {
                    ae_state_res[i] = true;
                    cnt -= 1;
                }
            }
            if let Some(tb) = &oos.tableau {
                let par = &tb.nodes[nd.tidx as usize].par;
                for (i, p) in oos.promises.iter().enumerate() {
                    if !promise_res[i] && par.is_fulfilling(p) {
                        promise_res[i] = true;
                        cnt -= 1;
                    }
                }
            }
            if cnt == 0 {
                break;
            }
            let mut next1: Option<u32> = None;
            let mut next2: Option<u32> = None;
            let mut has_unvisited = false;
            let cnt1 = cnt;
            for (i, &nx) in nd.succ.iter().enumerate() {
                if in_com.contains(&nx) {
                    if !g.check_action_all(cur, i, eaaction) {
                        continue;
                    }
                    next1 = Some(nx);
                    for (j, &idx) in pem.ae_action.iter().enumerate() {
                        if !ae_action_res[j] && g.check_action_one(cur, i, idx) {
                            ae_action_res[j] = true;
                            cnt -= 1;
                        }
                    }
                }
                if cnt < cnt1 {
                    cycle_stack.push(cur);
                    cur = nx;
                    seen.clear();
                    break 'next;
                }
                if in_com.contains(&nx) && !seen.contains(&nx) {
                    has_unvisited = true;
                    next2 = Some(nx);
                }
            }
            if cnt < cnt0 {
                if let Some(n1) = next1 {
                    cycle_stack.push(cur);
                    cur = n1;
                    seen.clear();
                    break;
                }
            }
            // continue with an unvisited successor, backtracking when there is none
            while !has_unvisited {
                let c = match cycle_stack.pop() {
                    Some(c) => c,
                    None => {
                        // cannot happen for a strongly connected component
                        has_unvisited = true;
                        next2 = Some(cur);
                        break;
                    }
                };
                cur = c;
                for &nx in &g.nodes[c as usize].succ {
                    if in_com.contains(&nx) && !seen.contains(&nx) {
                        has_unvisited = true;
                        next2 = Some(nx);
                        break;
                    }
                }
            }
            cycle_stack.push(cur);
            cur = next2.unwrap();
            seen.insert(cur);
        }
    }
    let end_node = cur;
    // ---- bfsPostFix (over the states of the component)
    let mut postfix: Vec<u32> = vec![]; // states
    let start_state = g.nodes[end_node as usize].state;
    if end_node != root {
        let mut seen_states: HashSet<u32> = HashSet::default();
        let mut queue: VecDeque<(u32, usize)> = VecDeque::new();
        let mut parent_of: HashMap<u32, usize> = HashMap::default(); // state -> index of its parent in `visit`
        let mut visit: Vec<u32> = vec![];
        let mut cur_state = start_state;
        let mut ploc: usize = usize::MAX;
        seen_states.insert(cur_state);
        'done: loop {
            let my = visit.len();
            visit.push(cur_state);
            let members = by_state.get(&cur_state).cloned().unwrap_or_default();
            for &m in &members {
                let nd = &g.nodes[m as usize];
                for (j, &nx) in nd.succ.iter().enumerate() {
                    if nx == m {
                        continue;
                    }
                    if !g.check_action_all(m, j, eaaction) {
                        continue;
                    }
                    if nx == root {
                        // reconstruct: cur_state back to the start state of the search
                        let mut cs = cur_state;
                        let mut pl = ploc;
                        while cs != start_state {
                            postfix.push(cs);
                            cs = visit[pl];
                            pl = *parent_of.get(&cs).unwrap_or(&usize::MAX);
                        }
                        postfix.push(start_state);
                        break 'done;
                    }
                    let ns = g.nodes[nx as usize].state;
                    if by_state.contains_key(&ns) && !seen_states.contains(&ns) {
                        seen_states.insert(ns);
                        queue.push_back((ns, my));
                    }
                }
            }
            if let Some(&p) = (ploc != usize::MAX).then_some(&ploc) {
                parent_of.insert(cur_state, p);
            }
            match queue.pop_front() {
                Some((s, pl)) => {
                    cur_state = s;
                    ploc = pl;
                }
                None => break,
            }
        }
    }
    while let Some(n) = cycle_stack.pop() {
        let s = g.nodes[n as usize].state;
        if postfix.last() != Some(&s) {
            postfix.push(s);
        }
    }
    // pack(): merge consecutive duplicates; removeLastIf(cycle state)
    let mut packed: Vec<u32> = vec![];
    for s in postfix {
        if packed.last() != Some(&s) {
            packed.push(s);
        }
    }
    if packed.last() == Some(&cycle_state) {
        packed.pop();
    }
    for s in packed.iter().rev() {
        states.push(*s);
    }
    let last = *states.last().unwrap();
    Lasso { states, cycle_pos, stuttering: last == cycle_state }
}

/// the behavior graphs of all orders of solution (Java: the `LiveChecker`s after the state space has been explored)
#[allow(clippy::too_many_arguments)]
pub fn build_all(ev: &Ev, store: &dyn States, succ: &[Vec<u32>], gen: Option<&[Vec<u32>]>, gen_fn: Option<GenFn>, inits: &[u32], oss: &[Oos], pre: &[Vec<Option<Vec<bool>>>]) -> R<Vec<Graph>> {
    oss.iter().enumerate().map(|(i, oos)| build_graph(ev, store, succ, gen, gen_fn, inits, oos, pre.get(i).map_or(&[][..], |v| &v[..]))).collect()
}

/// `LiveWorker.call` over all orders of solution: the first counterexample found
pub fn find_counterexample(ev: &Ev, store: &dyn States, graphs: &[Graph], oss: &[Oos]) -> R<Option<(usize, Lasso)>> {
    for (i, (oos, g)) in oss.iter().zip(graphs.iter()).enumerate() {
        for pem in &oos.pems {
            if let Some(l) = check_sccs(ev, store, g, oos, pem)? {
                return Ok(Some((i, l)));
            }
        }
    }
    Ok(None)
}

/// Where Java's incremental liveness checking reports a counterexample of a safety-like property (`LiveCheck`,
/// `addNextState` with `oos.hasEmptyPEM()`): the processed BFS state and the finite behavior to the node.
pub struct Shortcut {
    /// index (in processing order) of the state whose successors were being added
    pub k: usize,
    /// the states of the behavior from an initial state to the violating state
    pub states: Vec<u32>,
}

/// Port of `LiveCheck.TableauLiveChecker.addInitState` / `addNextState` (and the recursive `addNextState` for states that
/// are done already): the behavior graph is built incrementally in BFS order; when a node `<s, t>` whose tableau successor
/// `t1` is accepting and consistent with `s` is created, the finite path to it is a counterexample (no cycle needed).
pub fn safety_shortcut(ev: &Ev, store: &dyn States, succ: &[Vec<u32>], gen: Option<&[Vec<u32>]>, inits: &[u32], oos: &Oos) -> R<Option<Shortcut>> {
    let tb = match &oos.tableau {
        Some(t) if oos.has_empty_pem() => t,
        _ => return Ok(None),
    };
    struct Ctx<'a> {
        ev: &'a Ev,
        store: &'a dyn States,
        succ: &'a [Vec<u32>],
        gen: Option<&'a [Vec<u32>]>,
        tb: &'a tlc_core::liveness::tableau::TbGraph,
        recorded: HashSet<(u32, usize)>,
        nodes_of: HashMap<u32, Vec<usize>>,
        done: Vec<bool>,
        edges: HashMap<(u32, usize), Vec<(u32, usize)>>,
        edge_set: HashSet<((u32, usize), (u32, usize))>,
        cons: HashMap<(u32, usize), bool>,
        err: Option<(u32, usize)>,
    }
    impl<'a> Ctx<'a> {
        fn consistent(&mut self, s: u32, t: usize) -> R<bool> {
            if let Some(&b) = self.cons.get(&(s, t)) {
                return Ok(b);
            }
            let b = self.tb.nodes[t].is_consistent(self.ev, self.store.vals(s))?;
            self.cons.insert((s, t), b);
            Ok(b)
        }
        fn record(&mut self, s: u32, t: usize) {
            if self.recorded.insert((s, t)) {
                self.nodes_of.entry(s).or_default().push(t);
            }
        }
        fn add_edge(&mut self, from: (u32, usize), to: (u32, usize)) {
            if self.edge_set.insert((from, to)) {
                self.edges.entry(from).or_default().push(to);
            }
        }
        /// the private `addNextState(tool, s, fp, tnode, oos, dgraph)`: the node `<s, t>` is new and `s` is done
        fn rec(&mut self, s: u32, t: usize) -> R<()> {
            let nexts = self.tb.nodes[t].nexts.clone();
            // edges induced by s -> s (self-loop) coming from the tableau graph
            for &t1 in &nexts {
                if self.consistent(s, t1)? {
                    if self.tb.nodes[t1].is_accepting(t1) && self.err.is_none() {
                        self.err = Some((s, t));
                        return Ok(());
                    }
                    let rec1 = self.recorded.contains(&(s, t1));
                    if !rec1 || !self.edge_set.contains(&((s, t), (s, t1))) {
                        self.add_edge((s, t), (s, t1));
                        if !rec1 {
                            self.record(s, t1);
                            self.rec(s, t1)?;
                        }
                    }
                }
            }
            // edges induced by s -> s1 (s1 a successor of s in the state graph)
            let succs = match self.gen {
                Some(g) => g[s as usize].clone(),
                None => self.succ[s as usize].clone(),
            };
            for &s1 in &succs {
                let is_done = self.done[s1 as usize];
                for &t1 in &nexts {
                    if self.consistent(s1, t1)? {
                        let rec1 = self.recorded.contains(&(s1, t1));
                        if !rec1 || !self.edge_set.contains(&((s, t), (s1, t1))) {
                            self.add_edge((s, t), (s1, t1));
                            if !rec1 {
                                self.record(s1, t1);
                                if is_done {
                                    self.rec(s1, t1)?;
                                }
                            }
                        }
                    }
                }
            }
            Ok(())
        }
    }
    let n = succ.len();
    let mut cx = Ctx {
        ev,
        store,
        succ,
        gen,
        tb,
        recorded: Default::default(),
        nodes_of: HashMap::default(),
        done: vec![false; n],
        edges: HashMap::default(),
        edge_set: Default::default(),
        cons: HashMap::default(),
        err: None,
    };
    // addInitState: (state, tnode) is a root node if tnode is an initial tableau node consistent with the state
    let mut roots: Vec<(u32, usize)> = vec![];
    for &s in inits {
        for t in 0..tb.init_cnt {
            if cx.consistent(s, t)? {
                roots.push((s, t));
                cx.record(s, t);
            }
        }
    }
    for k in 0..n as u32 {
        cx.done[k as usize] = true;
        let snapshot = cx.nodes_of.get(&k).cloned().unwrap_or_default();
        let succs = succ[k as usize].clone();
        for &t0 in &snapshot {
            let nexts = tb.nodes[t0].nexts.clone();
            for &s1 in &succs {
                let is_done = cx.done[s1 as usize];
                for &t1 in &nexts {
                    if cx.consistent(s1, t1)? {
                        let rec1 = cx.recorded.contains(&(s1, t1));
                        if !rec1 || !cx.edge_set.contains(&((k, t0), (s1, t1))) {
                            cx.add_edge((k, t0), (s1, t1));
                            if !rec1 {
                                cx.record(s1, t1);
                                if is_done {
                                    cx.rec(s1, t1)?;
                                }
                            }
                        }
                    }
                }
            }
        }
        if let Some(target) = cx.err {
            // the path (breadth-first over the behavior graph built so far) from a root node to the violating node
            let mut parent: HashMap<(u32, usize), (u32, usize)> = HashMap::default();
            let mut seen: HashSet<(u32, usize)> = roots.iter().copied().collect();
            let mut q: VecDeque<(u32, usize)> = roots.iter().copied().collect();
            while let Some(cur) = q.pop_front() {
                if cur == target {
                    break;
                }
                if let Some(ns) = cx.edges.get(&cur) {
                    for &nx in ns {
                        if seen.insert(nx) {
                            parent.insert(nx, cur);
                            q.push_back(nx);
                        }
                    }
                }
            }
            let mut path = vec![target];
            let mut cur = target;
            while let Some(&p) = parent.get(&cur) {
                path.push(p);
                cur = p;
            }
            path.reverse();
            // finite stuttering is dropped
            let mut states: Vec<u32> = vec![];
            for (s, _) in path {
                if states.last() != Some(&s) {
                    states.push(s);
                }
            }
            return Ok(Some(Shortcut { k: k as usize, states }));
        }
    }
    Ok(None)
}
