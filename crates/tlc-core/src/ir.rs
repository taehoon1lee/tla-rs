//! Compiled expression tree evaluated by `eval.rs` (the role of `OpApplNode` trees + `Tool.eval` in Java).
//!
//! Slots: every definition body (and every top-level expression) owns a frame of `nslots` slots; binders assign
//! their slot (no push/pop), so continuations of the action enumerator can run inside a binder's extent.

use crate::value::*;
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use tla_sany::ast::Loc;
use tla_sany::sem::{self, B};

pub type Ex = Rc<Node>;

/// a value held in a frame slot
#[derive(Clone)]
pub enum Slot {
    Unset,
    V(Value),
    /// operator passed as an argument
    Op(Rc<OpClosure>),
    /// evaluation of an argument failed; fails when (and only when) the argument is used (lazy semantics)
    Poison(Box<TlcErr>),
    /// call-by-name argument (action-level expressions)
    Lazy(Rc<LazyArg>),
    /// memoized value of a nullary LET definition: (value, address and length of the current state, evaluation epoch);
    /// valid while the same state is evaluated and nothing was assigned (Java: `LazyValue`)
    Memo(Rc<MemoVal>),
}

/// the payload of `Slot::Memo` (boxed to keep `Slot` small)
pub struct MemoVal {
    pub v: Value,
    pub ptr: usize,
    pub len: usize,
    pub epoch: u64,
}

pub struct LazyArg {
    pub code: Ex,
    pub frame: Rc<Vec<Slot>>,
    pub substs: Substs,
    /// a state-level expression (no primes): its value can be cached per (state, evaluation epoch)
    pub cacheable: bool,
    pub cache: RefCell<Vec<LazyCache>>,
}

/// Java: `LazyValue.Cache`: the value computed for one state and evaluation
pub struct LazyCache {
    pub s0_ptr: usize,
    pub s0_len: usize,
    pub epoch: u64,
    pub val: Value,
    /// INSTANCE substitutions in scope when the value was computed (kept alive so that identity comparison is sound)
    pub substs: Substs,
}

#[derive(Clone)]
pub struct SubstEntry {
    pub decl: usize,
    pub slot: Slot,
}

/// INSTANCE substitutions in scope: a persistent list (newest first) so that capturing / restoring is O(1)
/// (closures, call-by-name arguments and function constructors capture the substitutions of their creation).
pub struct SubstNode {
    pub entry: SubstEntry,
    pub parent: Substs,
    pub len: usize,
}

#[derive(Clone, Default)]
pub struct Substs(Option<Rc<SubstNode>>);

impl Substs {
    /// same list object (or both empty)
    #[inline]
    pub fn same(&self, o: &Substs) -> bool {
        match (&self.0, &o.0) {
            (None, None) => true,
            (Some(a), Some(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |n| n.len)
    }
    /// a new list with `entry` as its newest element
    pub fn push(&self, entry: SubstEntry) -> Substs {
        Substs(Some(Rc::new(SubstNode { len: self.len() + 1, entry, parent: self.clone() })))
    }
    /// newest first
    #[inline]
    pub fn iter(&self) -> SubstIter<'_> {
        SubstIter(self.0.as_deref())
    }
    /// the newest entry substituting declaration `decl`
    #[inline]
    pub fn find(&self, decl: usize) -> Option<&SubstEntry> {
        self.iter().find(|e| e.decl == decl)
    }
}

pub struct SubstIter<'a>(Option<&'a SubstNode>);

impl<'a> Iterator for SubstIter<'a> {
    type Item = &'a SubstEntry;
    #[inline]
    fn next(&mut self) -> Option<&'a SubstEntry> {
        let n = self.0?;
        self.0 = n.parent.0.as_deref();
        Some(&n.entry)
    }
}

pub struct LambdaDef {
    pub nparams: usize,
    pub nslots: usize,
    pub body: Ex,
}

pub enum OpClosure {
    Def(Rc<CompiledDef>),
    Builtin(B),
    /// `self_slot`: slot (in the captured frame layout) that holds the closure itself (recursive LET operators)
    Lambda { def: Rc<LambdaDef>, frame: Rc<Vec<Slot>>, self_slot: Option<u32> },
    /// a constant operator parameter (`CONSTANT F(_)`) assigned by the configuration
    Decl(usize),
}

pub type NativeFn = fn(&crate::eval::Ev, &mut Vec<Slot>, &[Value], &[Value]) -> R<Value>;

pub struct CompiledDef {
    pub id: usize,
    pub name: sem::Name,
    pub module: sem::Name,
    pub nparams: usize,
    /// which parameters are operators (arity > 0)
    pub op_params: Vec<bool>,
    pub nslots: Cell<usize>,
    pub body: RefCell<Option<Ex>>,
    pub native: Cell<Option<NativeFn>>,
    pub level: sem::Level,
    pub loc: Loc,
    /// cached value of a constant-level definition without parameters
    pub cache: RefCell<Option<Value>>,
    /// for `f[x \in S] == ...`: a recursive function definition
    pub is_fcn: bool,
    pub src: Rc<sem::OpDef>,
    /// `<Name line .., col .. to line .., col .. of module M>` (computed on first use)
    /// value of a state-level definition without parameters for one state (Java: the LazyValue of an operator definition)
    pub state_cache: RefCell<Option<LazyCache>>,
    pub label_cache: std::cell::OnceCell<Option<Rc<str>>>,
    /// label base (name without parameters) shared by every call of this definition without arguments
    pub label_base: std::cell::OnceCell<Rc<crate::eval::LabelBase>>,
    /// calls remembered by argument values (see `memo`): 0 = not analysed yet, 1 = remember, 2 = never
    pub memo_kind: Cell<u8>,
    pub memo: RefCell<std::collections::HashMap<u64, Vec<(Vec<Value>, Value)>>>,
    pub memo_n: Cell<usize>,
    /// calls looked up / found in `memo`: remembering stops when fewer than half of the calls are found
    pub memo_calls: Cell<u32>,
    pub memo_hits: Cell<u32>,
}

pub enum OpRef {
    Def(Rc<CompiledDef>),
    Builtin(B),
    Local(u32),
    Decl(usize),
    Lambda(Rc<LambdaDef>),
}

pub enum Arg {
    /// expression argument; `true` = evaluated by name when used (action-level expressions)
    Val(Ex, bool),
    /// call-by-name, state-level (INSTANCE substitutions): evaluated lazily and cached like Java's LazyValue;
    /// the flag says that the expression reads no frame slot (no frame copy needed)
    State(Ex, bool),
    /// call-by-name expression argument that reads no frame slot
    ValClosed(Ex),
    Op(OpRef),
}

pub struct BoundIr {
    /// first slot of the group
    pub slot: u32,
    pub nvars: u32,
    pub tuple: bool,
    pub set: Ex,
}

pub struct ExceptIr {
    pub path: Vec<PathIr>,
    /// slot holding `@` while evaluating `val`
    pub at_slot: u32,
    pub val: Ex,
}

pub enum PathIr {
    Field(u32),
    Index(Ex),
}

pub struct DeclRef {
    pub id: usize,
    pub name: sem::Name,
    pub is_var: bool,
    pub var_index: u32,
    pub arity: usize,
}

/// source information about a compiled node, used to name actions (`<Name(args) line .. of module M>`)
#[derive(Clone)]
pub struct NodeInfo {
    pub loc: Loc,
    pub module: sem::Name,
    /// `\E` with constant domains / operator application with constant arguments: Java splits actions there
    pub const_sub: bool,
}

/// binary operators of Naturals/Integers with an inlined fast path for `Int` operands
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArithOp {
    Plus,
    Minus,
    Times,
    Lt,
    Gt,
    Le,
    Ge,
    DotDot,
}

pub enum Node {
    /// LET with recursive operator definitions: bind each closure to its slot, then evaluate the body
    LetRec(Vec<(u32, Rc<LambdaDef>)>, Ex),
    /// a closed constant expression: evaluated once, on first use
    Fold(Ex, RefCell<Option<Value>>),
    /// fast path of a native binary operator; the native function handles every other case (errors included)
    Arith(ArithOp, Ex, Ex, NativeFn),
    Const(Value),
    Local(u32),
    /// state variable (not substitutable)
    Var(u32),
    PrimedVar(u32),
    /// constant / variable declaration that an enclosing INSTANCE may substitute
    Decl(Rc<DeclRef>),
    /// declared constant operator applied to arguments
    CallDecl(Rc<DeclRef>, Vec<Arg>),
    Prime(Ex),
    Unchanged(Ex),
    Call(Rc<CompiledDef>, Vec<Arg>, Loc),
    CallLocal(u32, Vec<Arg>),
    /// built-in operator
    Bi(B, Vec<Ex>),
    And(Vec<Ex>),
    Or(Vec<Ex>),
    Not(Ex),
    Implies(Ex, Ex),
    Equiv(Ex, Ex),
    Eq(Ex, Ex),
    Neq(Ex, Ex),
    In(Ex, Ex),
    NotIn(Ex, Ex),
    Tuple(Vec<Ex>),
    SetEnum(Vec<Ex>),
    Times(Vec<Ex>),
    FcnApply(Ex, Ex),
    Record(Ex, u32),
    SubsetOf { bound: BoundIr, pred: Ex, filter_slots: Rc<Vec<u32>> },
    SetOfAll(Ex, Vec<BoundIr>),
    /// `[x \in S |-> e]`; `self_slot`: slot holding the function itself (recursive definitions)
    FcnCons(Vec<BoundIr>, Ex, Option<u32>),
    SetOfFcns(Ex, Ex),
    RcdCons(Vec<(u32, Ex)>),
    SetOfRcds(Vec<(u32, Ex)>),
    Except(Ex, Vec<ExceptIr>),
    ActionSub { boxed: bool, act: Ex, sub: Ex },
    If(Ex, Ex, Ex),
    Case(Vec<(Ex, Ex)>, Option<Ex>),
    Exists(Vec<BoundIr>, Ex),
    Forall(Vec<BoundIr>, Ex),
    Choose(BoundIr, Ex),
    /// INSTANCE substitution: (declaration id, argument)
    /// the cache: (substitutions in scope on entry, substitutions after this node's) -- valid when every argument is a
    /// call-by-name expression that reads no frame slot, so that the same lazy arguments can serve every evaluation
    SubstIn(Vec<(usize, Arg)>, Ex, bool, RefCell<Option<(Substs, Substs)>>),
    /// `[]`, `<>`, `WF`, `SF`, `~>`, `\EE` ... temporal operators (not evaluated by `eval`)
    Temporal(sem::Level),
    Unsupported(String),
    /// an evaluation error TLC raises at run time (e.g. unbounded CHOOSE)
    Fail(String),
    /// the argument of an inlined call: assign then evaluate (LET operator with parameters)
    InlineCall { assigns: Vec<(u32, Arg)>, body: Ex },
    /// scope of LET definitions that are evaluated at most once: their memo slots are cleared on entry
    LetScope(Vec<u32>, Ex),
    /// use of a memoized nullary LET definition: (memo slot, body of the definition)
    LetUse(u32, Ex),
}
