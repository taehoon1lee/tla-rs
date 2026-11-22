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
}

pub struct LazyArg {
    pub code: Ex,
    pub frame: Rc<Vec<Slot>>,
    pub substs: Rc<Vec<SubstEntry>>,
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
}

#[derive(Clone)]
pub struct SubstEntry {
    pub decl: usize,
    pub slot: Slot,
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
    /// call-by-name, state-level (INSTANCE substitutions): evaluated lazily and cached like Java's LazyValue
    State(Ex),
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
    SubstIn(Vec<(usize, Arg)>, Ex),
    /// `[]`, `<>`, `WF`, `SF`, `~>`, `\EE` ... temporal operators (not evaluated by `eval`)
    Temporal(sem::Level),
    Unsupported(String),
    /// an evaluation error TLC raises at run time (e.g. unbounded CHOOSE)
    Fail(String),
    /// the argument of an inlined call: assign then evaluate (LET operator with parameters)
    InlineCall { assigns: Vec<(u32, Arg)>, body: Ex },
}
