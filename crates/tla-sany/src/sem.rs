//! Semantic graph produced by `analyze.rs` (Java: `tla2sany.semantic.*` — ModuleNode, OpDefNode, OpDeclNode,
//! FormalParamNode, OpApplNode, SubstInNode, LetInNode ...). Identity of nodes matters (TLC keys contexts by
//! node identity), so definitions/declarations/params are `Rc`s with a unique `id`.

use crate::ast::Loc;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

pub type Name = Arc<str>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Level {
    Const = 0,
    State = 1,
    Action = 2,
    Temporal = 3,
}

impl Level {
    pub fn max(a: Level, b: Level) -> Level {
        if a >= b {
            a
        } else {
            b
        }
    }
    pub fn from_i32(i: i32) -> Level {
        match i {
            0 => Level::Const,
            1 => Level::State,
            2 => Level::Action,
            _ => Level::Temporal,
        }
    }
}

/// Java `FormalParamNode`: formal parameter of an operator definition, or a bound identifier.
#[derive(Debug)]
pub struct Param {
    pub id: usize,
    pub name: Name,
    pub arity: usize,
    pub loc: Loc,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeclKind {
    Constant,
    Variable,
}

/// Java `OpDeclNode`: CONSTANT / VARIABLE declaration
#[derive(Debug)]
pub struct OpDecl {
    pub id: usize,
    pub name: Name,
    pub kind: DeclKind,
    pub arity: usize,
    /// module in which it is declared
    pub module: Name,
    pub loc: Loc,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefKind {
    User,
    /// `M == INSTANCE ...`: only reserves the name
    ModuleInstance,
    /// THEOREM / ASSUME with a name
    Theorem,
}

/// Java `OpDefNode`
pub struct OpDef {
    pub id: usize,
    pub name: Name,
    pub params: RefCell<Vec<Rc<Param>>>,
    pub body: RefCell<Option<Expr>>,
    pub local: Cell<bool>,
    pub kind: DefKind,
    /// module in which the definition originally occurs
    pub module: Name,
    /// `getSource()`: the definition this one was copied from by INSTANCE (or itself)
    pub source: RefCell<Option<Rc<OpDef>>>,
    pub loc: Loc,
    pub level: Cell<Level>,
    /// weights[i]: does the level of argument i contribute to the level of an application?
    pub weights: RefCell<Vec<bool>>,
    /// declared in a RECURSIVE statement
    pub in_recursive: Cell<bool>,
    pub is_defined: Cell<bool>,
    pub let_level: Cell<i32>,
    /// `f[x \in S] == ...`
    pub is_fcn_def: Cell<bool>,
    pub is_recursive_fcn: Cell<bool>,
    /// for `f[x \in S] == ...`: the parameter standing for `f` inside the body (recursive references)
    pub fcn_param: RefCell<Option<Rc<Param>>>,
    /// defined inside a LET
    pub in_let: Cell<bool>,
    /// compound id segments for `A!B!C`
    pub compound: RefCell<Vec<Name>>,
}

impl std::fmt::Debug for OpDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "OpDef({}#{})", self.name, self.id)
    }
}

impl OpDef {
    pub fn arity(&self) -> usize {
        self.params.borrow().len()
    }
    pub fn body(&self) -> Option<Expr> {
        self.body.borrow().clone()
    }
    /// the definition this one derives from (itself if it is not an instance copy)
    pub fn original(self: &Rc<OpDef>) -> Rc<OpDef> {
        match &*self.source.borrow() {
            Some(s) => s.clone(),
            None => self.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Callee {
    Def(Rc<OpDef>),
    Decl(Rc<OpDecl>),
    Param(Rc<Param>),
}

impl Callee {
    pub fn name(&self) -> &Name {
        match self {
            Callee::Def(d) => &d.name,
            Callee::Decl(d) => &d.name,
            Callee::Param(p) => &p.name,
        }
    }
    pub fn arity(&self) -> usize {
        match self {
            Callee::Def(d) => d.arity(),
            Callee::Decl(d) => d.arity,
            Callee::Param(p) => p.arity,
        }
    }
    pub fn same(&self, other: &Callee) -> bool {
        match (self, other) {
            (Callee::Def(a), Callee::Def(b)) => Rc::ptr_eq(a, b),
            (Callee::Decl(a), Callee::Decl(b)) => Rc::ptr_eq(a, b),
            (Callee::Param(a), Callee::Param(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// argument of an operator application: an expression or an operator (Java `OpArgNode`)
#[derive(Clone, Debug)]
pub enum Arg {
    Expr(Expr),
    Op(OpArg),
}

#[derive(Clone, Debug)]
pub enum OpArg {
    Callee(Callee, Loc),
    Builtin(B, Loc),
    Lambda(Rc<OpDef>),
}

#[derive(Clone, Debug)]
pub struct Expr(pub Rc<ExprNode>);

#[derive(Debug)]
pub struct ExprNode {
    pub kind: EKind,
    pub loc: Loc,
    pub level: Level,
}

impl std::ops::Deref for Expr {
    type Target = ExprNode;
    fn deref(&self) -> &ExprNode {
        &self.0
    }
}

impl Expr {
    pub fn new(kind: EKind, loc: Loc, level: Level) -> Expr {
        Expr(Rc::new(ExprNode { kind, loc, level }))
    }
}

/// Built-in operators with plain expression arguments (Java `OpApplNode` with a `BuiltInKind` operator)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum B {
    True,
    False,
    Boolean,
    String_,
    Eq,
    Neq,
    Prime,
    Not,
    And,
    Or,
    Equiv,
    Implies,
    Subset,
    UnionAll,
    Domain,
    Subseteq,
    In,
    NotIn,
    SetMinus,
    Intersect,
    Union,
    Times,
    LeadsTo,
    Always,
    Eventually,
    Enabled,
    Unchanged,
    Cdot,
    TemporalImplies,
}

impl B {
    pub fn from_name(n: &str) -> Option<B> {
        Some(match n {
            "TRUE" => B::True,
            "FALSE" => B::False,
            "BOOLEAN" => B::Boolean,
            "STRING" => B::String_,
            "=" => B::Eq,
            "/=" => B::Neq,
            "'" => B::Prime,
            "\\lnot" | "\\neg" => B::Not,
            "\\land" => B::And,
            "\\lor" => B::Or,
            "\\equiv" => B::Equiv,
            "=>" => B::Implies,
            "SUBSET" => B::Subset,
            "UNION" => B::UnionAll,
            "DOMAIN" => B::Domain,
            "\\subseteq" => B::Subseteq,
            "\\in" => B::In,
            "\\notin" => B::NotIn,
            "\\" => B::SetMinus,
            "\\intersect" => B::Intersect,
            "\\union" => B::Union,
            "\\times" => B::Times,
            "~>" => B::LeadsTo,
            "[]" => B::Always,
            "<>" => B::Eventually,
            "ENABLED" => B::Enabled,
            "UNCHANGED" => B::Unchanged,
            "\\cdot" => B::Cdot,
            "-+->" => B::TemporalImplies,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            B::True => "TRUE",
            B::False => "FALSE",
            B::Boolean => "BOOLEAN",
            B::String_ => "STRING",
            B::Eq => "=",
            B::Neq => "/=",
            B::Prime => "'",
            B::Not => "\\lnot",
            B::And => "\\land",
            B::Or => "\\lor",
            B::Equiv => "\\equiv",
            B::Implies => "=>",
            B::Subset => "SUBSET",
            B::UnionAll => "UNION",
            B::Domain => "DOMAIN",
            B::Subseteq => "\\subseteq",
            B::In => "\\in",
            B::NotIn => "\\notin",
            B::SetMinus => "\\",
            B::Intersect => "\\intersect",
            B::Union => "\\union",
            B::Times => "\\times",
            B::LeadsTo => "~>",
            B::Always => "[]",
            B::Eventually => "<>",
            B::Enabled => "ENABLED",
            B::Unchanged => "UNCHANGED",
            B::Cdot => "\\cdot",
            B::TemporalImplies => "-+->",
        }
    }

    pub fn arity(self) -> usize {
        match self {
            B::True | B::False | B::Boolean | B::String_ => 0,
            B::Prime | B::Not | B::Subset | B::UnionAll | B::Domain | B::Always | B::Eventually | B::Enabled | B::Unchanged => 1,
            _ => 2,
        }
    }

    /// (operator level, per-argument max level, per-argument weight)  — `BuiltInOperators.Properties`
    pub fn props(self) -> (Level, [i32; 2], [bool; 2]) {
        use Level::*;
        match self {
            B::True | B::False | B::Boolean | B::String_ => (Const, [0, 0], [false, false]),
            B::Eq | B::Neq => (Const, [2, 2], [true, true]),
            B::Prime => (Action, [1, 0], [false, false]),
            B::Not => (Const, [3, 0], [true, false]),
            B::And | B::Or | B::Equiv | B::Implies => (Const, [3, 3], [true, true]),
            B::Subset | B::UnionAll | B::Domain => (Const, [2, 0], [true, false]),
            B::Subseteq | B::In | B::NotIn | B::SetMinus | B::Intersect | B::Union | B::Times => (Const, [2, 2], [true, true]),
            B::LeadsTo => (Temporal, [3, 3], [false, false]),
            B::Always | B::Eventually => (Temporal, [3, 0], [false, false]),
            B::Enabled => (State, [2, 0], [false, false]),
            B::Unchanged => (Action, [1, 0], [false, false]),
            B::Cdot => (Action, [2, 2], [false, false]),
            B::TemporalImplies => (Temporal, [3, 3], [false, false]),
        }
    }
}

/// bound identifiers of one quantifier/set/function bound: `x, y \in S` or `<<x, y>> \in S`
#[derive(Clone, Debug)]
pub struct BoundGroup {
    pub params: Vec<Rc<Param>>,
    pub tuple: bool,
    pub set: Expr,
}

/// the variable(s) of an unbounded/bounded CHOOSE, SubsetOf
#[derive(Clone, Debug)]
pub struct BoundVars {
    pub params: Vec<Rc<Param>>,
    pub tuple: bool,
}

#[derive(Clone, Debug)]
pub enum ExceptComp {
    Field(Name),
    /// argument expressions (a single expression, or several = a tuple index)
    Index(Vec<Expr>),
}

#[derive(Clone, Debug)]
pub struct ExceptSpec {
    pub path: Vec<ExceptComp>,
    pub val: Expr,
}

#[derive(Debug, Clone)]
pub struct Subst {
    pub target: Rc<OpDecl>,
    pub value: Arg,
    /// the module that holds the `INSTANCE` statement (the module the value expression was written in)
    pub module: Name,
}

#[derive(Debug, Clone)]
pub enum EKind {
    Num(Name),
    Dec(Name, Name),
    Str(Name),
    /// `@` inside EXCEPT
    At,
    /// application of a user-defined / declared / parameter operator (arity 0 included)
    Apply(Callee, Vec<Arg>),
    /// built-in operator on expressions
    Bi(B, Vec<Expr>),
    Tuple(Vec<Expr>),
    SetEnum(Vec<Expr>),
    /// `f[a]` / `f[a, b]` (args already packed into a tuple expr when more than one)
    FcnApply(Expr, Expr),
    Record(Expr, Name),
    SubsetOf(BoundVars, Expr, Expr),
    SetOfAll(Expr, Vec<BoundGroup>),
    FcnCons(Vec<BoundGroup>, Expr),
    SetOfFcns(Expr, Expr),
    RcdCons(Vec<(Name, Expr)>),
    SetOfRcds(Vec<(Name, Expr)>),
    Except(Expr, Vec<ExceptSpec>),
    /// `[A]_v` (`boxed`) or `<<A>>_v`
    ActionSub { boxed: bool, act: Expr, sub: Expr },
    /// `WF_v(A)` / `SF_v(A)`
    Fair { strong: bool, sub: Expr, act: Expr },
    If(Expr, Expr, Expr),
    Case(Vec<(Expr, Expr)>, Option<Expr>),
    LetIn(Vec<Rc<OpDef>>, Expr),
    BQuant { forall: bool, bounds: Vec<BoundGroup>, body: Expr },
    UQuant { forall: bool, params: Vec<Rc<Param>>, body: Expr },
    /// `\EE x : F`, `\AA x : F`
    TQuant { forall: bool, params: Vec<Rc<Param>>, body: Expr },
    Choose(BoundVars, Option<Expr>, Expr),
    Conj(Vec<Expr>),
    Disj(Vec<Expr>),
    SubstIn(Rc<Vec<Subst>>, Expr),
    Label(Name, Vec<Rc<Param>>, Expr),
    /// a construct SANY accepts but this port does not model yet; evaluating it reports "not ported"
    Unsupported(Name),
}

/// Java `InstanceNode`
#[derive(Debug)]
pub struct InstanceNode {
    pub name: Option<Name>,
    pub local: bool,
    pub module: Rc<ModuleNode>,
    pub subs: Vec<Subst>,
    pub params: Vec<Rc<Param>>,
    pub loc: Loc,
}

#[derive(Debug)]
pub struct AssumeNode {
    pub name: Option<Name>,
    pub expr: Expr,
    pub module: Name,
    pub loc: Loc,
}

#[derive(Clone, Debug)]
pub enum Sym {
    Def(Rc<OpDef>),
    Decl(Rc<OpDecl>),
    Param(Rc<Param>),
    Builtin(B),
    Module(Rc<ModuleNode>),
}

impl Sym {
    pub fn same(&self, o: &Sym) -> bool {
        match (self, o) {
            (Sym::Def(a), Sym::Def(b)) => Rc::ptr_eq(a, b),
            (Sym::Decl(a), Sym::Decl(b)) => Rc::ptr_eq(a, b),
            (Sym::Param(a), Sym::Param(b)) => Rc::ptr_eq(a, b),
            (Sym::Builtin(a), Sym::Builtin(b)) => a == b,
            (Sym::Module(a), Sym::Module(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// Java: the order in which `Hashtable.elements()` lists the values of `keys` put into a default `Hashtable` (11 buckets, load factor
/// 0.75, `String.hashCode()`) in this order, after `builtins` other entries (the context of a module holds the built-in operators):
/// buckets from the last to the first, the newest entry of a bucket first.  Returns indexes into `keys`.
pub fn java_hashtable_order(keys: &[&str], builtins: usize) -> Vec<usize> {
    fn hash(s: &str) -> i32 {
        s.encode_utf16().fold(0i32, |h, c| h.wrapping_mul(31).wrapping_add(c as i32))
    }
    // entries: (hash, index into keys or usize::MAX for a built-in)
    let mut cap = 11usize;
    let mut tab: Vec<Vec<(i32, usize)>> = vec![vec![]; cap];
    let mut count = 0usize;
    let mut put = |h: i32, id: usize, cap: &mut usize, tab: &mut Vec<Vec<(i32, usize)>>, count: &mut usize| {
        let idx = ((h & 0x7FFF_FFFF) as usize) % *cap;
        if tab[idx].iter().any(|e| e.0 == h && (id == usize::MAX || e.1 == id)) && id != usize::MAX {
            return;
        }
        let mut idx = idx;
        if *count >= (*cap as f64 * 0.75) as usize {
            let old = std::mem::take(tab);
            let oc = *cap;
            *cap = oc * 2 + 1;
            *tab = vec![vec![]; *cap];
            for i in (0..oc).rev() {
                for e in old[i].iter() {
                    let j = ((e.0 & 0x7FFF_FFFF) as usize) % *cap;
                    tab[j].insert(0, *e);
                }
            }
            idx = ((h & 0x7FFF_FFFF) as usize) % *cap;
        }
        tab[idx].insert(0, (h, id));
        *count += 1;
    };
    for i in 0..builtins {
        let h = hash(&format!("\u{1}builtin{}", i));
        put(h, usize::MAX, &mut cap, &mut tab, &mut count);
    }
    for (i, k) in keys.iter().enumerate() {
        put(hash(k), i, &mut cap, &mut tab, &mut count);
    }
    let mut out = vec![];
    for b in tab.iter().rev() {
        for e in b {
            if e.1 != usize::MAX {
                out.push(e.1);
            }
        }
    }
    out
}

/// ordered symbol context (Java `Context`)
#[derive(Default, Debug, Clone)]
pub struct Ctx {
    pub items: Vec<(Name, Sym, Loc)>,
    pub map: HashMap<(bool, Name), usize>,
}

impl Ctx {
    pub fn get(&self, name: &str) -> Option<&Sym> {
        self.map.get(&(false, Name::from(name))).map(|&i| &self.items[i].1)
    }
    pub fn get_module(&self, name: &str) -> Option<&Sym> {
        self.map.get(&(true, Name::from(name))).map(|&i| &self.items[i].1)
    }
    pub fn insert(&mut self, name: Name, sym: Sym, loc: Loc) {
        let is_mod = matches!(sym, Sym::Module(_));
        let key = (is_mod, name.clone());
        if let Some(&i) = self.map.get(&key) {
            self.items[i] = (name, sym, loc);
        } else {
            self.map.insert(key, self.items.len());
            self.items.push((name, sym, loc));
        }
    }
    pub fn contains(&self, name: &str) -> bool {
        self.map.contains_key(&(false, Name::from(name)))
    }
}

/// Java `ModuleNode`
pub struct ModuleNode {
    pub name: Name,
    pub loc: Loc,
    pub is_standard: Cell<bool>,
    /// exported context (non-LOCAL symbols), in insertion order
    pub ctx: RefCell<Ctx>,
    pub extends: RefCell<Vec<Rc<ModuleNode>>>,
    pub instances: RefCell<Vec<Rc<InstanceNode>>>,
    /// own definitions (and INSTANCE copies), in order (Java `getOpDefs`)
    pub defs: RefCell<Vec<Rc<OpDef>>>,
    /// constants and variables declared by this module and by the modules it extends (declaration order)
    pub decls: RefCell<Vec<Rc<OpDecl>>>,
    pub assumes: RefCell<Vec<Rc<AssumeNode>>>,
    pub inner_modules: RefCell<Vec<Rc<ModuleNode>>>,
    /// true when no CONSTANT/VARIABLE is declared in the module or the modules it extends/instances
    pub param_free: Cell<bool>,
}

impl std::fmt::Debug for ModuleNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Module({})", self.name)
    }
}

impl ModuleNode {
    pub fn new(name: Name, loc: Loc) -> ModuleNode {
        ModuleNode {
            name,
            loc,
            is_standard: Cell::new(false),
            ctx: RefCell::new(Ctx::default()),
            extends: RefCell::new(vec![]),
            instances: RefCell::new(vec![]),
            defs: RefCell::new(vec![]),
            decls: RefCell::new(vec![]),
            assumes: RefCell::new(vec![]),
            inner_modules: RefCell::new(vec![]),
            param_free: Cell::new(true),
        }
    }

    /// constants declared in this module or the ones it extends
    pub fn constants(&self) -> Vec<Rc<OpDecl>> {
        self.decls.borrow().iter().filter(|d| d.kind == DeclKind::Constant).cloned().collect()
    }
    pub fn variables(&self) -> Vec<Rc<OpDecl>> {
        self.decls.borrow().iter().filter(|d| d.kind == DeclKind::Variable).cloned().collect()
    }
    pub fn lookup(&self, name: &str) -> Option<Sym> {
        self.ctx.borrow().get(name).cloned()
    }
}

thread_local! {
    static NEXT_ID: Cell<usize> = const { Cell::new(1) };
}

pub fn fresh_id() -> usize {
    NEXT_ID.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    })
}

impl ExprNode {
    /// immediate sub-expressions (operator arguments that are expressions included), in syntactic order
    pub fn children(&self) -> Vec<Expr> {
        let mut v: Vec<Expr> = Vec::new();
        match &self.kind {
            EKind::Num(_) | EKind::Dec(..) | EKind::Str(_) | EKind::At | EKind::Unsupported(_) => {}
            EKind::Apply(_, args) => {
                for a in args {
                    if let Arg::Expr(e) = a {
                        v.push(e.clone());
                    }
                }
            }
            EKind::Bi(_, es) | EKind::Tuple(es) | EKind::SetEnum(es) | EKind::Conj(es) | EKind::Disj(es) => v.extend(es.iter().cloned()),
            EKind::FcnApply(a, b) | EKind::SetOfFcns(a, b) => {
                v.push(a.clone());
                v.push(b.clone());
            }
            EKind::Record(a, _) => v.push(a.clone()),
            EKind::SubsetOf(_, s, p) => {
                v.push(s.clone());
                v.push(p.clone());
            }
            EKind::SetOfAll(e, bs) => {
                for b in bs {
                    v.push(b.set.clone());
                }
                v.push(e.clone());
            }
            EKind::FcnCons(bs, e) => {
                for b in bs {
                    v.push(b.set.clone());
                }
                v.push(e.clone());
            }
            EKind::RcdCons(f) | EKind::SetOfRcds(f) => v.extend(f.iter().map(|(_, e)| e.clone())),
            EKind::Except(e, specs) => {
                v.push(e.clone());
                for s in specs {
                    for c in &s.path {
                        if let ExceptComp::Index(ix) = c {
                            v.extend(ix.iter().cloned());
                        }
                    }
                    v.push(s.val.clone());
                }
            }
            EKind::ActionSub { act, sub, .. } => {
                v.push(act.clone());
                v.push(sub.clone());
            }
            EKind::Fair { sub, act, .. } => {
                v.push(sub.clone());
                v.push(act.clone());
            }
            EKind::If(a, b, c) => {
                v.push(a.clone());
                v.push(b.clone());
                v.push(c.clone());
            }
            EKind::Case(arms, o) => {
                for (a, b) in arms {
                    v.push(a.clone());
                    v.push(b.clone());
                }
                if let Some(o) = o {
                    v.push(o.clone());
                }
            }
            EKind::LetIn(defs, b) => {
                for d in defs {
                    if let Some(body) = d.body() {
                        v.push(body);
                    }
                }
                v.push(b.clone());
            }
            EKind::BQuant { bounds, body, .. } => {
                for b in bounds {
                    v.push(b.set.clone());
                }
                v.push(body.clone());
            }
            EKind::UQuant { body, .. } | EKind::TQuant { body, .. } => v.push(body.clone()),
            EKind::Choose(_, s, b) => {
                if let Some(s) = s {
                    v.push(s.clone());
                }
                v.push(b.clone());
            }
            EKind::SubstIn(_, b) => v.push(b.clone()),
            EKind::Label(_, _, e) => v.push(e.clone()),
        }
        v
    }
}
