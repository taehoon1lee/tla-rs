//! Typed syntax tree produced by `parser.rs` (Java: `tla2sany.parser.SyntaxTreeNode` trees, N_* kinds of
//! `tla2sany.st.SyntaxTreeConstants`). Unlike Java we use typed nodes; every node carries its source span
//! (first token begin .. last token end) because TLC prints action locations from it.

use std::sync::Arc;

pub type Name = Arc<str>;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Loc {
    pub bl: u32,
    pub bc: u32,
    pub el: u32,
    pub ec: u32,
}

impl Loc {
    pub fn span(a: Loc, b: Loc) -> Loc {
        Loc { bl: a.bl, bc: a.bc, el: b.el, ec: b.ec }
    }
}

#[derive(Clone, Debug)]
pub struct Ident {
    pub name: Name,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub name: Name,
    pub name_loc: Loc,
    pub loc: Loc,
    pub extends: Vec<Ident>,
    /// names of modules instantiated anywhere in this module's body (tree order, nested modules excluded)
    pub instances: Vec<Name>,
    pub units: Vec<Unit>,
}

#[derive(Debug, Clone)]
pub enum Unit {
    Variable(Vec<Ident>, Loc),
    Constant(Vec<OpDecl>, Loc),
    Recursive(Vec<OpDecl>, Loc),
    OpDef(Box<OpDef>),
    Instance(Box<Instance>),
    Assume(Box<Assume>),
    Theorem(Box<Theorem>),
    Module(Box<Module>),
    /// USE / HIDE at module level (parsed, semantically ignored)
    UseHide(Loc),
    Separator(Loc),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// `F` or `F(_, _)`
    Ident,
    /// `-. _` style prefix operator parameter
    Prefix,
    /// `_ + _`
    Infix,
    /// `_ ^+`
    Postfix,
}

/// A declared (formal) operator parameter or CONSTANT/RECURSIVE item.
#[derive(Debug, Clone)]
pub struct OpDecl {
    pub name: Name,
    pub arity: usize,
    pub shape: Shape,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub struct OpDef {
    pub local: bool,
    pub name: Name,
    pub name_loc: Loc,
    pub params: Vec<OpDecl>,
    pub body: DefBody,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub enum DefBody {
    Expr(Expr),
    /// `f[x \in S, ...] == e`  (function definition)
    Function(Vec<Bound>, Expr),
    /// `M(a, b) == INSTANCE ...`
    Instance(Instantiation),
}

#[derive(Debug, Clone)]
pub struct Instance {
    pub local: bool,
    pub inst: Instantiation,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub struct Instantiation {
    pub module: Name,
    pub module_loc: Loc,
    pub subs: Vec<Subst>,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub struct Subst {
    pub name: Name,
    pub name_loc: Loc,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct Assume {
    pub name: Option<Ident>,
    pub body: Expr,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub struct Theorem {
    pub name: Option<Ident>,
    pub body: TheoremBody,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub enum TheoremBody {
    Expr(Expr),
    AssumeProve(Box<AssumeProve>),
}

#[derive(Debug, Clone)]
pub struct AssumeProve {
    pub items: Vec<AssumeItem>,
    pub prove: Expr,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub enum AssumeItem {
    New(Loc),
    Expr(Expr),
    AssumeProve(Box<AssumeProve>),
}

#[derive(Debug, Clone)]
pub struct Bound {
    /// one identifier, several identifiers sharing the set (`x, y \in S`), or a tuple (`<<x, y>> \in S`)
    pub vars: Vec<Ident>,
    pub tuple: bool,
    pub set: Expr,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub enum BoundVar {
    One(Ident),
    Tuple(Vec<Ident>, Loc),
}

#[derive(Debug, Clone)]
pub enum ExceptComp {
    Field(Ident),
    Index(Vec<Expr>),
}

#[derive(Debug, Clone)]
pub struct ExceptSpec {
    pub path: Vec<ExceptComp>,
    pub val: Expr,
    pub loc: Loc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdKind {
    Ident,
    PrefixOp,
    InfixOp,
    PostfixOp,
}

#[derive(Debug, Clone)]
pub struct PrefixElem {
    /// name (identifier or operator symbol) before the `!`
    pub name: Name,
    pub kind: IdKind,
    pub args: Option<Vec<Expr>>,
    pub loc: Loc,
}

/// `A(x)!B!C` : prefix elements `A(x)!`, `B!` then the final name `C`. Java: N_GeneralId.
#[derive(Debug, Clone)]
pub struct GenId {
    pub prefix: Vec<PrefixElem>,
    pub name: Name,
    pub kind: IdKind,
    pub loc: Loc,
}

#[derive(Debug, Clone)]
pub enum QBinds {
    Bound(Vec<Bound>),
    Unbound(Vec<Ident>),
}

#[derive(Debug, Clone)]
pub enum LetItem {
    Def(Box<OpDef>),
    Recursive(Vec<OpDecl>, Loc),
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub loc: Loc,
    pub kind: Box<ExprKind>,
}

impl Expr {
    pub fn new(loc: Loc, kind: ExprKind) -> Expr {
        Expr { loc, kind: Box::new(kind) }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Num(Name),
    Real(Name, Name),
    Str(Name),
    Id(GenId),
    Appl(GenId, Vec<Expr>),
    /// canonical operator name (`\lnot`, `-.`, `[]`, `<>`, `ENABLED`, `UNCHANGED`, `SUBSET`, `UNION`, `DOMAIN`)
    Prefix(Name, Loc, Box<Expr>),
    /// canonical operator name
    Infix(Box<Expr>, Name, Loc, Box<Expr>),
    Postfix(Box<Expr>, Name, Loc),
    Times(Vec<Expr>),
    FcnAppl(Box<Expr>, Vec<Expr>),
    Record(Box<Expr>, Ident),
    Paren(Box<Expr>),
    Tuple(Vec<Expr>),
    SetEnum(Vec<Expr>),
    SubsetOf(BoundVar, Box<Expr>, Box<Expr>),
    SetOfAll(Box<Expr>, Vec<Bound>),
    FcnConst(Vec<Bound>, Box<Expr>),
    SetOfFcns(Box<Expr>, Box<Expr>),
    RcdCons(Vec<(Ident, Expr)>),
    SetOfRcds(Vec<(Ident, Expr)>),
    Except(Box<Expr>, Vec<ExceptSpec>),
    /// `[A]_v` (boxed) or `<<A>>_v`
    ActionExpr { boxed: bool, act: Box<Expr>, sub: Box<Expr> },
    Fairness { strong: bool, sub: Box<Expr>, act: Box<Expr> },
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Case(Vec<(Expr, Expr)>, Option<Box<Expr>>),
    LetIn(Vec<LetItem>, Box<Expr>),
    Quant { forall: bool, temporal: bool, binds: QBinds, body: Box<Expr> },
    Choose { var: BoundVar, set: Option<Box<Expr>>, body: Box<Expr> },
    Conj(Vec<Expr>),
    Disj(Vec<Expr>),
    Label(GenIdLabel, Box<Expr>),
    Lambda(Vec<Ident>, Box<Expr>),
}

/// label `name(p1, p2) ::` — Java: N_Label with an N_GeneralId / N_OpApplication
#[derive(Debug, Clone)]
pub struct GenIdLabel {
    pub name: Ident,
    pub params: Vec<Ident>,
}
