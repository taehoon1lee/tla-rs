//! Port of the JavaCC grammar `TT/javacc/tla+.jj` (TLAplusParser) + `OperatorStack` + `JunctionListContext`.
//!
//! The Java parser builds a concrete syntax tree; we build the typed tree of `ast.rs` directly. The control flow
//! (lookaheads, `belchDEF` DEFBREAK insertion, junction-list columns, operator stack reduction) mirrors the Java.

use crate::ast::*;
use crate::lexer::{tokenize, Tk, Token};
use crate::ops::{self, Operator};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct ParseError {
    /// text SANY prints for this failure (starts with `***Parse Error***` or `Lexical error`)
    pub text: String,
}

type PResult<T> = Result<T, ParseError>;

pub struct ParsedModule {
    pub module: Module,
    /// `TLAplusParser.dependencies()`: module names this module EXTENDS/INSTANCEs (duplicates kept, in order)
    pub deps: Vec<Name>,
}

/// Parse one source file (Java: `TLAplusParser.parse()`); runs on a big-stack thread because the grammar is
/// recursive on operator chains.
pub fn parse_source(src: &str) -> Result<ParsedModule, ParseError> {
    let src = src.to_string();
    let h = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut p = Parser::new(&src);
            p.compilation_unit()
        })
        .expect("spawn parser thread");
    match h.join() {
        Ok(r) => r,
        Err(_) => Err(ParseError { text: "***Parse Error***\nparser stack overflow or internal panic".into() }),
    }
}

fn is_prefix_op_tok(k: Tk) -> bool {
    matches!(k, Tk::Prefix | Tk::CaseSep)
}

fn is_ne_prefix_op_tok(k: Tk) -> bool {
    matches!(k, Tk::Prefix | Tk::CaseSep | Tk::MinusDot)
}

fn is_open_start(k: Tk) -> bool {
    matches!(k, Tk::Case | Tk::Choose | Tk::Exists | Tk::Forall | Tk::If | Tk::Let | Tk::TExists | Tk::TForall)
}

/// `isFieldNameToken`: keywords that may be used as record field names
fn is_field_name_token(k: Tk) -> bool {
    use Tk::*;
    matches!(
        k,
        Action | Assume | BoxAssume | Assumption | Case | Choose | Constant | Else | Except | Extends | If | Instance | Let
            | LetIn | Local | Module | New | Other | Proposition | Sf | State | Then | By | Only | Define | Df | Theorem | Use
            | Hide | Have | Obvious | Omitted | Lambda | Take | Proof | Prove | BoxProve | Qed | Recursive | Temporal | Pick
            | Witness | Suffices | Variable | Wf | With | Us
    ) || (k == Prefix) // op_112..op_116 (ENABLED UNCHANGED SUBSET UNION DOMAIN) -- see `is_field_name`
}

// ---------------------------------------------------------------------------------------------- operator stack

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SOpKind {
    GenPrefix,
    GenInfix,
    GenPostfix,
    GenNonExpPrefix,
}

#[derive(Debug, Clone)]
enum SNode {
    Expr(Expr),
    Op { kind: SOpKind, name: Name, loc: Loc },
    FcnArgs(Vec<Expr>, Loc),
    Void,
}

impl SNode {
    fn loc(&self) -> Loc {
        match self {
            SNode::Expr(e) => e.loc,
            SNode::Op { loc, .. } => *loc,
            SNode::FcnArgs(_, l) => *l,
            SNode::Void => Loc::default(),
        }
    }
}

struct OSel {
    node: SNode,
    op: Option<&'static Operator>,
}

fn loc_str(l: Loc) -> String {
    format!("line {}, col {} to line {}, col {}", l.bl, l.bc, l.el, l.ec)
}

// ---------------------------------------------------------------------------------------------- parser

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    jl: Vec<(Tk, u32)>,
    /// token ranges [start, end) of junction lists (excluded from the indentation check of enclosing items)
    jl_ranges: Vec<(usize, usize)>,
    proof_depth: i32,
    proof_stack: Vec<i32>,
    expecting: String,
    msg_stack: Vec<(&'static str, u32, u32)>,
    deps: Vec<Name>,
    internals: Vec<Name>,
    os: Vec<Vec<OSel>>,
    last_op: Option<&'static Operator>,
    fairness_hook: Option<Vec<Expr>>,
    mn: Option<Name>,
    lex_error: Option<String>,
    inst_stack: Vec<Vec<Name>>,
}

const MAX_PROOF_DEPTH: usize = 100;

impl Parser {
    fn new(src: &str) -> Parser {
        let mut toks = tokenize(src);
        // dummy token in front (Java: the initial `token` object whose `next` is the first token)
        let dummy = Token { kind: Tk::Eof, image: "".into(), bl: 0, bc: 0, el: 0, ec: 0 };
        toks.insert(0, dummy);
        let lex_error = toks.iter().find(|t| t.kind == Tk::Error).map(|t| t.image.to_string());
        Parser {
            toks,
            pos: 1,
            jl: Vec::new(),
            jl_ranges: Vec::new(),
            proof_depth: -1,
            proof_stack: vec![-1; MAX_PROOF_DEPTH],
            expecting: "nothing".into(),
            msg_stack: Vec::new(),
            deps: Vec::new(),
            internals: Vec::new(),
            os: Vec::new(),
            last_op: None,
            fairness_hook: None,
            mn: None,
            lex_error,
            inst_stack: Vec::new(),
        }
    }

    // ---- token access

    fn tok(&self, k: usize) -> &Token {
        let i = (self.pos + k - 1).min(self.toks.len() - 1);
        &self.toks[i]
    }
    fn kind(&self, k: usize) -> Tk {
        self.tok(k).kind
    }
    fn prev(&self) -> &Token {
        &self.toks[self.pos - 1]
    }
    fn advance(&mut self) -> Token {
        let t = self.toks[self.pos.min(self.toks.len() - 1)].clone();
        if !matches!(t.kind, Tk::Eof | Tk::DefBreak | Tk::Error) {
            // `new SyntaxTreeNode(mn, t)` interns the token image (UniqueString order matters to TLC)
            crate::intern::intern(&t.image);
        }
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn above(&self, col: u32) -> bool {
        match self.jl.last() {
            None => true,
            Some((_, c)) => *c < col,
        }
    }
    fn above_tok(&self, k: usize) -> bool {
        self.above(self.tok(k).bc)
    }
    fn is_new_bullet(&self, col: u32, kind: Tk) -> bool {
        match self.jl.last() {
            Some((k0, c)) => (kind == Tk::And || kind == Tk::Or) && *c == col && *k0 == kind,
            None => false,
        }
    }

    fn loc_of(t: &Token) -> Loc {
        Loc { bl: t.bl, bc: t.bc, el: t.el, ec: t.ec }
    }

    // ---- errors

    fn bpa(&mut self, name: &'static str) {
        let t = self.tok(1);
        self.msg_stack.push((name, t.bl, t.bc));
        self.expecting.clear();
    }
    fn epa(&mut self) {
        self.msg_stack.pop();
        self.expecting.clear();
    }

    fn stack_text(&self) -> String {
        let mut s = String::from("\n\nResidual stack trace follows:\n");
        let n = self.msg_stack.len();
        for i in (n.saturating_sub(5)..n).rev() {
            let (name, l, c) = self.msg_stack[i];
            s.push_str(&format!("{} starting at line {}, column {}.\n", name, l, c));
        }
        s
    }

    fn header(&self) -> String {
        let mut s = String::from("***Parse Error***\n");
        if !self.expecting.is_empty() {
            s.push_str(&format!("Was expecting \"{}\"\n", self.expecting));
        }
        s
    }

    /// JavaCC `ParseException` for an unexpected token
    fn unexpected(&self) -> ParseError {
        if let Some(l) = &self.lex_error {
            if self.toks.iter().skip(self.pos.saturating_sub(1)).take(8).any(|t| t.kind == Tk::Error) {
                return ParseError { text: l.clone() };
            }
        }
        let t = self.tok(1);
        let img = if t.kind == Tk::Eof { "<EOF>".to_string() } else { t.image.to_string() };
        let mut s = self.header();
        s.push_str(&format!(
            "Encountered \"{}\" at line {}, column {} and token \"{}\" ",
            img,
            t.bl,
            t.bc,
            self.prev().image
        ));
        s.push_str(&self.stack_text());
        ParseError { text: s }
    }

    /// `throw new ParseException(msg)`
    fn custom(&self, msg: &str) -> ParseError {
        let mut s = self.header();
        s.push_str(msg);
        s.push_str(&self.stack_text());
        ParseError { text: s }
    }

    fn expect(&mut self, k: Tk) -> PResult<Token> {
        if self.kind(1) == k {
            Ok(self.advance())
        } else {
            Err(self.unexpected())
        }
    }

    fn set_expecting(&mut self, s: &str) {
        self.expecting = s.to_string();
    }

    fn mn(&self) -> Name {
        self.mn.clone().unwrap_or_else(|| "".into())
    }

    // ---- belchDEF: insert a DEFBREAK token before the identifier/operator that the next `==` defines

    fn belch_def(&mut self) {
        let start_prev = self.pos - 1; // chain start (its reverse `next` is null)
        let mut prev = start_prev;
        let mut cur = self.pos;
        let last = self.toks.len() - 1;
        if cur > last {
            return;
        }
        let mut nxt = (cur + 1).min(last);
        loop {
            let nk = self.toks[nxt].kind;
            let ck = self.toks[cur].kind;
            if cur >= last
                || nk == Tk::Eof
                || nk == Tk::Theorem
                || nk == Tk::Proposition
                || nk == Tk::Assumption
                || nk == Tk::EndModule
                || ck == Tk::Theorem
                || ck == Tk::Proposition
            {
                return;
            }
            if ck == Tk::Def {
                let mut t = prev;
                let kind_at = |s: &Parser, i: usize| s.toks[i].kind;
                if matches!(kind_at(self, t), Tk::Rbr | Tk::Rsb) {
                    let mut depth = 1;
                    let mut aborted = false;
                    loop {
                        if t == start_prev {
                            aborted = true;
                            break;
                        }
                        t -= 1;
                        let k = kind_at(self, t);
                        if matches!(k, Tk::Lbr | Tk::Lsb) && depth == 1 {
                            break;
                        }
                        if matches!(k, Tk::Lbr | Tk::Lsb) && depth > 1 {
                            depth -= 1;
                        }
                        if matches!(k, Tk::Rbr | Tk::Rsb) {
                            depth += 1;
                        }
                    }
                    if aborted || t == start_prev {
                        // `t.next == null`: give up (Java: `if (t.next == null) break;`)
                        if t == start_prev {
                            return;
                        }
                    }
                    if t > start_prev && kind_at(self, t - 1) == Tk::Identifier {
                        t -= 1;
                    }
                } else if kind_at(self, t) == Tk::Identifier {
                    let identifier = t;
                    if t > start_prev {
                        let tn = t - 1; // t.next
                        let tnn_ident = tn > start_prev && kind_at(self, tn - 1) == Tk::Identifier;
                        let nk = kind_at(self, tn);
                        if nk.is_op() && !nk.is_postfix() && (!nk.is_infix() || tnn_ident) {
                            t = tn;
                            // t.next.kind == SUBSTITUTE
                            if t > start_prev && kind_at(self, t - 1) == Tk::Substitute {
                                t = identifier;
                            } else if kind_at(self, t).is_infix() && t > start_prev {
                                t -= 1;
                            }
                        }
                    }
                } else if kind_at(self, t).is_op() && t > start_prev {
                    t -= 1;
                }
                // insert before t unless already a DEFBREAK there
                if t == start_prev || self.toks[t - 1].kind != Tk::DefBreak {
                    let like = self.toks[t].clone();
                    let i = Token::synthetic(Tk::DefBreak, "Beginning of definition", &like);
                    self.toks.insert(t, i);
                }
                return;
            } else {
                prev = cur;
                cur = nxt;
                nxt = (nxt + 1).min(last);
            }
        }
    }

    // ---- compilation unit / module

    fn compilation_unit(&mut self) -> PResult<ParsedModule> {
        self.belch_def();
        // Prelude (pragma) is skipped by the lexer
        let m = self.module()?;
        let deps = std::mem::take(&mut self.deps);
        Ok(ParsedModule { module: m, deps })
    }

    fn module(&mut self) -> PResult<Module> {
        self.bpa("Module definition");
        self.inst_stack.push(Vec::new());
        let stack_level = self.internals.len();
        self.set_expecting("---- MODULE");
        // BeginModule
        self.bpa("Begin module");
        self.set_expecting("---- MODULE (beginning of module)");
        let begin = self.expect(Tk::BeginModule)?;
        self.set_expecting("Identifier");
        self.field_name_to_ident(1);
        let name_tok = self.expect(Tk::Identifier)?;
        if self.mn.is_none() {
            self.mn = Some(name_tok.image.clone());
        }
        self.set_expecting("----");
        self.expect(Tk::Separator)?;
        self.epa();
        let name = name_tok.image.clone();
        let name_loc = Self::loc_of(&name_tok);
        self.set_expecting("EXTENDS clause or module body");
        // Extends
        let mut extends = Vec::new();
        self.bpa("Extends");
        if self.kind(1) == Tk::Extends {
            self.advance();
            self.set_expecting("Identifier");
            self.field_name_to_ident(1);
            let t = self.expect(Tk::Identifier)?;
            self.add_dependency(&t.image);
            extends.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
            self.set_expecting("comma or module body");
            while self.kind(1) == Tk::Comma {
                self.advance();
                self.set_expecting("Identifier");
                self.field_name_to_ident(1);
                let t = self.expect(Tk::Identifier)?;
                self.add_dependency(&t.image);
                extends.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
            }
        }
        self.epa();
        self.set_expecting("Module body");
        let units = self.body()?;
        self.set_expecting("==== or more Module body");
        let end = self.expect(Tk::EndModule)?;
        self.internals.truncate(stack_level);
        self.internals.push(name.clone());
        self.epa();
        let loc = Loc::span(Self::loc_of(&begin), Self::loc_of(&end));
        let instances = self.inst_stack.pop().unwrap_or_default();
        Ok(Module { name, name_loc, loc, extends, instances, units })
    }

    fn add_dependency(&mut self, s: &Name) {
        if !self.internals.iter().any(|x| x == s) {
            self.deps.push(s.clone());
        }
    }

    fn field_name_to_ident(&mut self, k: usize) {
        let i = (self.pos + k - 1).min(self.toks.len() - 1);
        let kind = self.toks[i].kind;
        if self.is_field_name(kind, i) {
            self.toks[i].kind = Tk::Identifier;
        }
    }

    fn is_field_name(&self, kind: Tk, i: usize) -> bool {
        if kind == Tk::Prefix {
            matches!(&*self.toks[i].image, "ENABLED" | "UNCHANGED" | "SUBSET" | "UNION" | "DOMAIN")
        } else {
            is_field_name_token(kind) && kind != Tk::Prefix
        }
    }

    fn body(&mut self) -> PResult<Vec<Unit>> {
        self.bpa("Module body");
        self.set_expecting("LOCAL, INSTANCE, PROOF, ASSUMPTION, THEOREM, RECURSIVE, declaration, or definition");
        let mut units = Vec::new();
        loop {
            let k1 = self.kind(1);
            let u: Unit = match k1 {
                Tk::Separator => {
                    let t = self.advance();
                    Unit::Separator(Self::loc_of(&t))
                }
                Tk::Variable => self.variable_declaration()?,
                Tk::Constant => self.param_declaration()?,
                Tk::Local | Tk::DefBreak
                    if (k1 == Tk::DefBreak) || (k1 == Tk::Local && self.kind(2) == Tk::DefBreak) =>
                {
                    self.op_or_function_definition_unit()?
                }
                Tk::Recursive => self.recursive_unit()?,
                Tk::Local | Tk::Instance if k1 == Tk::Instance || self.kind(2) == Tk::Instance => self.instance_unit()?,
                Tk::Assume | Tk::Assumption => self.assumption()?,
                Tk::Theorem | Tk::Proposition => self.theorem()?,
                Tk::BeginModule => {
                    let m = self.module()?;
                    self.belch_def();
                    Unit::Module(Box::new(m))
                }
                Tk::Use if self.kind(2) != Tk::Only => self.use_hide_by_unit()?,
                Tk::Hide => self.use_hide_by_unit()?,
                _ => break,
            };
            units.push(u);
        }
        self.epa();
        Ok(units)
    }

    fn variable_declaration(&mut self) -> PResult<Unit> {
        self.bpa("variable declaration");
        let t0 = self.advance();
        self.set_expecting("Identifier");
        let mut names = Vec::new();
        let t = self.expect(Tk::Identifier)?;
        names.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
        self.set_expecting("comma or module body");
        let mut last = t;
        while self.kind(1) == Tk::Comma {
            self.advance();
            self.set_expecting("Identifier");
            let t = self.expect(Tk::Identifier)?;
            names.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
            last = t;
        }
        self.epa();
        Ok(Unit::Variable(names, Loc::span(Self::loc_of(&t0), Self::loc_of(&last))))
    }

    fn param_declaration(&mut self) -> PResult<Unit> {
        self.bpa("Parameter declaration");
        self.set_expecting("CONSTANT");
        let t0 = self.advance();
        self.set_expecting("Identifier, operator or _");
        let mut decls = vec![self.constant_declaration_item()?];
        self.set_expecting(",");
        while self.kind(1) == Tk::Comma {
            self.advance();
            self.set_expecting("Identifier, operator or _");
            decls.push(self.constant_declaration_item()?);
        }
        self.epa();
        let l = decls.last().unwrap().loc;
        Ok(Unit::Constant(decls, Loc::span(Self::loc_of(&t0), l)))
    }

    fn recursive_unit(&mut self) -> PResult<Unit> {
        let (d, l) = self.recursive()?;
        Ok(Unit::Recursive(d, l))
    }

    fn recursive(&mut self) -> PResult<(Vec<OpDecl>, Loc)> {
        self.bpa("Recursive");
        self.set_expecting("RECURSIVE");
        let t0 = self.expect(Tk::Recursive)?;
        self.set_expecting("Identifier, operator or _");
        let mut decls = vec![self.constant_declaration_item()?];
        self.set_expecting(",");
        while self.kind(1) == Tk::Comma {
            self.advance();
            self.set_expecting("Identifier, operator or _");
            decls.push(self.constant_declaration_item()?);
            self.set_expecting("`,' or `)'");
        }
        self.epa();
        let l = decls.last().unwrap().loc;
        Ok((decls, Loc::span(Self::loc_of(&t0), l)))
    }

    /// ConstantDeclarationItems: `Id [( _ , _ )] | prefixop _ | _ infixop _ | _ postfixop`
    fn constant_declaration_item(&mut self) -> PResult<OpDecl> {
        self.bpa("Constant declaration items");
        self.set_expecting("Identifier, _ or prefix op");
        let r = if self.kind(1) == Tk::Identifier {
            let t = self.advance();
            let mut arity = 0;
            let mut end = Self::loc_of(&t);
            self.set_expecting("(, comma, or Module Body");
            if self.kind(1) == Tk::Lbr && self.kind(2) == Tk::Us {
                self.advance();
                self.advance();
                arity = 1;
                self.set_expecting("comma or )");
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    self.set_expecting("_");
                    self.expect(Tk::Us)?;
                    arity += 1;
                    self.set_expecting("comma or )");
                }
                let r = self.expect(Tk::Rbr)?;
                end = Self::loc_of(&r);
            }
            OpDecl { name: t.image.clone(), arity, shape: Shape::Ident, loc: Loc::span(Self::loc_of(&t), end) }
        } else if is_ne_prefix_op_tok(self.kind(1)) {
            let t = self.advance();
            self.set_expecting("_");
            let u = self.expect(Tk::Us)?;
            OpDecl {
                name: ops::resolve_synonym(&t.image).into(),
                arity: 1,
                shape: Shape::Prefix,
                loc: Loc::span(Self::loc_of(&t), Self::loc_of(&u)),
            }
        } else if self.kind(1) == Tk::Us {
            let t0 = self.advance();
            self.set_expecting("prefix or postfix operator");
            if self.kind(1).is_infix() {
                let op = self.advance();
                self.set_expecting("_");
                let u = self.expect(Tk::Us)?;
                OpDecl {
                    name: ops::resolve_synonym(&op.image).into(),
                    arity: 2,
                    shape: Shape::Infix,
                    loc: Loc::span(Self::loc_of(&t0), Self::loc_of(&u)),
                }
            } else if self.kind(1).is_postfix() {
                let op = self.advance();
                OpDecl {
                    name: ops::resolve_synonym(&op.image).into(),
                    arity: 1,
                    shape: Shape::Postfix,
                    loc: Loc::span(Self::loc_of(&t0), Self::loc_of(&op)),
                }
            } else {
                return Err(self.unexpected());
            }
        } else {
            return Err(self.unexpected());
        };
        self.epa();
        Ok(r)
    }

    /// IdentDecl | SomeFixDecl (formal parameters of a definition)
    fn param_decl(&mut self) -> PResult<OpDecl> {
        if self.kind(1) == Tk::Identifier {
            self.bpa("Identifier Declation");
            let t = self.advance();
            let mut arity = 0;
            let mut end = Self::loc_of(&t);
            self.set_expecting("( or ...");
            if self.kind(1) == Tk::Lbr {
                self.advance();
                self.set_expecting("_");
                self.expect(Tk::Us)?;
                arity = 1;
                self.set_expecting("COMMA or )");
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    self.set_expecting("_");
                    self.expect(Tk::Us)?;
                    arity += 1;
                    self.set_expecting("COMMA or )");
                }
                let r = self.expect(Tk::Rbr)?;
                end = Self::loc_of(&r);
            }
            self.epa();
            Ok(OpDecl { name: t.image.clone(), arity, shape: Shape::Ident, loc: Loc::span(Self::loc_of(&t), end) })
        } else {
            self.bpa("Op. Symbol Declaration");
            let r = if is_ne_prefix_op_tok(self.kind(1)) {
                let t = self.advance();
                self.set_expecting("_");
                let u = self.expect(Tk::Us)?;
                OpDecl {
                    name: ops::resolve_synonym(&t.image).into(),
                    arity: 1,
                    shape: Shape::Prefix,
                    loc: Loc::span(Self::loc_of(&t), Self::loc_of(&u)),
                }
            } else if self.kind(1) == Tk::Us {
                let t0 = self.advance();
                self.set_expecting("infix or postfix operator");
                if self.kind(1).is_infix() {
                    let op = self.advance();
                    self.set_expecting("_");
                    let u = self.expect(Tk::Us)?;
                    OpDecl {
                        name: ops::resolve_synonym(&op.image).into(),
                        arity: 2,
                        shape: Shape::Infix,
                        loc: Loc::span(Self::loc_of(&t0), Self::loc_of(&u)),
                    }
                } else if self.kind(1).is_postfix() {
                    let op = self.advance();
                    OpDecl {
                        name: ops::resolve_synonym(&op.image).into(),
                        arity: 1,
                        shape: Shape::Postfix,
                        loc: Loc::span(Self::loc_of(&t0), Self::loc_of(&op)),
                    }
                } else {
                    return Err(self.unexpected());
                }
            } else {
                return Err(self.unexpected());
            };
            self.epa();
            Ok(r)
        }
    }

    fn op_or_function_definition_unit(&mut self) -> PResult<Unit> {
        Ok(Unit::OpDef(Box::new(self.op_or_function_definition()?)))
    }

    /// `OperatorOrFunctionDefinition` (also ModuleDefinition)
    fn op_or_function_definition(&mut self) -> PResult<OpDef> {
        self.bpa("Definition");
        self.set_expecting("LOCAL, Identifier or Operator Symbol");
        let mut local = false;
        let mut start: Option<Loc> = None;
        if self.kind(1) == Tk::Local {
            let t = self.advance();
            start = Some(Self::loc_of(&t));
            local = true;
        }
        self.expect(Tk::DefBreak)?;
        self.set_expecting("LOCAL, Identifier or Operator Symbol");
        let k1 = self.kind(1);
        let k2 = self.kind(2);
        let first_loc = Self::loc_of(self.tok(1));
        let def: OpDef;
        if k1 == Tk::Identifier && k2 == Tk::Lsb {
            // function definition
            let id = self.advance();
            self.set_expecting("[");
            self.advance();
            self.set_expecting("Identifier");
            let mut bounds = vec![self.quant_bound()?];
            self.set_expecting("COMMA or ]");
            while self.kind(1) == Tk::Comma {
                self.advance();
                self.set_expecting("Identifier");
                bounds.push(self.quant_bound()?);
            }
            self.expect(Tk::Rsb)?;
            self.set_expecting("==");
            self.expect(Tk::Def)?;
            self.belch_def();
            self.set_expecting("Expression");
            let e = self.expression()?;
            let loc = Loc::span(start.unwrap_or(first_loc), e.loc);
            def = OpDef {
                local,
                name: id.image.clone(),
                name_loc: Self::loc_of(&id),
                params: Vec::new(),
                body: DefBody::Function(bounds, e),
                loc,
            };
        } else if k1 == Tk::Identifier && self.kind(2).is_postfix() {
            let id = self.advance();
            let op = self.advance();
            self.set_expecting("==");
            self.expect(Tk::Def)?;
            self.belch_def();
            self.set_expecting("Expression");
            let e = self.expression()?;
            let loc = Loc::span(start.unwrap_or(first_loc), e.loc);
            def = OpDef {
                local,
                name: ops::resolve_synonym(&op.image).into(),
                name_loc: Self::loc_of(&op),
                params: vec![OpDecl { name: id.image.clone(), arity: 0, shape: Shape::Ident, loc: Self::loc_of(&id) }],
                body: DefBody::Expr(e),
                loc,
            };
        } else if k1 == Tk::Identifier && self.kind(2).is_infix() {
            let a = self.advance();
            let op = self.advance();
            self.set_expecting("Identifier");
            let b = self.expect(Tk::Identifier)?;
            self.set_expecting("==");
            self.expect(Tk::Def)?;
            self.belch_def();
            self.set_expecting("Expression");
            let e = self.expression()?;
            let loc = Loc::span(start.unwrap_or(first_loc), e.loc);
            def = OpDef {
                local,
                name: ops::resolve_synonym(&op.image).into(),
                name_loc: Self::loc_of(&op),
                params: vec![
                    OpDecl { name: a.image.clone(), arity: 0, shape: Shape::Ident, loc: Self::loc_of(&a) },
                    OpDecl { name: b.image.clone(), arity: 0, shape: Shape::Ident, loc: Self::loc_of(&b) },
                ],
                body: DefBody::Expr(e),
                loc,
            };
        } else if k1 == Tk::Identifier && (k2 == Tk::Lbr || k2 == Tk::Def) {
            // IdentLHS
            self.bpa("Identifier LHS");
            let id = self.advance();
            self.set_expecting("( or ==");
            let mut params = Vec::new();
            if self.kind(1) == Tk::Lbr {
                self.advance();
                self.set_expecting("Identifier Declaration, prefix op, _ or )");
                params.push(self.param_decl()?);
                self.set_expecting("COMMA or )");
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    self.set_expecting("Identifier Declaration, prefix op or _");
                    params.push(self.param_decl()?);
                    self.set_expecting("COMMA or )");
                }
                self.expect(Tk::Rbr)?;
            }
            self.epa();
            self.set_expecting("==");
            self.expect(Tk::Def)?;
            self.belch_def();
            self.set_expecting("Expression or Instance");
            if self.kind(1) == Tk::Instance {
                let inst = self.instantiation()?;
                let loc = Loc::span(start.unwrap_or(first_loc), inst.loc);
                def = OpDef { local, name: id.image.clone(), name_loc: Self::loc_of(&id), params, body: DefBody::Instance(inst), loc };
            } else {
                let e = self.expression()?;
                let loc = Loc::span(start.unwrap_or(first_loc), e.loc);
                def = OpDef { local, name: id.image.clone(), name_loc: Self::loc_of(&id), params, body: DefBody::Expr(e), loc };
            }
        } else if is_ne_prefix_op_tok(k1) {
            // PrefixLHS
            let op = self.advance();
            self.set_expecting("Identifier");
            let a = self.expect(Tk::Identifier)?;
            self.set_expecting("==");
            self.expect(Tk::Def)?;
            self.belch_def();
            self.set_expecting("Expression");
            let e = self.expression()?;
            let loc = Loc::span(start.unwrap_or(first_loc), e.loc);
            let name: Name = if &*op.image == "-." { "-.".into() } else { ops::resolve_synonym(&op.image).into() };
            def = OpDef {
                local,
                name,
                name_loc: Self::loc_of(&op),
                params: vec![OpDecl { name: a.image.clone(), arity: 0, shape: Shape::Ident, loc: Self::loc_of(&a) }],
                body: DefBody::Expr(e),
                loc,
            };
        } else {
            return Err(self.unexpected());
        }
        self.epa();
        Ok(def)
    }

    fn instance_unit(&mut self) -> PResult<Unit> {
        self.bpa("Instance");
        self.set_expecting("LOCAL or instance");
        let mut local = false;
        let mut start = None;
        if self.kind(1) == Tk::Local {
            let t = self.advance();
            local = true;
            start = Some(Self::loc_of(&t));
        }
        let inst = self.instantiation()?;
        self.set_expecting("COMMA or Module Body");
        self.epa();
        let loc = Loc::span(start.unwrap_or(inst.loc), inst.loc);
        Ok(Unit::Instance(Box::new(Instance { local, inst, loc })))
    }

    fn instantiation(&mut self) -> PResult<Instantiation> {
        self.bpa("NonLocalInstance");
        let t0 = self.expect(Tk::Instance)?;
        self.set_expecting("Module identifier");
        self.field_name_to_ident(1);
        let m = self.expect(Tk::Identifier)?;
        self.add_dependency(&m.image);
        if let Some(top) = self.inst_stack.last_mut() {
            top.push(m.image.clone());
        }
        self.set_expecting("WITH or another definition.");
        let mut subs = Vec::new();
        let mut end = Self::loc_of(&m);
        if self.kind(1) == Tk::With {
            self.advance();
            self.set_expecting("");
            let s = self.substitution()?;
            end = s.expr.loc;
            subs.push(s);
            // ( LOOKAHEAD(3) COMMA Substitution )*
            while self.kind(1) == Tk::Comma
                && (self.kind(2) == Tk::Identifier || is_ne_prefix_op_tok(self.kind(2)) || self.kind(2).is_infix() || self.kind(2).is_postfix())
                && self.kind(3) == Tk::Substitute
            {
                self.advance();
                let s = self.substitution()?;
                end = s.expr.loc;
                subs.push(s);
            }
        }
        self.epa();
        Ok(Instantiation { module: m.image.clone(), module_loc: Self::loc_of(&m), subs, loc: Loc::span(Self::loc_of(&t0), end) })
    }

    fn substitution(&mut self) -> PResult<Subst> {
        self.bpa("Substitution");
        let k = self.kind(1);
        let (name, nloc): (Name, Loc) = if k == Tk::Identifier {
            let t = self.advance();
            (t.image.clone(), Self::loc_of(&t))
        } else if is_ne_prefix_op_tok(k) || k.is_infix() || k.is_postfix() {
            let t = self.advance();
            (ops::resolve_synonym(&t.image).into(), Self::loc_of(&t))
        } else {
            return Err(self.unexpected());
        };
        self.set_expecting("<-");
        self.expect(Tk::Substitute)?;
        self.set_expecting("Expression or Op. Symbol");
        let e = self.op_or_expr()?;
        self.epa();
        Ok(Subst { name, name_loc: nloc, expr: e })
    }

    fn assumption(&mut self) -> PResult<Unit> {
        self.bpa("Assumption");
        self.set_expecting("ASSUM...");
        let t0 = self.advance();
        let mut name = None;
        // [ LOOKAHEAD(2) (DEFBREAK)? Identifier DEF ]
        let (k1, k2, k3) = (self.kind(1), self.kind(2), self.kind(3));
        if (k1 == Tk::DefBreak && k2 == Tk::Identifier && k3 == Tk::Def) || (k1 == Tk::Identifier && k2 == Tk::Def) {
            if k1 == Tk::DefBreak {
                self.advance();
            }
            let id = self.advance();
            self.set_expecting("==");
            self.expect(Tk::Def)?;
            name = Some(Ident { name: id.image.clone(), loc: Self::loc_of(&id) });
        }
        self.belch_def();
        self.set_expecting("Expression");
        let e = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), e.loc);
        Ok(Unit::Assume(Box::new(Assume { name, body: e, loc })))
    }

    fn theorem(&mut self) -> PResult<Unit> {
        self.bpa("Theorem");
        self.set_expecting("THEOREM, PROPOSITION");
        let t0 = self.advance();
        self.set_expecting("Identifier, Assume-Prove or Expression");
        let mut name = None;
        if self.kind(1) == Tk::Identifier && self.kind(2) == Tk::Def {
            let id = self.advance();
            self.set_expecting("==");
            self.advance();
            name = Some(Ident { name: id.image.clone(), loc: Self::loc_of(&id) });
        }
        self.belch_def();
        let body = if matches!(self.kind(1), Tk::Assume | Tk::BoxAssume) {
            TheoremBody::AssumeProve(Box::new(self.assume_prove()?))
        } else {
            TheoremBody::Expr(self.expression()?)
        };
        let mut end = match &body {
            TheoremBody::Expr(e) => e.loc,
            TheoremBody::AssumeProve(a) => a.loc,
        };
        if self.begins_proof(1) {
            let l = self.proof()?;
            end = Loc::span(end, l);
        }
        self.epa();
        Ok(Unit::Theorem(Box::new(Theorem { name, body, loc: Loc::span(Self::loc_of(&t0), end) })))
    }

    fn assume_prove(&mut self) -> PResult<AssumeProve> {
        self.bpa("Assume-Prove");
        // optional label (Identifier ::) is accepted but never produced by real specs
        let t0;
        if self.kind(1) == Tk::Identifier && self.kind(2) == Tk::ColonColon {
            self.advance();
            self.advance();
        }
        if matches!(self.kind(1), Tk::Assume | Tk::BoxAssume) {
            t0 = self.advance();
        } else {
            return Err(self.unexpected());
        }
        self.set_expecting("Expression, Declaration, or AssumeProve");
        let mut items = Vec::new();
        items.push(self.assume_item()?);
        self.set_expecting("PROVE or `,'");
        while self.kind(1) == Tk::Comma {
            self.advance();
            self.set_expecting("Expression, Declaration, or AssumeProve");
            items.push(self.assume_item()?);
            self.set_expecting("PROVE or `,'");
        }
        if !matches!(self.kind(1), Tk::Prove | Tk::BoxProve) {
            return Err(self.unexpected());
        }
        self.advance();
        self.set_expecting("Expression");
        let prove = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), prove.loc);
        Ok(AssumeProve { items, prove, loc })
    }

    fn assume_item(&mut self) -> PResult<AssumeItem> {
        let k1 = self.kind(1);
        if matches!(k1, Tk::Assume | Tk::BoxAssume)
            || (self.kind(2) == Tk::ColonColon && matches!(self.kind(3), Tk::Assume | Tk::BoxAssume))
        {
            Ok(AssumeItem::AssumeProve(Box::new(self.assume_prove()?)))
        } else if matches!(k1, Tk::New | Tk::Constant | Tk::Variable | Tk::State | Tk::Action | Tk::Temporal)
            && (k1 != Tk::Constant || true)
        {
            let l = self.new_symb()?;
            Ok(AssumeItem::New(l))
        } else {
            Ok(AssumeItem::Expr(self.expression()?))
        }
    }

    /// NewSymb (parsed and ignored)
    fn new_symb(&mut self) -> PResult<Loc> {
        self.bpa("NEW symbol declaration");
        self.set_expecting("NEW, CONSTANT, VARIABLE, STATE, ACTION, or TEMPORAL");
        let t0 = self.tok(1).clone();
        let mut last = Self::loc_of(&t0);
        let has_new = self.kind(1) == Tk::New;
        if has_new {
            self.advance();
        }
        match self.kind(1) {
            Tk::Constant => {
                self.advance();
                self.set_expecting("Constant declaration");
                // IdentDecl [\in Expression] | SomeFixDecl
                if self.kind(1) == Tk::Identifier {
                    let d = self.param_decl()?;
                    last = d.loc;
                    if self.kind(1) == Tk::In {
                        if d.arity > 0 {
                            return Err(self.custom(&format!(
                                "declared symbol with arguments before \\in at {}",
                                loc_str(d.loc)
                            )));
                        }
                        self.advance();
                        self.set_expecting("Expression");
                        let e = self.expression()?;
                        last = e.loc;
                    }
                } else {
                    let d = self.param_decl()?;
                    last = d.loc;
                }
            }
            Tk::Variable => {
                self.advance();
                self.set_expecting("Identifier");
                let t = self.expect(Tk::Identifier)?;
                last = Self::loc_of(&t);
            }
            Tk::State | Tk::Action | Tk::Temporal => {
                self.advance();
                self.set_expecting("Declaration");
                let d = self.param_decl()?;
                last = d.loc;
            }
            _ => {
                if has_new {
                    // `NEW x \in S` without CONSTANT
                    self.set_expecting("Constant declaration");
                    if self.kind(1) == Tk::Identifier {
                        let d = self.param_decl()?;
                        last = d.loc;
                        if self.kind(1) == Tk::In {
                            self.advance();
                            let e = self.expression()?;
                            last = e.loc;
                        }
                    } else {
                        let d = self.param_decl()?;
                        last = d.loc;
                    }
                } else {
                    return Err(self.unexpected());
                }
            }
        }
        self.epa();
        Ok(Loc::span(Self::loc_of(&t0), last))
    }

    // ---- proofs (parsed, not kept)

    fn level_of_lexeme(tok: &Token) -> i32 {
        let im: Vec<char> = tok.image.chars().collect();
        if im.len() < 2 {
            return 0;
        }
        if im[1] == '*' {
            return -1;
        }
        if im[1] == '+' {
            return -2;
        }
        let s: String = im[1..].iter().take_while(|c| **c != '>').collect();
        s.parse::<i32>().unwrap_or(i32::MAX)
    }

    fn push_proof_level(&mut self) -> PResult<()> {
        self.proof_depth += 1;
        if self.proof_depth as usize >= MAX_PROOF_DEPTH {
            return Err(self.custom(&format!("Proofs nested more than {}deep.", MAX_PROOF_DEPTH)));
        }
        self.proof_stack[self.proof_depth as usize] = -1;
        Ok(())
    }
    fn pop_proof_level(&mut self) -> PResult<()> {
        if self.proof_depth < 0 {
            return Err(self.custom("Parser bug: an extra QED step found."));
        }
        self.proof_depth -= 1;
        Ok(())
    }
    fn proof_level(&self) -> i32 {
        if self.proof_depth < 0 {
            self.proof_depth
        } else {
            self.proof_stack[self.proof_depth as usize]
        }
    }

    fn begins_proof(&self, k: usize) -> bool {
        let tok = self.tok(k);
        let im: Vec<char> = tok.image.chars().collect();
        if im.len() < 2 {
            return false;
        }
        if im[1] == '*' {
            return self.proof_depth < 0;
        }
        if im[1] == '+' {
            return true;
        }
        match tok.kind {
            Tk::ProofStepLexeme | Tk::BareLevelLexeme | Tk::UnnumberedStepLexeme | Tk::ProofStepDotLexeme => {
                if self.proof_depth < 0 {
                    return true;
                }
                let tl = Self::level_of_lexeme(tok);
                self.proof_stack[self.proof_depth as usize] >= 0 && tl > self.proof_stack[self.proof_depth as usize]
            }
            Tk::By | Tk::Proof | Tk::Obvious | Tk::Omitted => true,
            _ => false,
        }
    }

    fn correct_level(&mut self, tok: &Token) -> bool {
        let tl = Self::level_of_lexeme(tok);
        let mut last_level = -1;
        if self.proof_depth > 0 {
            last_level = self.proof_stack[self.proof_depth as usize - 1];
        }
        let d = self.proof_depth.max(0) as usize;
        match tl {
            -1 => {
                if self.proof_stack[d] < 0 {
                    self.proof_stack[d] = last_level + 1;
                }
                true
            }
            -2 => {
                if self.proof_stack[d] < 0 {
                    self.proof_stack[d] = last_level + 1;
                    true
                } else {
                    false
                }
            }
            _ => {
                if self.proof_stack[d] < 0 {
                    self.proof_stack[d] = tl;
                    tl > last_level
                } else {
                    self.proof_stack[d] == tl
                }
            }
        }
    }

    fn is_step_start(k: Tk) -> bool {
        matches!(
            k,
            Tk::ProofStepLexeme | Tk::ProofImplicitStepLexeme | Tk::ProofStepDotLexeme | Tk::BareLevelLexeme | Tk::UnnumberedStepLexeme
        )
    }

    /// Proof(): returns the span of the proof
    fn proof(&mut self) -> PResult<Loc> {
        self.push_proof_level()?;
        self.bpa("Proof");
        let start = Self::loc_of(self.tok(1));
        let mut end = start;
        if self.kind(1) == Tk::By || self.kind(2) == Tk::By {
            end = self.use_hide_or_by()?;
        } else if (self.kind(1) == Tk::Proof && matches!(self.kind(2), Tk::Obvious | Tk::Omitted))
            || matches!(self.kind(1), Tk::Obvious | Tk::Omitted)
        {
            if self.kind(1) == Tk::Proof {
                self.advance();
            }
            let t = self.advance();
            end = Self::loc_of(&t);
        } else {
            if self.kind(1) == Tk::Proof && Self::is_step_start(self.kind(2)) || self.kind(1) == Tk::Proof {
                let t = self.advance();
                end = Self::loc_of(&t);
            }
            while self.kind(2) != Tk::Qed && Self::is_step_start(self.kind(1)) {
                end = self.step()?;
                self.set_expecting("a proof step");
            }
            end = self.qed_step()?;
        }
        self.epa();
        self.pop_proof_level()?;
        Ok(Loc::span(start, end))
    }

    /// UseOrHideOrBy (returns the end location)
    fn use_hide_or_by(&mut self) -> PResult<Loc> {
        self.bpa("UseOrHideOrBy");
        let mut is_by = false;
        let mut last;
        if self.kind(1) == Tk::Proof {
            self.advance();
        }
        match self.kind(1) {
            Tk::By => {
                let t = self.advance();
                last = Self::loc_of(&t);
                is_by = true;
                if self.kind(1) == Tk::Only {
                    let t = self.advance();
                    last = Self::loc_of(&t);
                }
            }
            Tk::Use => {
                let t = self.advance();
                last = Self::loc_of(&t);
                if self.kind(1) == Tk::Only {
                    let t = self.advance();
                    last = Self::loc_of(&t);
                }
            }
            Tk::Hide => {
                let t = self.advance();
                last = Self::loc_of(&t);
            }
            _ => return Err(self.unexpected()),
        }
        self.set_expecting("an expression, `MODULE' or `DEF'");
        // ( (MODULE Identifier | Expression) (COMMA (MODULE Identifier | Expression))* )?
        if self.kind(1) != Tk::Df && !self.proof_item_end() {
            last = self.module_or_expr()?;
            while self.kind(1) == Tk::Comma {
                self.advance();
                self.set_expecting("MODULE or expression");
                last = self.module_or_expr()?;
                self.set_expecting(if is_by { "comma, DEF, or [.]" } else { "comma, DEF, or proof step" });
            }
        }
        if self.kind(1) == Tk::Df {
            let t = self.advance();
            last = Self::loc_of(&t);
            self.set_expecting("MODULE or expression");
            last = self.module_or_expr().map(|l| l).unwrap_or(last);
            while self.kind(1) == Tk::Comma {
                self.advance();
                self.set_expecting("MODULE or expression");
                last = self.module_or_expr()?;
            }
        }
        self.epa();
        Ok(last)
    }

    /// can the next token NOT begin an Expression/MODULE item? (JavaCC would simply fail the optional group)
    fn proof_item_end(&self) -> bool {
        let k = self.kind(1);
        !(k == Tk::Module || self.can_start_expression(k))
    }

    fn can_start_expression(&self, k: Tk) -> bool {
        k.is_op()
            || matches!(
                k,
                Tk::Identifier
                    | Tk::NumberLiteral
                    | Tk::StringLiteral
                    | Tk::Lbr
                    | Tk::Lbc
                    | Tk::Lsb
                    | Tk::Lab
                    | Tk::Wf
                    | Tk::Sf
                    | Tk::ProofStepLexeme
                    | Tk::ProofImplicitStepLexeme
            )
            || is_open_start(k)
    }

    fn module_or_expr(&mut self) -> PResult<Loc> {
        if self.kind(1) == Tk::Module {
            self.advance();
            self.set_expecting("identifier");
            let t = self.expect(Tk::Identifier)?;
            Ok(Self::loc_of(&t))
        } else {
            let e = self.expression()?;
            Ok(e.loc)
        }
    }

    fn use_hide_by_unit(&mut self) -> PResult<Unit> {
        let l = self.use_hide_or_by()?;
        Ok(Unit::UseHide(l))
    }

    fn step_start(&mut self, qed: bool) -> PResult<Token> {
        self.set_expecting("Step number");
        let k = self.kind(1);
        if !Self::is_step_start(k) {
            return Err(self.unexpected());
        }
        let t = self.advance();
        if !self.correct_level(&t) {
            let l = Self::loc_of(&t);
            return Err(self.custom(&format!(
                "{}: {}",
                loc_str(l),
                if qed { "QED step's number has bad level." } else { "step's number has bad level." }
            )));
        }
        Ok(t)
    }

    fn qed_step(&mut self) -> PResult<Loc> {
        self.bpa("QED step");
        let t0 = self.step_start(true)?;
        self.set_expecting("QED");
        let q = self.expect(Tk::Qed)?;
        let mut end = Self::loc_of(&q);
        if self.begins_proof(1) {
            let l = self.proof()?;
            end = l;
        }
        self.epa();
        Ok(Loc::span(Self::loc_of(&t0), end))
    }

    fn step(&mut self) -> PResult<Loc> {
        self.bpa("Step");
        let t0 = self.step_start(false)?;
        self.set_expecting("proof step");
        let mut end = Self::loc_of(&t0);
        let mut may_have_proof = false;
        let k = self.kind(1);
        if matches!(k, Tk::Use | Tk::Hide) {
            end = self.use_hide_or_by()?;
        } else if k == Tk::Instance {
            end = self.instantiation()?.loc;
        } else if matches!(k, Tk::DefBreak | Tk::Define) {
            // DefStep
            self.bpa("DefStep");
            if self.kind(1) == Tk::Define {
                let t = self.advance();
                end = Self::loc_of(&t);
            }
            loop {
                if self.kind(1) == Tk::DefBreak || (self.kind(1) == Tk::Local && self.kind(2) == Tk::DefBreak) {
                    let d = self.op_or_function_definition()?;
                    end = d.loc;
                } else {
                    break;
                }
            }
            self.epa();
        } else if k == Tk::Have {
            self.advance();
            self.set_expecting("expression");
            end = self.expression()?.loc;
        } else if k == Tk::Take {
            self.advance();
            self.set_expecting("identifier");
            if self.take_lookahead_bound() {
                end = self.quant_bound()?.loc;
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    end = self.quant_bound()?.loc;
                }
            } else {
                let t = self.expect(Tk::Identifier)?;
                end = Self::loc_of(&t);
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    let t = self.expect(Tk::Identifier)?;
                    end = Self::loc_of(&t);
                }
            }
        } else if k == Tk::Witness {
            self.advance();
            self.set_expecting("expression");
            end = self.expression()?.loc;
            while self.kind(1) == Tk::Comma {
                self.advance();
                end = self.expression()?.loc;
            }
        } else if k == Tk::Pick {
            self.advance();
            self.set_expecting("identifier");
            if self.lookahead_ident_list_then(Tk::Colon) {
                self.expect(Tk::Identifier)?;
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    self.expect(Tk::Identifier)?;
                }
            } else {
                self.quant_bound()?;
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    self.quant_bound()?;
                }
            }
            self.expect(Tk::Colon)?;
            self.set_expecting("expression");
            end = self.expression()?.loc;
            may_have_proof = true;
        } else if k == Tk::Case {
            self.advance();
            self.set_expecting("expression");
            end = self.expression()?.loc;
            may_have_proof = true;
        } else {
            // AssertStep
            if self.kind(1) == Tk::Suffices {
                self.advance();
                self.set_expecting("expression or ASSUME/PROVE");
            }
            if matches!(self.kind(1), Tk::Assume | Tk::BoxAssume) {
                end = self.assume_prove()?.loc;
            } else {
                end = self.expression()?.loc;
            }
            may_have_proof = true;
        }
        if self.begins_proof(1) {
            if !may_have_proof {
                return Err(self.custom(&format!("{}: proof of step that does not take a proof.", loc_str(Loc::span(Self::loc_of(&t0), end)))));
            }
            end = self.proof()?;
        }
        self.epa();
        Ok(Loc::span(Self::loc_of(&t0), end))
    }

    /// LOOKAHEAD( <IDENTIFIER> (<COMMA> <IDENTIFIER>)* <IN> | <LAB> )
    fn take_lookahead_bound(&self) -> bool {
        if self.kind(1) == Tk::Lab {
            return true;
        }
        self.lookahead_ident_list_then(Tk::In)
    }

    /// LOOKAHEAD( <IDENTIFIER> (<COMMA> <IDENTIFIER>)* <END> )
    fn lookahead_ident_list_then(&self, end: Tk) -> bool {
        let mut k = 1;
        if self.kind(k) != Tk::Identifier {
            return false;
        }
        k += 1;
        while self.kind(k) == Tk::Comma {
            k += 1;
            if self.kind(k) != Tk::Identifier {
                return false;
            }
            k += 1;
        }
        self.kind(k) == end
    }

    // ---- bounds

    fn identifier_tuple(&mut self) -> PResult<(Vec<Ident>, Loc)> {
        self.bpa("Identifier tuple");
        let t0 = self.expect(Tk::Lab)?;
        self.set_expecting("Identifier or >>");
        let mut ids = Vec::new();
        if self.kind(1) == Tk::Identifier {
            let t = self.advance();
            ids.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
            self.set_expecting("COMMA or >>");
            while self.kind(1) == Tk::Comma {
                self.advance();
                self.set_expecting("COMMA or >>");
                let t = self.expect(Tk::Identifier)?;
                ids.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
                self.set_expecting("COMMA or >>");
            }
        }
        let t1 = self.expect(Tk::Rab)?;
        self.epa();
        Ok((ids, Loc::span(Self::loc_of(&t0), Self::loc_of(&t1))))
    }

    fn quant_bound(&mut self) -> PResult<Bound> {
        self.bpa("Quant Bound");
        let start = Self::loc_of(self.tok(1));
        let (vars, tuple) = if self.kind(1) == Tk::Lab {
            let (ids, _) = self.identifier_tuple()?;
            (ids, true)
        } else {
            let t = self.expect(Tk::Identifier)?;
            let mut ids = vec![Ident { name: t.image.clone(), loc: Self::loc_of(&t) }];
            while self.kind(1) == Tk::Comma {
                self.advance();
                let t = self.expect(Tk::Identifier)?;
                ids.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
                self.set_expecting(", or \\in");
            }
            (ids, false)
        };
        self.expect(Tk::In)?;
        let set = self.expression()?;
        self.epa();
        let loc = Loc::span(start, set.loc);
        Ok(Bound { vars, tuple, set, loc })
    }

    // ---- expressions

    fn mixfix(&self, op: &'static Operator) -> Option<&'static Operator> {
        ops::get_mixfix(op)
    }

    fn os_top(&mut self) -> &mut Vec<OSel> {
        self.os.last_mut().expect("operator stack")
    }

    fn push_on_stack(&mut self, node: SNode, op: Option<&'static Operator>) {
        self.os_top().push(OSel { node, op });
    }

    fn push_expr(&mut self, e: Expr) {
        self.push_on_stack(SNode::Expr(e), None);
    }

    fn pre_in_empty_top(&self) -> bool {
        match self.os.last() {
            None => true,
            Some(v) => match v.last() {
                None => true,
                Some(s) => match s.op {
                    Some(op) => op.is_prefix() || op.is_infix(),
                    None => false,
                },
            },
        }
    }

    fn take_expr(n: SNode) -> Expr {
        match n {
            SNode::Expr(e) => e,
            other => {
                let l = other.loc();
                // an operator node used as an expression (e.g. unreduced): represent it as an identifier
                match other {
                    SNode::Op { name, kind, loc } => Expr::new(
                        loc,
                        ExprKind::Id(GenId {
                            prefix: vec![],
                            name,
                            kind: match kind {
                                SOpKind::GenInfix => IdKind::InfixOp,
                                SOpKind::GenPostfix => IdKind::PostfixOp,
                                _ => IdKind::PrefixOp,
                            },
                            loc,
                        }),
                    ),
                    _ => Expr::new(l, ExprKind::Tuple(vec![])),
                }
            }
        }
    }

    fn reduce_infix(&mut self, op: &'static Operator) {
        let st = self.os_top();
        let n = st.len() as isize - 1;
        if n >= 3 {
            let n = n as usize;
            let right = st.remove(n - 1);
            let opn = st.remove(n - 2); // after removing n-1, index n-2 is op
            let left_idx = n - 3;
            let left = std::mem::replace(&mut st[left_idx], OSel { node: SNode::Void, op: None });
            let (opname, oploc) = match &opn.node {
                SNode::Op { name, loc, .. } => (name.clone(), *loc),
                _ => ("".into(), Loc::default()),
            };
            let l = Self::take_expr(left.node);
            let r = Self::take_expr(right.node);
            let loc = Loc::span(l.loc, r.loc);
            let e = if op.is_nfix() {
                match *l.kind {
                    ExprKind::Times(mut v) => {
                        v.push(r);
                        Expr::new(loc, ExprKind::Times(v))
                    }
                    k => {
                        let l2 = Expr { loc: l.loc, kind: Box::new(k) };
                        Expr::new(loc, ExprKind::Times(vec![l2, r]))
                    }
                }
            } else {
                Expr::new(loc, ExprKind::Infix(Box::new(l), opname, oploc, Box::new(r)))
            };
            st[left_idx] = OSel { node: SNode::Expr(e), op: None };
        }
    }

    fn reduce_prefix(&mut self) {
        let st = self.os_top();
        let n = st.len() as isize - 1;
        if n >= 2 {
            let n = n as usize;
            let operand = st.remove(n - 1);
            let opn = std::mem::replace(&mut st[n - 2], OSel { node: SNode::Void, op: None });
            let (mut opname, oploc) = match &opn.node {
                SNode::Op { name, loc, .. } => (name.clone(), *loc),
                _ => ("".into(), Loc::default()),
            };
            if &*opname == "-" {
                opname = "-.".into();
            }
            let e = Self::take_expr(operand.node);
            let loc = Loc::span(oploc, e.loc);
            st[n - 2] = OSel { node: SNode::Expr(Expr::new(loc, ExprKind::Prefix(opname, oploc, Box::new(e)))), op: None };
        }
    }

    fn reduce_postfix(&mut self) {
        let st = self.os_top();
        let n = st.len() as isize - 1;
        if n >= 2 {
            let n = n as usize;
            let opn = st.remove(n - 1);
            let target = std::mem::replace(&mut st[n - 2], OSel { node: SNode::Void, op: None });
            let e = Self::take_expr(target.node);
            let new = match opn.node {
                SNode::FcnArgs(args, aloc) => {
                    let loc = Loc::span(e.loc, aloc);
                    Expr::new(loc, ExprKind::FcnAppl(Box::new(e), args))
                }
                SNode::Op { name, loc, .. } => {
                    let l = Loc::span(e.loc, loc);
                    Expr::new(l, ExprKind::Postfix(Box::new(e), name, loc))
                }
                _ => e,
            };
            st[n - 2] = OSel { node: SNode::Expr(new), op: None };
        }
    }

    fn loc_s(&self, node: &SNode) -> String {
        loc_str(node.loc())
    }

    /// `OperatorStack.reduceStack`
    fn reduce_stack(&mut self) -> PResult<()> {
        loop {
            let st = self.os.last().expect("stack");
            let n = st.len() as isize - 1;
            if n < 0 {
                return Ok(());
            }
            let n = n as usize;
            let (or, tm0_loc) = match st[n].op {
                None => return Ok(()), // !tm0.isOperator()
                Some(o) => (o, self.loc_s(&st[n].node)),
            };
            let ostr = or.id;
            let before = st.len();
            if or.is_postfix() {
                if n == 0 {
                    return Err(self.custom(&format!("\n  Encountered postfix op {} in block {} on empty stack", ostr, tm0_loc)));
                }
                let tm1 = &st[n - 1];
                if let Some(ol) = tm1.op {
                    if ol.is_infix() || ol.is_prefix() {
                        return Err(self.custom(&format!(
                            "\n  Encountered postfix op {} in block {} following prefix or infix op {}.",
                            ostr, tm0_loc, ol.id
                        )));
                    } else {
                        self.reduce_postfix();
                    }
                } else if n > 1 {
                    let tm2 = &st[n - 2];
                    if let Some(ol) = tm2.op {
                        if Operator::succ(ol, or) {
                            if ol.is_infix() {
                                self.reduce_infix(ol)
                            } else {
                                self.reduce_prefix()
                            }
                        } else if !Operator::prec(ol, or) {
                            return Err(self.custom(&format!(
                                "Precedence conflict between ops {} in block {} and {}.",
                                ol.id, tm0_loc, ostr
                            )));
                        } else {
                            return Ok(());
                        }
                    } else {
                        return Err(self.custom(&format!(
                            "Expression at location {} and expression at location {} follow each other without any intervening operator.",
                            self.loc_s(&tm2.node),
                            self.loc_s(&tm1.node)
                        )));
                    }
                } else {
                    return Ok(());
                }
            } else if or.is_prefix() {
                if n == 0 {
                    return Ok(());
                }
                let tm1 = &st[n - 1];
                if let Some(ol) = tm1.op {
                    if ol.is_postfix() {
                        return Err(self.custom(&format!(
                            "\n  Encountered prefix op {} in block {} following postfix op {}.",
                            ostr, tm0_loc, ol.id
                        )));
                    } else {
                        return Ok(());
                    }
                } else {
                    return Err(self.custom(&format!(
                        "\n  Encountered prefix op {} in block {} following an expression.",
                        ostr, tm0_loc
                    )));
                }
            } else {
                // infix
                if n == 0 {
                    if self.mixfix(or).is_none() {
                        return Err(self.custom(&format!(
                            "\n  Encountered infix op {} in block {} on empty stack.",
                            ostr, tm0_loc
                        )));
                    } else {
                        return Ok(());
                    }
                }
                let tm1 = &st[n - 1];
                if let Some(ol) = tm1.op {
                    if ol.is_infix() || ol.is_prefix() {
                        let mix_r = self.mixfix(or);
                        match mix_r {
                            None => {
                                if std::ptr::eq(or, ops::void_operator()) {
                                    return Err(self.custom(&format!(
                                        "\n  Missing expression in block {} following prefix or infix op {}.",
                                        self.loc_s(&tm1.node),
                                        ol.id
                                    )));
                                } else {
                                    return Err(self.custom(&format!(
                                        "\n  Encountered infix op {} in block {} following prefix or infix op {}.",
                                        ostr,
                                        self.loc_s(&tm1.node),
                                        ol.id
                                    )));
                                }
                            }
                            Some(mr) => {
                                if Operator::succ(ol, mr) || (std::ptr::eq(ol, mr) && ol.assoc_left()) {
                                    return Err(self.custom(&format!(
                                        "\n  Precedence conflict between ops {} in block {} and {}.",
                                        ol.id,
                                        self.loc_s(&tm1.node),
                                        mr.id
                                    )));
                                }
                            }
                        }
                    } else {
                        self.reduce_postfix();
                    }
                } else if n > 1 {
                    let tm2 = &st[n - 2];
                    if let Some(mut ol) = tm2.op {
                        let mix_l = self.mixfix(ol);
                        if let Some(ml) = mix_l {
                            if n == 2 || st[n - 3].op.is_some() {
                                ol = ml;
                            }
                        }
                        if Operator::succ(ol, or) || (std::ptr::eq(ol, or) && ol.assoc_left()) {
                            if ol.is_infix() {
                                self.reduce_infix(ol);
                            } else if ol.is_prefix() {
                                self.reduce_prefix();
                            } else {
                                let l2 = tm2.node.loc();
                                let l1 = tm1.node.loc();
                                if l2.bl < l1.bl && or.id == "=" {
                                    return Err(self.custom(&format!(
                                        "\n  *** Hint *** You may have mistyped ==\n  Illegal combination of operators {} in block {} and {}.",
                                        ol.id,
                                        self.loc_s(&tm2.node),
                                        ostr
                                    )));
                                } else if std::ptr::eq(or, ops::void_operator()) {
                                    return Err(self.custom(&format!(
                                        "\n Error following expression at  {}, missing operator or separator.",
                                        self.loc_s(&tm2.node)
                                    )));
                                } else {
                                    return Err(self.custom(&format!(
                                        "\n  Illegal combination of operators {} in block {} and {}.",
                                        ol.id,
                                        self.loc_s(&tm2.node),
                                        ostr
                                    )));
                                }
                            }
                        } else if !(Operator::prec(ol, or) || (std::ptr::eq(ol, or) && ol.assoc_right())) {
                            return Err(self.custom(&format!(
                                "\n  Precedence conflict between ops {} in block {} and {}.",
                                ol.id,
                                self.loc_s(&tm2.node),
                                ostr
                            )));
                        } else {
                            return Ok(());
                        }
                    } else {
                        return Err(self.custom(&format!(
                            "Expression at location {} and expression at location {} follow each other without any intervening operator.",
                            self.loc_s(&tm2.node),
                            self.loc_s(&tm1.node)
                        )));
                    }
                } else {
                    return Ok(());
                }
            }
            let after = self.os.last().unwrap().len();
            // `while (n != CurrentTop.size()-1)`
            if n == after - 1 {
                let _ = before;
                return Ok(());
            }
        }
    }

    fn final_reduce(&mut self) -> PResult<Expr> {
        self.push_on_stack(SNode::Void, Some(ops::void_operator()));
        self.reduce_stack()?;
        let st = self.os.last_mut().unwrap();
        if st.len() == 2 {
            let n = std::mem::replace(&mut st[0].node, SNode::Void);
            Ok(Self::take_expr(n))
        } else {
            let mut msg = String::from("Couldn't properly parse expression");
            let mut n = 0;
            loop {
                msg.push_str("-- incomplete expression at ");
                msg.push_str(&loc_str(st[n].node.loc()));
                msg.push_str(".\n");
                n += 1;
                if n >= st.len() - 1 {
                    break;
                }
            }
            // PErrors.push(...): reported as a parse error by `parse()`
            Err(ParseError { text: msg })
        }
    }

    fn reduce_record(&mut self, dot_loc: Loc, field: Ident) -> PResult<()> {
        let st = self.os.last_mut().unwrap();
        if st.is_empty() {
            return Err(self.custom(&format!("\n    ``.'' has no left hand side at {}.", loc_str(dot_loc))));
        }
        let mut index = st.len() - 1;
        if st[index].op.is_some() {
            let below_is_op = index >= 1 && st[index - 1].op.is_some();
            if st[index].op.unwrap().is_postfix() && !below_is_op {
                // humour reducePostfix: temporarily add a dummy element
                st.push(OSel { node: SNode::Void, op: None });
                // reduce_postfix works on [.., operand, op, dummy]: operand at n-2, op at n-1
                let n = st.len() - 1;
                let opn = st.remove(n - 1);
                let target = std::mem::replace(&mut st[n - 2], OSel { node: SNode::Void, op: None });
                let e = Self::take_expr(target.node);
                let new = match opn.node {
                    SNode::Op { name, loc, .. } => Expr::new(Loc::span(e.loc, loc), ExprKind::Postfix(Box::new(e), name, loc)),
                    SNode::FcnArgs(args, aloc) => Expr::new(Loc::span(e.loc, aloc), ExprKind::FcnAppl(Box::new(e), args)),
                    _ => e,
                };
                st[n - 2] = OSel { node: SNode::Expr(new), op: None };
                // remove the dummy (it is now the last element)
                st.pop();
                index = st.len() - 1;
            } else {
                let l = st[index].node.loc();
                return Err(self.custom(&format!("\n    ``.'' follows operator {}.", loc_str(l))));
            }
        }
        let left = std::mem::replace(&mut st[index].node, SNode::Void);
        let left = Self::take_expr(left);
        let loc = Loc::span(left.loc, field.loc);
        st[index] = OSel { node: SNode::Expr(Expr::new(loc, ExprKind::Record(Box::new(left), field))), op: None };
        Ok(())
    }

    fn last_op_set(&mut self, image: &str) {
        self.last_op = ops::get_operator(image);
    }

    /// Expression()
    fn expression(&mut self) -> PResult<Expr> {
        self.bpa("Expression");
        self.os.push(Vec::new());
        let r = self.expression_inner();
        self.os.pop();
        let r = r?;
        self.epa();
        Ok(r)
    }

    fn push_leading_op(&mut self) -> PResult<()> {
        // ( LOOKAHEAD(PrefixOpToken() | <op_77>, {above}) (PrefixOp | InfixOp) )*
        loop {
            let k = self.kind(1);
            if (is_prefix_op_tok(k) || k == Tk::Minus) && self.above_tok(1) {
                let t = self.advance();
                self.last_op_set(&t.image);
                let (kind, name) = if k == Tk::Minus {
                    (SOpKind::GenInfix, Arc::<str>::from("-"))
                } else {
                    (SOpKind::GenPrefix, Arc::<str>::from(ops::resolve_synonym(&t.image)))
                };
                let lo = self.last_op;
                self.push_on_stack(SNode::Op { kind, name, loc: Self::loc_of(&t) }, lo);
                if self.os.last().unwrap().len() != 1 {
                    self.reduce_stack()?;
                }
            } else {
                return Ok(());
            }
        }
    }

    fn expression_inner(&mut self) -> PResult<Expr> {
        self.push_leading_op()?;
        let k = self.kind(1);
        if is_open_start(k) && self.above_tok(1) {
            let tn = self.open_expression()?;
            self.push_expr(tn);
        } else if self.above_tok(1) {
            self.extendable_expr()?;
        } else {
            return Err(self.unexpected());
        }
        self.final_reduce()
    }

    fn open_expression(&mut self) -> PResult<Expr> {
        match self.kind(1) {
            Tk::Exists | Tk::Forall => self.some_quant(),
            Tk::TExists | Tk::TForall => self.some_tquant(),
            Tk::If => self.if_then_else(),
            Tk::Case => self.case_expr(),
            Tk::Let => self.let_in(),
            Tk::Choose => self.choose(),
            _ => Err(self.unexpected()),
        }
    }

    fn extendable_expr(&mut self) -> PResult<()> {
        self.bpa("ExtendableExpr");
        // first operand: junctions | parentheses expression | primitive expression
        let k = self.kind(1);
        if (k == Tk::And || k == Tk::Or) && self.pre_in_empty_top() {
            let tn = self.junctions()?;
            self.push_expr(tn);
        } else if matches!(k, Tk::Lbr | Tk::Lbc | Tk::Lsb | Tk::Lab | Tk::Wf | Tk::Sf) {
            let tn = self.parentheses_expression()?;
            match tn {
                SBr::Expr(e) => self.push_expr(e),
                SBr::FcnArgs(..) => return Err(self.unexpected()),
            }
        } else {
            let tn = self.primitive_exp()?;
            self.push_expr(tn);
        }
        // ( postfix op | . field | [ ... ] function application )*
        loop {
            let k = self.kind(1);
            if k.is_postfix() && self.above_tok(1) {
                let t = self.advance();
                self.last_op_set(&t.image);
                let name: Name = ops::resolve_synonym(&t.image).into();
                let lo = self.last_op;
                self.push_on_stack(SNode::Op { kind: SOpKind::GenPostfix, name, loc: Self::loc_of(&t) }, lo);
                if self.os.last().unwrap().len() != 1 {
                    self.reduce_stack()?;
                }
            } else if k == Tk::Dot && self.above_tok(1) {
                let t = self.advance();
                self.field_name_to_ident(1);
                if !(self.kind(1) == Tk::Identifier && self.above_tok(1)) {
                    return Err(self.unexpected());
                }
                let id = self.advance();
                self.reduce_record(Self::loc_of(&t), Ident { name: id.image.clone(), loc: Self::loc_of(&id) })?;
            } else if k == Tk::Lsb && self.above_tok(1) {
                self.set_expecting("function argument");
                let tn = self.s_bracket_cases()?;
                match tn {
                    SBr::FcnArgs(args, loc) => {
                        let fcn = ops::get_operator("[");
                        self.push_on_stack(SNode::FcnArgs(args, loc), fcn);
                        if self.os.last().unwrap().len() != 1 {
                            self.reduce_stack()?;
                        }
                    }
                    SBr::Expr(e) => self.push_expr(e),
                }
            } else {
                break;
            }
        }
        // ( infix op ... | :: label )?
        let k = self.kind(1);
        if k.is_infix() && self.above_tok(1) {
            let t = self.advance();
            self.last_op_set(&t.image);
            let name: Name = ops::resolve_synonym(&t.image).into();
            let lo = self.last_op;
            self.push_on_stack(SNode::Op { kind: SOpKind::GenInfix, name, loc: Self::loc_of(&t) }, lo);
            if self.os.last().unwrap().len() != 1 {
                self.reduce_stack()?;
            }
            self.push_leading_op()?;
            let k = self.kind(1);
            if is_open_start(k) && self.above_tok(1) {
                let tn = self.open_expression()?;
                self.push_expr(tn);
            } else if self.above_tok(1) {
                self.extendable_expr()?;
            } else {
                return Err(self.unexpected());
            }
        } else if k == Tk::ColonColon && self.above_tok(1) {
            let t = self.advance();
            let tn0 = self.os.last().unwrap().last().map(|s| &s.node);
            let lbl = match tn0 {
                Some(SNode::Expr(e)) => self.as_label(e),
                _ => None,
            };
            let lbl = match lbl {
                Some(l) => l,
                None => {
                    return Err(self.custom(&format!("`::' at {} does not follow a label.", loc_str(Self::loc_of(&t)))));
                }
            };
            let lbl_loc = self.os.last().unwrap().last().unwrap().node.loc();
            self.os.last_mut().unwrap().pop();
            let tn2 = self.expression()?;
            // labelDoesNotChangeParse
            let ok = match &*tn2.kind {
                ExprKind::Infix(_, name, ..) | ExprKind::Postfix(_, name, ..) => {
                    let lab_op = ops::get_operator(name);
                    match (self.os.last().and_then(|s| s.last()).and_then(|s| s.op), lab_op) {
                        (Some(stack_op), Some(lo)) => Operator::prec(stack_op, lo),
                        _ => true,
                    }
                }
                _ => true,
            };
            if !ok {
                return Err(self.custom(&format!(
                    "Removing label at {} would change expression parsing.",
                    loc_str(lbl_loc)
                )));
            }
            let loc = Loc::span(lbl_loc, tn2.loc);
            self.push_expr(Expr::new(loc, ExprKind::Label(lbl, Box::new(tn2))));
        }
        self.epa();
        Ok(())
    }

    /// `isLabel`: an identifier, or an operator application all of whose arguments are plain identifiers
    fn as_label(&self, e: &Expr) -> Option<GenIdLabel> {
        match &*e.kind {
            ExprKind::Id(g) if g.prefix.is_empty() && g.kind == IdKind::Ident => {
                Some(GenIdLabel { name: Ident { name: g.name.clone(), loc: g.loc }, params: vec![] })
            }
            ExprKind::Appl(g, args) if g.prefix.is_empty() => {
                let mut params = vec![];
                for a in args {
                    match &*a.kind {
                        ExprKind::Id(ga) if ga.prefix.is_empty() => params.push(Ident { name: ga.name.clone(), loc: ga.loc }),
                        _ => return None,
                    }
                }
                Some(GenIdLabel { name: Ident { name: g.name.clone(), loc: g.loc }, params })
            }
            _ => None,
        }
    }

    // ---- junction lists

    fn junctions(&mut self) -> PResult<Expr> {
        let t = self.tok(1).clone();
        let start_idx = self.pos;
        self.jl.push((t.kind, t.bc));
        self.bpa("AND-OR Junction");
        let is_conj = t.kind == Tk::And;
        let mut items = vec![self.junc_item()?];
        loop {
            let t = self.tok(1);
            if self.is_new_bullet(t.bc, t.kind) {
                items.push(self.junc_item()?);
            } else {
                break;
            }
        }
        self.jl.pop();
        self.jl_ranges.push((start_idx, self.pos));
        self.epa();
        let loc = Loc::span(Self::loc_of(&t), items.last().unwrap().loc);
        Ok(Expr::new(loc, if is_conj { ExprKind::Conj(items) } else { ExprKind::Disj(items) }))
    }

    fn junc_item(&mut self) -> PResult<Expr> {
        self.bpa("Junction Item");
        let bullet = self.advance();
        let expr_start = self.pos;
        let e = self.expression()?;
        self.epa();
        // checkIndentation: every token of the item (except nested junction lists) must be right of the bullet column
        let col = self.jl.last().map(|x| x.1).unwrap_or(0);
        let ranges: Vec<(usize, usize)> = self.jl_ranges.iter().filter(|(s, _)| *s >= expr_start).cloned().collect();
        for i in expr_start..self.pos {
            if ranges.iter().any(|(s, en)| i >= *s && i < *en) {
                continue;
            }
            let t = &self.toks[i];
            if t.kind == Tk::DefBreak {
                continue;
            }
            if t.bc <= col {
                return Err(self.custom(&format!(
                    "Item at {} is not properly indented inside conjunction or  disjunction list item at {}",
                    loc_str(Self::loc_of(t)),
                    loc_str(Loc::span(Self::loc_of(&bullet), e.loc))
                )));
            }
        }
        // drop the nested ranges now accounted for
        self.jl_ranges.retain(|(s, _)| *s < expr_start);
        Ok(e)
    }

    // ---- primitive expressions

    fn string_literal(&mut self) -> PResult<Expr> {
        let t = self.expect(Tk::StringLiteral)?;
        let s = reduce_string(&t.image);
        Ok(Expr::new(Self::loc_of(&t), ExprKind::Str(s.into())))
    }

    fn number(&mut self) -> PResult<Expr> {
        let t1 = self.expect(Tk::NumberLiteral)?;
        if self.kind(1) == Tk::Dot && self.kind(2) == Tk::NumberLiteral {
            self.advance();
            let t2 = self.advance();
            Ok(Expr::new(Loc::span(Self::loc_of(&t1), Self::loc_of(&t2)), ExprKind::Real(t1.image.clone(), t2.image.clone())))
        } else {
            Ok(Expr::new(Self::loc_of(&t1), ExprKind::Num(t1.image.clone())))
        }
    }

    fn op_args(&mut self) -> PResult<(Vec<Expr>, Loc)> {
        self.bpa("Optional Arguments");
        let t0 = self.expect(Tk::Lbr)?;
        let mut args = vec![self.op_or_expr()?];
        while self.kind(1) == Tk::Comma {
            self.advance();
            args.push(self.op_or_expr()?);
        }
        let t1 = self.expect(Tk::Rbr)?;
        self.epa();
        Ok((args, Loc::span(Self::loc_of(&t0), Self::loc_of(&t1))))
    }

    /// OpOrExpr
    fn op_or_expr(&mut self) -> PResult<Expr> {
        let k1 = self.kind(1);
        let k2 = self.kind(2);
        let op_like = is_ne_prefix_op_tok(k1) || k1.is_infix() || k1.is_postfix();
        let stop2 = matches!(
            k2,
            Tk::Comma
                | Tk::Rbr
                | Tk::DefBreak
                | Tk::Local
                | Tk::Instance
                | Tk::Theorem
                | Tk::Assume
                | Tk::EndModule
                | Tk::Separator
                | Tk::BeginModule
                | Tk::Assumption
                | Tk::Constant
                | Tk::Variable
                | Tk::Recursive
        );
        if op_like && stop2 && self.above_tok(1) {
            let t = self.advance();
            let name: Name = ops::resolve_synonym(&t.image).into();
            let kind = if k1.is_postfix() {
                IdKind::PostfixOp
            } else if k1.is_infix() {
                IdKind::InfixOp
            } else {
                IdKind::PrefixOp
            };
            if k1.is_infix() && matches!(&*t.image, "\\X" | "\\times") {
                return Err(self.custom(&format!("{}: \\X may not be used as an infix operator.", loc_str(Self::loc_of(&t)))));
            }
            let loc = Self::loc_of(&t);
            return Ok(Expr::new(loc, ExprKind::Id(GenId { prefix: vec![], name, kind, loc })));
        }
        if k1 == Tk::Lambda && self.above_tok(1) {
            return self.lambda();
        }
        self.expression()
    }

    fn lambda(&mut self) -> PResult<Expr> {
        self.bpa("Lambda");
        let t0 = self.expect(Tk::Lambda)?;
        self.set_expecting("Identifier");
        let t = self.expect(Tk::Identifier)?;
        let mut params = vec![Ident { name: t.image.clone(), loc: Self::loc_of(&t) }];
        self.set_expecting("`,' or `:'");
        while self.kind(1) == Tk::Comma {
            self.advance();
            self.set_expecting("Identifier");
            let t = self.expect(Tk::Identifier)?;
            params.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
            self.set_expecting("`,' or `:'");
        }
        self.expect(Tk::Colon)?;
        self.set_expecting("Expression");
        let e = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), e.loc);
        Ok(Expr::new(loc, ExprKind::Lambda(params, Box::new(e))))
    }

    fn primitive_exp(&mut self) -> PResult<Expr> {
        self.bpa("Primitive expression");
        let k = self.kind(1);
        if k == Tk::StringLiteral && self.above_tok(1) {
            let e = self.string_literal()?;
            self.epa();
            return Ok(e);
        }
        if k == Tk::NumberLiteral && self.above_tok(1) {
            let e = self.number()?;
            self.epa();
            return Ok(e);
        }
        // head
        let (name0, kind0, loc0): (Name, IdKind, Loc) = match k {
            Tk::Identifier => {
                let t = self.advance();
                (t.image.clone(), IdKind::Ident, Self::loc_of(&t))
            }
            Tk::ProofStepLexeme | Tk::ProofImplicitStepLexeme => {
                let t = self.advance();
                let l = Self::loc_of(&t);
                if self.proof_level() < 0 && self.proof_depth <= 0 {
                    return Err(self.custom(&format!("{}: Step number used outside proof.", loc_str(l))));
                }
                if t.image.chars().nth(1) == Some('+') {
                    return Err(self.custom(&format!("{}: <+> step number used in an expression.", loc_str(l))));
                }
                (t.image.clone(), IdKind::Ident, l)
            }
            Tk::MinusDot => {
                let t = self.advance();
                self.last_op_set(&t.image);
                (ops::resolve_synonym(&t.image).into(), IdKind::PrefixOp, Self::loc_of(&t))
            }
            _ if k.is_infix() => {
                let t = self.advance();
                self.last_op_set(&t.image);
                (ops::resolve_synonym(&t.image).into(), IdKind::InfixOp, Self::loc_of(&t))
            }
            _ if k.is_postfix() => {
                let t = self.advance();
                self.last_op_set(&t.image);
                (ops::resolve_synonym(&t.image).into(), IdKind::PostfixOp, Self::loc_of(&t))
            }
            _ => return Err(self.unexpected()),
        };
        let mut elem_args: Option<Vec<Expr>> = None;
        let mut end = loc0;
        if self.kind(1) == Tk::Lbr && self.lookahead_op_args_2() {
            let (a, l) = self.op_args()?;
            elem_args = Some(a);
            end = l;
        }
        // BangExt*
        let mut bangs: Vec<(Name, IdKind, Loc, Option<Vec<Expr>>)> = Vec::new();
        let mut bang_opargs_only: Option<(Vec<Expr>, Loc)> = None;
        while self.kind(1) == Tk::Bang {
            self.bpa("Bang Extension");
            let bt = self.advance();
            let k = self.kind(1);
            let (nm, ik, nl): (Name, IdKind, Loc);
            if k == Tk::Identifier && &*self.tok(1).image != "@" {
                let t = self.advance();
                nm = t.image.clone();
                ik = IdKind::Ident;
                nl = Self::loc_of(&t);
            } else if is_ne_prefix_op_tok(k) {
                let t = self.advance();
                nm = ops::resolve_synonym(&t.image).into();
                ik = IdKind::PrefixOp;
                nl = Self::loc_of(&t);
            } else if k.is_infix() {
                let t = self.advance();
                nm = ops::resolve_synonym(&t.image).into();
                ik = IdKind::InfixOp;
                nl = Self::loc_of(&t);
            } else if k.is_postfix() {
                let t = self.advance();
                nm = ops::resolve_synonym(&t.image).into();
                ik = IdKind::PostfixOp;
                nl = Self::loc_of(&t);
            } else if k == Tk::Lbr {
                let (a, l) = self.op_args()?;
                bang_opargs_only = Some((a, l));
                self.epa();
                end = Loc::span(Self::loc_of(&bt), l);
                bangs.push(("".into(), IdKind::Ident, l, None));
                continue;
            } else if matches!(k, Tk::Lab | Tk::Rab | Tk::Colon | Tk::NumberLiteral)
                || (k == Tk::Identifier && &*self.tok(1).image == "@")
            {
                let t = self.advance();
                nm = t.image.clone();
                ik = IdKind::Ident;
                nl = Self::loc_of(&t);
            } else {
                return Err(self.unexpected());
            }
            let mut a = None;
            let mut e = nl;
            if self.kind(1) == Tk::Lbr && self.lookahead_op_args_2() {
                let (aa, l) = self.op_args()?;
                a = Some(aa);
                e = l;
            }
            end = Loc::span(Self::loc_of(&bt), e);
            bangs.push((nm, ik, nl, a));
            self.epa();
        }
        let _ = bang_opargs_only;
        let whole = Loc::span(loc0, end);
        let result = if bangs.is_empty() {
            let g = GenId { prefix: vec![], name: name0, kind: kind0, loc: loc0 };
            match elem_args {
                None => Expr::new(loc0, ExprKind::Id(g)),
                Some(a) => Expr::new(whole, ExprKind::Appl(g, a)),
            }
        } else {
            let mut prefix = vec![PrefixElem { name: name0, kind: kind0, args: elem_args, loc: loc0 }];
            let n = bangs.len();
            for (i, (nm, ik, nl, a)) in bangs.into_iter().enumerate() {
                if i + 1 < n {
                    prefix.push(PrefixElem { name: nm, kind: ik, args: a, loc: nl });
                } else {
                    let g = GenId { prefix, name: nm, kind: ik, loc: Loc::span(loc0, nl) };
                    prefix = vec![];
                    let e = match a {
                        None => Expr::new(Loc::span(loc0, nl), ExprKind::Id(g)),
                        Some(args) => Expr::new(whole, ExprKind::Appl(g, args)),
                    };
                    self.epa();
                    return Ok(e);
                }
            }
            unreachable!()
        };
        self.epa();
        Ok(result)
    }

    /// LOOKAHEAD(2) for OpArgs: `(` followed by a token that can begin an operator-or-expression
    fn lookahead_op_args_2(&self) -> bool {
        let k2 = self.kind(2);
        k2 != Tk::Rbr && (self.can_start_expression(k2) || k2 == Tk::Lambda || is_ne_prefix_op_tok(k2))
    }

    // ---- ( ) { } [ ] << >> WF/SF

    fn parentheses_expression(&mut self) -> PResult<SBr> {
        match self.kind(1) {
            Tk::Lbr => {
                let t0 = self.advance();
                let e = self.expression()?;
                let t1 = self.expect(Tk::Rbr)?;
                Ok(SBr::Expr(Expr::new(Loc::span(Self::loc_of(&t0), Self::loc_of(&t1)), ExprKind::Paren(Box::new(e)))))
            }
            Tk::Lbc => Ok(SBr::Expr(self.brace_cases()?)),
            Tk::Lsb => self.s_bracket_cases(),
            Tk::Lab => Ok(SBr::Expr(self.tuple_or_action()?)),
            Tk::Wf | Tk::Sf => Ok(SBr::Expr(self.fairness_expr()?)),
            _ => Err(self.unexpected()),
        }
    }

    /// `matchFcnConst()`: after `{` or `[` : `<< ... >> \in` or `Id [, Id]* \in`
    fn match_fcn_const(&self) -> bool {
        // the opening bracket is the previously consumed token; look at tokens from kind(1)
        let mut k = 1;
        if self.kind(k) == Tk::Lab {
            let mut count = 1;
            while count != 0 {
                k += 1;
                let kk = self.kind(k);
                if kk == Tk::Lab {
                    count += 1;
                }
                if kk == Tk::Rab {
                    count -= 1;
                }
                if kk == Tk::Eof {
                    return false;
                }
            }
            self.kind(k + 1) == Tk::In
        } else if self.kind(k) == Tk::Identifier {
            k += 1;
            while self.kind(k) == Tk::Comma {
                k += 1;
                if self.kind(k) != Tk::Identifier {
                    return false;
                }
                k += 1;
            }
            self.kind(k) == Tk::In
        } else {
            false
        }
    }

    fn brace_cases(&mut self) -> PResult<Expr> {
        self.bpa("Some { } form");
        let t0 = self.expect(Tk::Lbc)?;
        let start = Self::loc_of(&t0);
        let result: ExprKind;
        if self.match_fcn_const() {
            // ( IdentifierTuple | Identifier ) \in Expression ...
            let bv: BoundVar = if self.kind(1) == Tk::Lab {
                let (ids, l) = self.identifier_tuple()?;
                BoundVar::Tuple(ids, l)
            } else {
                let t = self.advance();
                BoundVar::One(Ident { name: t.image.clone(), loc: Self::loc_of(&t) })
            };
            self.set_expecting("\\in");
            self.expect(Tk::In)?;
            let in_tok = self.toks[self.pos - 1].clone();
            let tn2 = self.expression()?;
            self.set_expecting("':', ',' or '}'");
            if self.kind(1) == Tk::Colon {
                self.advance();
                let p = self.expression()?;
                result = ExprKind::SubsetOf(bv, Box::new(tn2), Box::new(p));
            } else {
                // the infix expression `x \in S`
                let (vloc, vexpr) = match &bv {
                    BoundVar::One(id) => (
                        id.loc,
                        Expr::new(id.loc, ExprKind::Id(GenId { prefix: vec![], name: id.name.clone(), kind: IdKind::Ident, loc: id.loc })),
                    ),
                    BoundVar::Tuple(ids, l) => (
                        *l,
                        Expr::new(
                            *l,
                            ExprKind::Tuple(
                                ids.iter()
                                    .map(|id| {
                                        Expr::new(
                                            id.loc,
                                            ExprKind::Id(GenId { prefix: vec![], name: id.name.clone(), kind: IdKind::Ident, loc: id.loc }),
                                        )
                                    })
                                    .collect(),
                            ),
                        ),
                    ),
                };
                let _ = vloc;
                let loc = Loc::span(vexpr.loc, tn2.loc);
                let first = Expr::new(
                    loc,
                    ExprKind::Infix(Box::new(vexpr), "\\in".into(), Self::loc_of(&in_tok), Box::new(tn2)),
                );
                let mut elems = vec![first];
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    elems.push(self.expression()?);
                }
                result = ExprKind::SetEnum(elems);
            }
        } else if self.kind(1) == Tk::Rbc {
            result = ExprKind::SetEnum(vec![]);
        } else if self.lookahead_ident_or_tuple_then(Tk::Comma) {
            let mut elems = vec![self.expression()?];
            while self.kind(1) == Tk::Comma {
                self.advance();
                elems.push(self.expression()?);
            }
            result = ExprKind::SetEnum(elems);
        } else if self.lookahead_ident_or_tuple_then(Tk::Colon) {
            let e = self.expression()?;
            self.expect(Tk::Colon)?;
            let mut bs = vec![self.quant_bound()?];
            while self.kind(1) == Tk::Comma {
                self.advance();
                bs.push(self.quant_bound()?);
            }
            result = ExprKind::SetOfAll(Box::new(e), bs);
        } else {
            let tn = self.expression()?;
            if self.kind(1) == Tk::Colon {
                let ct = self.advance();
                // Java rejects `{a \in b : c \in d}` here
                if let ExprKind::Infix(_, name, ..) = &*tn.kind {
                    if &**name == "\\in" {
                        return Err(self.custom(&format!("Form {{a \\in b : c \\in d }}, at line {}, is not allowed", ct.bl)));
                    }
                }
                let mut bs = vec![self.quant_bound()?];
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    bs.push(self.quant_bound()?);
                }
                result = ExprKind::SetOfAll(Box::new(tn), bs);
            } else if self.kind(1) == Tk::Comma {
                let mut elems = vec![tn];
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    elems.push(self.expression()?);
                }
                result = ExprKind::SetEnum(elems);
            } else {
                result = ExprKind::SetEnum(vec![tn]);
            }
        }
        let t1 = self.expect(Tk::Rbc)?;
        self.epa();
        Ok(Expr::new(Loc::span(start, Self::loc_of(&t1)), result))
    }

    /// LOOKAHEAD( ( IdentifierTuple() | <IDENTIFIER>) <END> )
    fn lookahead_ident_or_tuple_then(&self, end: Tk) -> bool {
        let mut k = 1;
        if self.kind(k) == Tk::Lab {
            // IdentifierTuple: << [Id (, Id)*] >>
            k += 1;
            if self.kind(k) == Tk::Identifier {
                k += 1;
                while self.kind(k) == Tk::Comma {
                    k += 1;
                    if self.kind(k) != Tk::Identifier {
                        return false;
                    }
                    k += 1;
                }
            }
            if self.kind(k) != Tk::Rab {
                return false;
            }
            k += 1;
        } else if self.kind(k) == Tk::Identifier {
            k += 1;
        } else {
            return false;
        }
        self.kind(k) == end
    }

    fn s_bracket_cases(&mut self) -> PResult<SBr> {
        self.bpa("Some [] Form");
        let t0 = self.expect(Tk::Lsb)?;
        let start = Self::loc_of(&t0);
        let r: SBr;
        if self.match_fcn_const() {
            let mut bs = vec![self.quant_bound()?];
            while self.kind(1) == Tk::Comma {
                self.advance();
                bs.push(self.quant_bound()?);
            }
            self.expect(Tk::MapTo)?;
            let e = self.expression()?;
            let t1 = self.expect(Tk::Rsb)?;
            r = SBr::Expr(Expr::new(Loc::span(start, Self::loc_of(&t1)), ExprKind::FcnConst(bs, Box::new(e))));
        } else if (self.kind(1) == Tk::Identifier && self.kind(2) == Tk::MapTo)
            || (self.kind(2) == Tk::MapTo && self.is_field_name(self.kind(1), self.pos))
        {
            self.field_name_to_ident(1);
            let mut fields = vec![self.field_val()?];
            while self.kind(1) == Tk::Comma {
                self.advance();
                fields.push(self.field_val()?);
            }
            let t1 = self.expect(Tk::Rsb)?;
            r = SBr::Expr(Expr::new(Loc::span(start, Self::loc_of(&t1)), ExprKind::RcdCons(fields)));
        } else if self.kind(1) == Tk::Identifier && self.kind(2) == Tk::Colon {
            let mut fields = vec![self.field_set()?];
            while self.kind(1) == Tk::Comma {
                self.advance();
                fields.push(self.field_set()?);
            }
            let t1 = self.expect(Tk::Rsb)?;
            r = SBr::Expr(Expr::new(Loc::span(start, Self::loc_of(&t1)), ExprKind::SetOfRcds(fields)));
        } else {
            let e = self.expression()?;
            match self.kind(1) {
                Tk::Comma | Tk::Rsb => {
                    let mut args = vec![e];
                    while self.kind(1) == Tk::Comma {
                        self.advance();
                        args.push(self.expression()?);
                    }
                    let t1 = self.expect(Tk::Rsb)?;
                    r = SBr::FcnArgs(args, Loc::span(start, Self::loc_of(&t1)));
                }
                Tk::Arrow => {
                    self.advance();
                    let b = self.expression()?;
                    let t1 = self.expect(Tk::Rsb)?;
                    r = SBr::Expr(Expr::new(Loc::span(start, Self::loc_of(&t1)), ExprKind::SetOfFcns(Box::new(e), Box::new(b))));
                }
                Tk::Except => {
                    self.advance();
                    let mut specs = vec![self.except_spec()?];
                    while self.kind(1) == Tk::Comma {
                        self.advance();
                        specs.push(self.except_spec()?);
                    }
                    let t1 = self.expect(Tk::Rsb)?;
                    r = SBr::Expr(Expr::new(Loc::span(start, Self::loc_of(&t1)), ExprKind::Except(Box::new(e), specs)));
                }
                Tk::Arsb => {
                    self.advance();
                    let sub = self.reduced_expression()?;
                    let loc = Loc::span(start, sub.loc);
                    r = SBr::Expr(Expr::new(loc, ExprKind::ActionExpr { boxed: true, act: Box::new(e), sub: Box::new(sub) }));
                }
                _ => return Err(self.unexpected()),
            }
        }
        self.epa();
        Ok(r)
    }

    fn field_val(&mut self) -> PResult<(Ident, Expr)> {
        self.bpa("Field Value");
        let t = self.expect(Tk::Identifier)?;
        self.expect(Tk::MapTo)?;
        let e = self.expression()?;
        self.epa();
        Ok((Ident { name: t.image.clone(), loc: Self::loc_of(&t) }, e))
    }

    fn field_set(&mut self) -> PResult<(Ident, Expr)> {
        self.bpa("Field Set");
        let t = self.expect(Tk::Identifier)?;
        self.expect(Tk::Colon)?;
        let e = self.expression()?;
        self.epa();
        Ok((Ident { name: t.image.clone(), loc: Self::loc_of(&t) }, e))
    }

    fn except_spec(&mut self) -> PResult<ExceptSpec> {
        self.bpa("Except Spec");
        let t0 = self.expect(Tk::Bang)?;
        let mut path = Vec::new();
        loop {
            self.bpa("Except Component");
            if self.kind(1) == Tk::Dot {
                self.advance();
                self.field_name_to_ident(1);
                let t = self.expect(Tk::Identifier)?;
                if &*t.image == "@" {
                    return Err(ParseError { text: "@ used in !.@".into() });
                }
                path.push(ExceptComp::Field(Ident { name: t.image.clone(), loc: Self::loc_of(&t) }));
            } else if self.kind(1) == Tk::Lsb {
                self.advance();
                let mut idx = vec![self.expression()?];
                while self.kind(1) == Tk::Comma {
                    self.advance();
                    idx.push(self.expression()?);
                }
                self.expect(Tk::Rsb)?;
                path.push(ExceptComp::Index(idx));
            } else {
                return Err(self.unexpected());
            }
            self.epa();
            self.set_expecting("= or ,");
            if !matches!(self.kind(1), Tk::Dot | Tk::Lsb) {
                break;
            }
        }
        self.expect(Tk::Equals)?;
        let val = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), val.loc);
        Ok(ExceptSpec { path, val, loc })
    }

    fn tuple_or_action(&mut self) -> PResult<Expr> {
        self.bpa("Some << -- >> or >>_ Form");
        let t0 = self.expect(Tk::Lab)?;
        let start = Self::loc_of(&t0);
        let mut elems = Vec::new();
        if !matches!(self.kind(1), Tk::Rab | Tk::Arab) {
            elems.push(self.expression()?);
            while self.kind(1) == Tk::Comma {
                self.advance();
                elems.push(self.expression()?);
            }
        }
        let r = match self.kind(1) {
            Tk::Rab => {
                let t1 = self.advance();
                Expr::new(Loc::span(start, Self::loc_of(&t1)), ExprKind::Tuple(elems))
            }
            Tk::Arab => {
                self.advance();
                let sub = self.reduced_expression()?;
                // the action is the (single) expression inside <<...>>
                let loc = Loc::span(start, sub.loc);
                let act = if elems.len() == 1 {
                    elems.pop().unwrap()
                } else {
                    return Err(self.unexpected());
                };
                Expr::new(loc, ExprKind::ActionExpr { boxed: false, act: Box::new(act), sub: Box::new(sub) })
            }
            _ => return Err(self.unexpected()),
        };
        self.epa();
        Ok(r)
    }

    /// ReducedExpression: the subscript after `]_` / `>>_` / `WF_`
    fn reduced_expression(&mut self) -> PResult<Expr> {
        self.bpa("restricted form of expression");
        let r = match self.kind(1) {
            Tk::Identifier => self.no_op_extension()?,
            Tk::Lbr => {
                let t0 = self.advance();
                let e = self.expression()?;
                let t1 = self.expect(Tk::Rbr)?;
                Expr::new(Loc::span(Self::loc_of(&t0), Self::loc_of(&t1)), ExprKind::Paren(Box::new(e)))
            }
            Tk::Lbc => self.brace_cases()?,
            Tk::Lsb => match self.s_bracket_cases()? {
                SBr::Expr(e) => e,
                SBr::FcnArgs(..) => return Err(self.unexpected()),
            },
            Tk::Lab => self.tuple_or_action()?,
            _ => return Err(self.unexpected()),
        };
        self.epa();
        Ok(r)
    }

    /// NoOpExtension: `Id [OpArgs] [! NoOpExtension]`  (sets `fairness_hook`)
    fn no_op_extension(&mut self) -> PResult<Expr> {
        let mut prefix: Vec<PrefixElem> = Vec::new();
        loop {
            let tid = self.expect(Tk::Identifier)?;
            let mut top: Option<Vec<Expr>> = None;
            if self.kind(1) == Tk::Lbr && self.lookahead_op_args_2() {
                top = Some(self.op_args()?.0);
            }
            if self.kind(1) == Tk::Bang {
                self.advance();
                prefix.push(PrefixElem { name: tid.image.clone(), kind: IdKind::Ident, args: top, loc: Self::loc_of(&tid) });
                continue;
            }
            self.fairness_hook = top;
            let loc = Loc::span(prefix.first().map(|p| p.loc).unwrap_or(Self::loc_of(&tid)), Self::loc_of(&tid));
            return Ok(Expr::new(
                loc,
                ExprKind::Id(GenId { prefix, name: tid.image.clone(), kind: IdKind::Ident, loc }),
            ));
        }
    }

    fn fairness_expr(&mut self) -> PResult<Expr> {
        self.bpa("Fairness Expression");
        self.fairness_hook = None;
        let t0 = self.advance();
        let strong = t0.kind == Tk::Sf;
        let sub = self.reduced_expression()?;
        let hook = self.fairness_hook.take();
        if self.kind(1) == Tk::Lbr && self.lookahead_op_args_2() {
            // extra parenthesized action
            self.advance();
            let act = self.expression()?;
            let t1 = self.expect(Tk::Rbr)?;
            let sub2 = match (&*sub.kind, hook) {
                (ExprKind::Id(g), Some(h)) => Expr::new(sub.loc, ExprKind::Appl(g.clone(), h)),
                _ => sub,
            };
            self.epa();
            let loc = Loc::span(Self::loc_of(&t0), Self::loc_of(&t1));
            return Ok(Expr::new(loc, ExprKind::Fairness { strong, sub: Box::new(sub2), act: Box::new(act) }));
        }
        // no extra (): the parameter list captured by NoOpExtension is the action
        match hook {
            Some(mut h) if h.len() == 1 => {
                let act = h.pop().unwrap();
                self.epa();
                let loc = Loc::span(Self::loc_of(&t0), act.loc);
                let loc = Loc { el: loc.el, ec: loc.ec + 1, ..loc };
                Ok(Expr::new(loc, ExprKind::Fairness { strong, sub: Box::new(sub), act: Box::new(act) }))
            }
            _ => Err(self.custom(&format!(
                "Ill-structured fairness expression at line {}, column {}",
                t0.bl, t0.bc
            ))),
        }
    }

    // ---- IF / CASE / LET / quantifiers / CHOOSE

    fn if_then_else(&mut self) -> PResult<Expr> {
        self.bpa("IF THEN ELSE");
        let t0 = self.expect(Tk::If)?;
        let c = self.expression()?;
        self.expect(Tk::Then)?;
        let a = self.expression()?;
        self.expect(Tk::Else)?;
        let b = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), b.loc);
        Ok(Expr::new(loc, ExprKind::If(Box::new(c), Box::new(a), Box::new(b))))
    }

    fn case_sep(&self) -> bool {
        self.kind(1) == Tk::CaseSep && self.above_tok(1)
    }

    fn case_expr(&mut self) -> PResult<Expr> {
        self.bpa("CASE Expression");
        let t0 = self.expect(Tk::Case)?;
        let mut arms = vec![self.case_arm()?];
        while self.case_sep() && self.kind(2) != Tk::Other {
            self.advance();
            arms.push(self.case_arm()?);
        }
        let mut other = None;
        let mut end = arms.last().unwrap().1.loc;
        if self.case_sep() {
            self.advance();
            self.bpa("Case Other Arm");
            self.expect(Tk::Other)?;
            self.expect(Tk::Arrow)?;
            let e = self.expression()?;
            self.epa();
            end = e.loc;
            other = Some(Box::new(e));
        }
        self.epa();
        Ok(Expr::new(Loc::span(Self::loc_of(&t0), end), ExprKind::Case(arms, other)))
    }

    fn case_arm(&mut self) -> PResult<(Expr, Expr)> {
        self.bpa("Case Arm");
        let c = self.expression()?;
        self.expect(Tk::Arrow)?;
        let e = self.expression()?;
        self.epa();
        Ok((c, e))
    }

    fn let_in(&mut self) -> PResult<Expr> {
        self.bpa("Case Other Arm");
        let t0 = self.expect(Tk::Let)?;
        self.bpa("Let Definitions");
        let mut items = Vec::new();
        loop {
            let k = self.kind(1);
            if k == Tk::DefBreak || (k == Tk::Local && self.kind(2) == Tk::DefBreak) {
                items.push(LetItem::Def(Box::new(self.op_or_function_definition()?)));
            } else if k == Tk::Recursive {
                let (d, l) = self.recursive()?;
                items.push(LetItem::Recursive(d, l));
            } else {
                break;
            }
        }
        if items.is_empty() {
            return Err(self.unexpected());
        }
        self.epa();
        self.expect(Tk::LetIn)?;
        let body = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), body.loc);
        Ok(Expr::new(loc, ExprKind::LetIn(items, Box::new(body))))
    }

    fn some_quant(&mut self) -> PResult<Expr> {
        self.bpa("Quantified form");
        let t0 = self.advance();
        let forall = t0.kind == Tk::Forall;
        let binds;
        if self.lookahead_ident_list_then(Tk::Colon) {
            let mut ids = Vec::new();
            let t = self.advance();
            ids.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
            while self.kind(1) == Tk::Comma {
                self.advance();
                let t = self.expect(Tk::Identifier)?;
                ids.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
            }
            binds = QBinds::Unbound(ids);
        } else {
            let mut bs = vec![self.quant_bound()?];
            while self.kind(1) == Tk::Comma {
                self.advance();
                bs.push(self.quant_bound()?);
            }
            binds = QBinds::Bound(bs);
        }
        self.expect(Tk::Colon)?;
        let body = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), body.loc);
        Ok(Expr::new(loc, ExprKind::Quant { forall, temporal: false, binds, body: Box::new(body) }))
    }

    fn some_tquant(&mut self) -> PResult<Expr> {
        self.bpa("Bound Quantified Expression");
        let t0 = self.advance();
        let forall = t0.kind == Tk::TForall;
        let t = self.expect(Tk::Identifier)?;
        let mut ids = vec![Ident { name: t.image.clone(), loc: Self::loc_of(&t) }];
        while self.kind(1) == Tk::Comma {
            self.advance();
            let t = self.expect(Tk::Identifier)?;
            ids.push(Ident { name: t.image.clone(), loc: Self::loc_of(&t) });
        }
        self.expect(Tk::Colon)?;
        let body = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), body.loc);
        Ok(Expr::new(loc, ExprKind::Quant { forall, temporal: true, binds: QBinds::Unbound(ids), body: Box::new(body) }))
    }

    fn choose(&mut self) -> PResult<Expr> {
        self.bpa("(Un)Bounded Choose");
        let t0 = self.expect(Tk::Choose)?;
        let var = if self.kind(1) == Tk::Lab {
            let (ids, l) = self.identifier_tuple()?;
            BoundVar::Tuple(ids, l)
        } else {
            let t = self.expect(Tk::Identifier)?;
            BoundVar::One(Ident { name: t.image.clone(), loc: Self::loc_of(&t) })
        };
        // MaybeBound
        let set = if self.kind(1) == Tk::In {
            self.advance();
            self.set_expecting("Expression");
            Some(Box::new(self.expression()?))
        } else {
            None
        };
        self.expect(Tk::Colon)?;
        let body = self.expression()?;
        self.epa();
        let loc = Loc::span(Self::loc_of(&t0), body.loc);
        Ok(Expr::new(loc, ExprKind::Choose { var, set, body: Box::new(body) }))
    }
}

enum SBr {
    Expr(Expr),
    FcnArgs(Vec<Expr>, Loc),
}

/// `reduceString`: strip the quotes and process the escapes
fn reduce_string(image: &str) -> String {
    let inner: Vec<char> = image.chars().collect();
    let inner = &inner[1..inner.len() - 1];
    let mut out = String::new();
    let mut i = 0;
    while i < inner.len() {
        if inner[i] == '\\' && i + 1 < inner.len() {
            i += 1;
            match inner[i] {
                '\\' => out.push('\\'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                'f' => out.push('\u{c}'),
                't' => out.push('\t'),
                '"' => out.push('"'),
                _ => {}
            }
        } else {
            out.push(inner[i]);
        }
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(src: &str) -> Result<ParsedModule, ParseError> {
        parse_source(src)
    }

    #[test]
    fn parses_simple_spec() {
        let m = p("---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_x\n====\n").unwrap();
        assert_eq!(&*m.module.name, "M");
        assert_eq!(m.deps.len(), 1);
        assert_eq!(m.module.units.len(), 4);
    }

    #[test]
    fn junction_lists() {
        let m = p("---- MODULE M ----\nA == /\\ x = 1\n     /\\ \\/ y = 2\n        \\/ y = 3\n     /\\ z = 4\nB == 1\n====\n").unwrap();
        match &m.module.units[0] {
            Unit::OpDef(d) => match &d.body {
                DefBody::Expr(e) => match &*e.kind {
                    ExprKind::Conj(items) => assert_eq!(items.len(), 3),
                    k => panic!("{:?}", k),
                },
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn precedence() {
        let m = p("---- MODULE M ----\nA == 1 + 2 * 3 = 7 /\\ ~ FALSE\n====\n").unwrap();
        match &m.module.units[0] {
            Unit::OpDef(d) => match &d.body {
                DefBody::Expr(e) => assert!(matches!(&*e.kind, ExprKind::Infix(_, n, ..) if &**n == "\\land")),
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn various_forms() {
        let src = "---- MODULE M ----\nEXTENDS Naturals, Sequences\nCONSTANT N, F(_), _ \\prec _\nVARIABLES a, b\n\
f[i \\in 1..N] == i * 2\nS == {x \\in 1..N : x > 2}\nT == {<<x, y>> \\in S \\X S : x < y}\nR == [a |-> 1, b |-> 2]\n\
U == [R EXCEPT !.a = 2, !.b = @ + 1]\nW == \\E x, y \\in S : x = y\nC == CASE a = 1 -> 2 [] a = 2 -> 3 [] OTHER -> 4\n\
L == LET g(z) == z + 1 IN g(2)\nSpec == a = 0 /\\ [][a' = a + 1]_<<a, b>> /\\ WF_<<a, b>>(a' = a + 1)\n\
THEOREM Spec => []TRUE\nASSUME N \\in Nat\n====\n";
        p(src).unwrap();
    }

    #[test]
    fn syntax_error_reported() {
        let e = p("---- MODULE M ----\nA == 1 +\n====\n").err().unwrap();
        assert!(e.text.contains("Parse Error") || e.text.contains("Couldn't") || e.text.contains("infix"), "{}", e.text);
    }
}
