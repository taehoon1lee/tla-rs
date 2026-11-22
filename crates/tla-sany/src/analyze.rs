//! Port (re-implementation) of `tla2sany.semantic.Generator` + `SymbolTable` + `Context` + level computation:
//! turns the syntax tree of each module into the semantic graph of `sem.rs`.

use crate::ast::{self, DefBody, Loc, Unit};
use crate::modules::{ModId, SpecObj};
use crate::sem::*;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Msg {
    pub loc: Option<(Loc, Name)>,
    pub text: String,
    pub module_only: Option<Name>,
}

impl Msg {
    pub fn render(&self) -> String {
        let l = match (&self.loc, &self.module_only) {
            (Some((l, m)), _) => format!("line {}, col {} to line {}, col {} of module {}", l.bl, l.bc, l.el, l.ec, m),
            (None, Some(m)) => format!("In module {}", m),
            (None, None) => "Unknown location".to_string(),
        };
        format!("{}\n\n{}", l, self.text)
    }
}

#[derive(Default)]
pub struct Errors {
    pub errors: Vec<Msg>,
    pub warnings: Vec<Msg>,
}

/// the result of semantic analysis
pub struct SemSpec {
    pub modules: HashMap<String, Rc<ModuleNode>>,
    /// the root module (the last one analysed)
    pub root: Rc<ModuleNode>,
    pub order: Vec<String>,
}

/// a lexical scope
#[derive(Default)]
pub(crate) struct Scope {
    pub(crate) map: HashMap<(bool, Name), Sym>,
    pub(crate) locs: HashMap<(bool, Name), Loc>,
}

pub(crate) struct Analyzer<'a> {
    pub(crate) spec: &'a SpecObj,
    pub(crate) table: HashMap<String, Rc<ModuleNode>>,
    pub(crate) errors: Errors,
    pub(crate) scopes: Vec<Scope>,
    pub(crate) cur: Option<Rc<ModuleNode>>,
    pub(crate) cur_name: Name,
    /// nesting depth of EXCEPT value expressions where `@` is meaningful
    pub(crate) at_depth: i32,
    pub(crate) let_level: i32,
    pub(crate) mod_depth_stack: Vec<usize>,
    /// RECURSIVE-declared definitions awaiting a definition (per module / LET level)
    pub(crate) pending_rec: Vec<Rc<OpDef>>,
    /// function definitions being processed (for recursion detection)
    pub(crate) cur_fcn: Vec<(Rc<Param>, Rc<Cell<bool>>)>,
    pub(crate) levels: bool,
}

pub(crate) type R<T> = Result<T, ()>;

pub(crate) fn nm(s: &str) -> Name {
    Name::from(s)
}

pub(crate) fn is_local(sym: &Sym) -> bool {
    match sym {
        Sym::Def(d) => d.local.get(),
        _ => false,
    }
}

pub(crate) fn sym_module(sym: &Sym) -> Option<Name> {
    match sym {
        Sym::Def(d) => Some(d.module.clone()),
        Sym::Decl(d) => Some(d.module.clone()),
        _ => None,
    }
}

pub(crate) fn sym_loc(sym: &Sym) -> Loc {
    match sym {
        Sym::Def(d) => d.loc,
        Sym::Decl(d) => d.loc,
        Sym::Param(p) => p.loc,
        Sym::Module(m) => m.loc,
        Sym::Builtin(_) => Loc::default(),
    }
}

pub(crate) fn sym_arity(sym: &Sym) -> usize {
    match sym {
        Sym::Def(d) => d.arity(),
        Sym::Decl(d) => d.arity,
        Sym::Param(p) => p.arity,
        Sym::Builtin(b) => b.arity(),
        Sym::Module(_) => 0,
    }
}

pub(crate) fn sym_kind_tag(sym: &Sym) -> u8 {
    match sym {
        Sym::Def(_) => 1,
        Sym::Decl(d) => match d.kind {
            DeclKind::Constant => 2,
            DeclKind::Variable => 3,
        },
        Sym::Param(_) => 4,
        Sym::Builtin(_) => 5,
        Sym::Module(_) => 6,
    }
}

impl<'a> Analyzer<'a> {
    pub(crate) fn new(spec: &'a SpecObj, levels: bool) -> Self {
        Analyzer {
            spec,
            table: HashMap::new(),
            errors: Errors::default(),
            scopes: Vec::new(),
            cur: None,
            cur_name: nm(""),
            at_depth: 0,
            let_level: 0,
            mod_depth_stack: Vec::new(),
            pending_rec: Vec::new(),
            cur_fcn: Vec::new(),
            levels,
        }
    }

    // ------------------------------------------------------------------ errors

    pub(crate) fn err(&mut self, loc: Loc, text: impl Into<String>) {
        let m = Msg { loc: Some((loc, self.cur_name.clone())), text: text.into(), module_only: None };
        if !self.errors.errors.iter().any(|x| x.text == m.text && x.loc.as_ref().map(|l| l.0) == m.loc.as_ref().map(|l| l.0)) {
            self.errors.errors.push(m);
        }
    }

    pub(crate) fn warn(&mut self, loc: Loc, text: impl Into<String>) {
        let m = Msg { loc: Some((loc, self.cur_name.clone())), text: text.into(), module_only: None };
        if !self.errors.warnings.iter().any(|x| x.text == m.text && x.loc.as_ref().map(|l| l.0) == m.loc.as_ref().map(|l| l.0)) {
            self.errors.warnings.push(m);
        }
    }

    pub(crate) fn loc_s(&self, loc: Loc, module: &Name) -> String {
        format!("line {}, col {} to line {}, col {} of module {}", loc.bl, loc.bc, loc.el, loc.ec, module)
    }

    // ------------------------------------------------------------------ symbol table

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }
    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(crate) fn builtin_sym(&mut self, name: &str) -> Option<Sym> {
        B::from_name(name).map(Sym::Builtin)
    }

    /// `SymbolTable.resolveSymbol`
    pub(crate) fn resolve(&mut self, name: &str) -> Option<Sym> {
        let key = (false, nm(name));
        for sc in self.scopes.iter().rev() {
            if let Some(s) = sc.map.get(&key) {
                return Some(s.clone());
            }
        }
        self.builtin_sym(name)
    }

    pub(crate) fn resolve_module(&self, name: &str) -> Option<Rc<ModuleNode>> {
        let key = (true, nm(name));
        for sc in self.scopes.iter().rev() {
            if let Some(Sym::Module(m)) = sc.map.get(&key) {
                return Some(m.clone());
            }
        }
        self.table.get(name).cloned()
    }

    /// insert directly into the top scope (and, for module-level scope, the module's exported context)
    pub(crate) fn put(&mut self, name: Name, sym: Sym, loc: Loc) {
        let is_mod = matches!(sym, Sym::Module(_));
        let top = self.scopes.last_mut().unwrap();
        top.map.insert((is_mod, name.clone()), sym.clone());
        top.locs.insert((is_mod, name.clone()), loc);
        if self.scopes.len() == self.module_scope_depth() {
            if let Some(m) = &self.cur {
                m.ctx.borrow_mut().insert(name, sym, loc);
            }
        }
    }

    pub(crate) fn module_scope_depth(&self) -> usize {
        self.mod_depth_stack.last().copied().unwrap_or(1)
    }

    /// `SymbolTable.addSymbol`
    pub(crate) fn add_symbol(&mut self, name: Name, sym: Sym, loc: Loc) -> bool {
        let cur = self.resolve(&name);
        if let Some(cur) = &cur {
            if cur.same(&sym) {
                return true;
            }
        }
        match cur {
            None => {
                self.put(name, sym, loc);
                true
            }
            Some(Sym::Builtin(_)) => {
                self.err(loc, format!("Symbol {} is a built-in operator, and cannot be redefined.", name));
                false
            }
            Some(cur) => {
                let is_param = matches!(sym, Sym::Param(_));
                if is_param || sym_kind_tag(&cur) != sym_kind_tag(&sym) || sym_arity(&cur) != sym_arity(&sym) {
                    let cl = sym_loc(&cur);
                    let cm = sym_module(&cur).unwrap_or_else(|| self.cur_name.clone());
                    self.err(
                        loc,
                        format!(
                            "Multiply-defined symbol '{}': this definition or declaration conflicts \nwith the one at {}.",
                            name,
                            self.loc_s(cl, &cm)
                        ),
                    );
                    return false;
                }
                if self.same_originally(&sym, &cur) {
                    return true;
                }
                let cl = sym_loc(&cur);
                let cm = sym_module(&cur).unwrap_or_else(|| self.cur_name.clone());
                let m = self.loc_s(cl, &cm);
                self.warn(
                    loc,
                    format!("Multiple declarations or definitions for symbol {}.  \nThis duplicates the one at {}.", name, m),
                );
                true
            }
        }
    }

    // ------------------------------------------------------------------ module generation

    pub(crate) fn gen_module(&mut self, m: &ast::Module, parent: Option<&Rc<ModuleNode>>) -> R<Rc<ModuleNode>> {
        let node = Rc::new(ModuleNode::new(m.name.clone(), m.loc));
        let saved_cur = self.cur.clone();
        let saved_name = self.cur_name.clone();
        self.cur = Some(node.clone());
        self.cur_name = m.name.clone();
        if let Some(p) = parent {
            p.inner_modules.borrow_mut().push(node.clone());
        }
        self.mod_depth_stack.push(self.scopes.len() + 1);
        self.push_scope();
        let r = self.gen_module_body(m, &node);
        self.pop_scope();
        self.mod_depth_stack.pop();
        self.cur = saved_cur;
        self.cur_name = saved_name;
        r?;
        Ok(node)
    }

    fn gen_module_body(&mut self, m: &ast::Module, node: &Rc<ModuleNode>) -> R<()> {
        // EXTENDS
        for e in &m.extends {
            let ext = match self.resolve_module(&e.name) {
                Some(x) => x,
                None => {
                    self.err(e.loc, format!("Could not find module {}", e.name));
                    return Err(());
                }
            };
            self.merge_extend(&ext, e.loc);
            node.extends.borrow_mut().push(ext.clone());
            for d in ext.decls.borrow().iter() {
                if !node.decls.borrow().iter().any(|x| Rc::ptr_eq(x, d)) {
                    node.decls.borrow_mut().push(d.clone());
                }
            }
            for a in ext.assumes.borrow().iter() {
                node.assumes.borrow_mut().push(a.clone());
            }
        }
        for u in &m.units {
            match u {
                Unit::Variable(names, _) => {
                    for id in names {
                        let d = Rc::new(OpDecl {
                            id: fresh_id(),
                            name: id.name.clone(),
                            kind: DeclKind::Variable,
                            arity: 0,
                            module: self.cur_name.clone(),
                            loc: id.loc,
                        });
                        if self.add_symbol(id.name.clone(), Sym::Decl(d.clone()), id.loc) {
                            node.decls.borrow_mut().push(d);
                        }
                    }
                }
                Unit::Constant(decls, _) => {
                    for dd in decls {
                        let d = Rc::new(OpDecl {
                            id: fresh_id(),
                            name: dd.name.clone(),
                            kind: DeclKind::Constant,
                            arity: dd.arity,
                            module: self.cur_name.clone(),
                            loc: dd.loc,
                        });
                        if self.add_symbol(dd.name.clone(), Sym::Decl(d.clone()), dd.loc) {
                            node.decls.borrow_mut().push(d);
                        }
                    }
                }
                Unit::OpDef(d) => match &d.body {
                    DefBody::Instance(inst) => {
                        let _ = self.process_module_definition(d, inst, node, None);
                    }
                    DefBody::Function(..) => {
                        let _ = self.process_function(d, node, None);
                    }
                    DefBody::Expr(_) => {
                        let _ = self.process_operator(d, node, None);
                    }
                },
                Unit::Recursive(decls, _) => self.process_recursive(decls),
                Unit::Instance(i) => {
                    let _ = self.generate_instance(i.local, &i.inst, node, i.loc, true);
                }
                Unit::Module(inner) => {
                    // nested module: separate symbol table sharing the outer ones
                    let im = self.gen_module(inner, Some(node))?;
                    self.add_module_name(im.name.clone(), im.clone(), inner.name_loc);
                }
                Unit::Assume(a) => {
                    if let Ok(e) = self.gen_expr(&a.body) {
                        let n = Rc::new(AssumeNode { name: a.name.as_ref().map(|x| x.name.clone()), expr: e.clone(), module: self.cur_name.clone(), loc: a.loc });
                        node.assumes.borrow_mut().push(n);
                        if let Some(nm_) = &a.name {
                            let d = crate::analyze_expr::new_def(nm_.name.clone(), vec![], Some(e.clone()), false, DefKind::Theorem, self.cur_name.clone(), a.loc);
                            d.level.set(e.level);
                            if self.add_symbol(nm_.name.clone(), Sym::Def(d.clone()), a.loc) {
                                node.defs.borrow_mut().push(d);
                            }
                        }
                    }
                }
                Unit::Theorem(t) => {
                    // name resolution inside the statement only (proofs are not analysed)
                    let body = match &t.body {
                        ast::TheoremBody::Expr(e) => self.gen_expr(e).ok(),
                        ast::TheoremBody::AssumeProve(_) => None,
                    };
                    if let Some(n) = &t.name {
                        let d = crate::analyze_expr::new_def(n.name.clone(), vec![], body.clone(), false, DefKind::Theorem, self.cur_name.clone(), t.loc);
                        d.level.set(body.as_ref().map_or(Level::Const, |b| b.level));
                        if self.add_symbol(n.name.clone(), Sym::Def(d.clone()), t.loc) {
                            node.defs.borrow_mut().push(d);
                        }
                    }
                }
                Unit::UseHide(_) | Unit::Separator(_) => {}
            }
        }
        // undefined RECURSIVE operators
        let pend: Vec<Rc<OpDef>> = self.pending_rec.drain(..).collect();
        for d in pend {
            if !d.is_defined.get() {
                self.err(d.loc, format!("Recursive operator {} was declared but never defined.", d.name));
            }
        }
        // parameter-free?
        node.param_free.set(node.decls.borrow().is_empty());
        Ok(())
    }

    pub(crate) fn add_module_name(&mut self, name: Name, m: Rc<ModuleNode>, loc: Loc) {
        let key = (true, name.clone());
        let exists = self.scopes.iter().any(|s| s.map.contains_key(&key)) || self.table.contains_key(&*name);
        if exists {
            self.err(loc, format!("Multiply-defined module '{}': this definition or declaration conflicts \nwith the one at {}.", name, self.loc_s(m.loc, &name)));
            return;
        }
        self.put(name, Sym::Module(m), loc);
    }

    /// `Context.mergeExtendContext`
    pub(crate) fn merge_extend(&mut self, ext: &Rc<ModuleNode>, loc: Loc) {
        let items: Vec<(Name, Sym, Loc)> = ext.ctx.borrow().items.clone();
        for (name, sym, _l) in items {
            if is_local(&sym) {
                continue;
            }
            let is_mod = matches!(sym, Sym::Module(_));
            let existing = {
                let top = self.scopes.last().unwrap();
                top.map.get(&(is_mod, name.clone())).cloned()
            };
            match existing {
                None => {
                    let l = sym_loc(&sym);
                    self.put(name, sym, l);
                }
                Some(ex) => {
                    if ex.same(&sym) {
                        continue;
                    }
                    if sym_kind_tag(&ex) == sym_kind_tag(&sym) {
                        if sym_module(&ex) != sym_module(&sym) {
                            let m = sym_module(&ex).unwrap_or_else(|| self.cur_name.clone());
                            let at = self.loc_s(sym_loc(&ex), &m);
                            let kind = match ex {
                                Sym::Def(_) => "definition",
                                Sym::Decl(ref d) if d.kind == DeclKind::Constant => "declaration",
                                Sym::Decl(_) => "declaration",
                                _ => "symbol",
                            };
                            self.warn(loc, format!("Warning: the {} of '{}' conflicts with \nits {} at {}.", kind, name, kind, at));
                        }
                    } else {
                        let m = sym_module(&ex).unwrap_or_else(|| self.cur_name.clone());
                        let at = self.loc_s(sym_loc(&ex), &m);
                        self.err(loc, format!("The definition of '{}' conflicts with \nits definition at {}.", name, at));
                    }
                }
            }
        }
    }
}
