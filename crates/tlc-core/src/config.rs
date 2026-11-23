//! Port of `tlc2.tool.impl.ModelConfig`: parser of the `.cfg` file.

use crate::ec;
use crate::value::Value;
use std::collections::HashMap;
use tla_sany::intern;

#[derive(Debug, Clone)]
pub struct CfgError {
    pub code: i32,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct ConstAssign {
    pub name: String,
    /// arguments given in `CONSTANT f(1, 2) = ...` (rare)
    pub args: Vec<Value>,
    pub value: Value,
}

#[derive(Debug, Default, Clone)]
pub struct ModelConfig {
    pub init: String,
    pub next: String,
    pub spec: String,
    pub view: String,
    pub symmetry: String,
    pub alias: String,
    pub periodic: String,
    pub constants: Vec<ConstAssign>,
    /// `Foo <- Bar` : (Foo, Bar)
    pub overrides: Vec<(String, String)>,
    /// `CONSTANT x = v` in module `[M]`
    pub mod_constants: HashMap<String, Vec<ConstAssign>>,
    pub mod_overrides: HashMap<String, Vec<(String, String)>>,
    pub constraints: Vec<String>,
    pub action_constraints: Vec<String>,
    pub invariants: Vec<String>,
    pub properties: Vec<String>,
    pub postconditions: Vec<String>,
    pub possible: Vec<String>,
    pub check_deadlock: Option<bool>,
    /// the model values and strings of the values, in the order the parser met (and interned) them
    pub value_order: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
enum T {
    Id(String),
    Num(String),
    Str(String),
    Sym(String),
    Eof,
}

struct Lx {
    chars: Vec<char>,
    i: usize,
    line: usize,
}

/// JavaCC `TokenMgrError.addEscapes`
fn add_escapes(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '\u{8}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            '"' => out.push_str("\\\""),
            '\'' => out.push_str("\\'"),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

impl Lx {
    /// Java: `TokenMgrError.LexicalError`: the token starting at char index `start` cannot be completed at `self.i`
    fn lexical_error(&self, start: usize, cur: Option<char>) -> CfgError {
        let mut line_start = self.i.min(self.chars.len());
        while line_start > 0 && self.chars[line_start - 1] != '\n' {
            line_start -= 1;
        }
        let column = self.i - line_start + 1;
        let after: String = self.chars[start..self.i.min(self.chars.len())].iter().collect();
        let encountered = match cur {
            None => "<EOF> ".to_string(),
            Some(c) => format!("\"{}\" ({}), ", add_escapes(&c.to_string()), c as u32),
        };
        let text = format!(
            "Lexical error at line {}, column {}.  Encountered: {}after : \"{}\"",
            self.line,
            column,
            encountered,
            add_escapes(&after)
        );
        cfg_err(ec::CFG_LEXICAL_ERROR, self.line, &text)
    }

    fn next(&mut self) -> Result<T, CfgError> {
        loop {
            while self.i < self.chars.len() && self.chars[self.i].is_whitespace() {
                if self.chars[self.i] == '\n' {
                    self.line += 1;
                }
                self.i += 1;
            }
            if self.i >= self.chars.len() {
                return Ok(T::Eof);
            }
            let c = self.chars[self.i];
            // comments
            if c == '\\' && self.chars.get(self.i + 1) == Some(&'*') {
                while self.i < self.chars.len() && self.chars[self.i] != '\n' {
                    self.i += 1;
                }
                continue;
            }
            if c == '(' && self.chars.get(self.i + 1) == Some(&'*') {
                let mut depth = 0;
                while self.i < self.chars.len() {
                    if self.chars[self.i] == '(' && self.chars.get(self.i + 1) == Some(&'*') {
                        depth += 1;
                        self.i += 2;
                    } else if self.chars[self.i] == '*' && self.chars.get(self.i + 1) == Some(&')') {
                        depth -= 1;
                        self.i += 2;
                        if depth == 0 {
                            break;
                        }
                    } else {
                        if self.chars[self.i] == '\n' {
                            self.line += 1;
                        }
                        self.i += 1;
                    }
                }
                continue;
            }
            if c.is_ascii_alphabetic() || c == '_' {
                let s = self.i;
                while self.i < self.chars.len() && (self.chars[self.i].is_ascii_alphanumeric() || self.chars[self.i] == '_') {
                    self.i += 1;
                }
                return Ok(T::Id(self.chars[s..self.i].iter().collect()));
            }
            if c.is_ascii_digit() {
                let s = self.i;
                while self.i < self.chars.len() && self.chars[self.i].is_ascii_digit() {
                    self.i += 1;
                }
                // identifiers such as 1a are lexed as identifiers by SANY's lexer
                if self.i < self.chars.len() && (self.chars[self.i].is_ascii_alphabetic() || self.chars[self.i] == '_') {
                    while self.i < self.chars.len() && (self.chars[self.i].is_ascii_alphanumeric() || self.chars[self.i] == '_') {
                        self.i += 1;
                    }
                    return Ok(T::Id(self.chars[s..self.i].iter().collect()));
                }
                return Ok(T::Num(self.chars[s..self.i].iter().collect()));
            }
            if c == '"' {
                let s = self.i;
                self.i += 1;
                while self.i < self.chars.len() && self.chars[self.i] != '"' {
                    // Java (TokenMgrError): a string literal that is not closed before the end of the line is a lexical error
                    if self.chars[self.i] == '\n' {
                        return Err(self.lexical_error(s, Some('\n')));
                    }
                    if self.chars[self.i] == '\\' {
                        self.i += 1;
                    }
                    self.i += 1;
                }
                if self.i >= self.chars.len() {
                    return Err(self.lexical_error(s, None));
                }
                self.i += 1;
                let end = self.i.min(self.chars.len());
                return Ok(T::Str(self.chars[s..end].iter().collect()));
            }
            // symbols
            let two: String = self.chars[self.i..(self.i + 2).min(self.chars.len())].iter().collect();
            if two == "<-" || two == "<<" || two == ">>" {
                self.i += 2;
                return Ok(T::Sym(two));
            }
            self.i += 1;
            return Ok(T::Sym(c.to_string()));
        }
    }
}

fn is_keyword(s: &str) -> bool {
    matches!(
        s,
        "CONSTANT"
            | "CONSTANTS"
            | "CONSTRAINT"
            | "CONSTRAINTS"
            | "ACTION_CONSTRAINT"
            | "ACTION_CONSTRAINTS"
            | "INVARIANT"
            | "INVARIANTS"
            | "INIT"
            | "NEXT"
            | "VIEW"
            | "SYMMETRY"
            | "SPECIFICATION"
            | "PROPERTY"
            | "PROPERTIES"
            | "ALIAS"
            | "POSTCONDITION"
            | "POSTCONDITIONS"
            | "_PERIODIC"
            | "_RL_REWARD"
            | "_POSSIBLE"
            | "CHECK_DEADLOCK"
    )
}

fn cfg_err(code: i32, line: usize, a: &str) -> CfgError {
    let text = match code {
        ec::CFG_MISSING_ID => format!("TLC found an error in the configuration file at line {}\nThe keyword {} was not followed by an identifier.", line, a),
        ec::CFG_TWICE_KEYWORD => format!("TLC found an error in the configuration file at line {}\nThe keyword {} appeared twice.", line, a),
        ec::CFG_EXPECT_ID => format!("TLC found an error in the configuration file at line {}\nExpected an identifier after {}.", line, a),
        ec::CFG_EXPECTED_SYMBOL => format!("TLC found an error in the configuration file at line {}\nIt was expecting {}, but did not find it.", line, a),
        ec::CFG_GENERAL => format!("TLC found an error in the configuration file at line {}\n", line),
        _ => format!("TLC found an error in the configuration file:\n{}", a),
    };
    CfgError { code, text }
}

fn tok_image(t: &T) -> String {
    match t {
        T::Id(s) | T::Num(s) | T::Str(s) | T::Sym(s) => s.clone(),
        T::Eof => String::new(),
    }
}

struct P {
    lx: Lx,
    cur: T,
    /// Java: `ModelValue.make` / `new StringValue` intern their text while the file is parsed: the distinct texts in that order
    order: Vec<String>,
}

impl P {
    fn adv(&mut self) -> Result<T, CfgError> {
        let n = self.lx.next()?;
        Ok(std::mem::replace(&mut self.cur, n))
    }

    fn note(&mut self, s: &str) {
        if !self.order.iter().any(|x| x == s) {
            self.order.push(s.to_string());
        }
    }

    fn parse_value(&mut self, t: &T) -> Result<Value, CfgError> {
        match t {
            T::Num(s) => match s.parse::<i32>() {
                Ok(i) => Ok(Value::Int(i)),
                Err(_) => Err(cfg_err(ec::CFG_LEXICAL_ERROR, self.lx.line, &format!("number out of range: {}", s))),
            },
            T::Str(s) => {
                let inner = &s[1..s.len().saturating_sub(1).max(1)];
                if inner.contains('\\') {
                    return Err(cfg_err(
                        ec::CFG_LEXICAL_ERROR,
                        self.lx.line,
                        &format!("escape sequences are not supported in strings at line {}", self.lx.line),
                    ));
                }
                let inner = inner.to_string();
                self.note(&inner);
                Ok(Value::str(&inner))
            }
            T::Id(s) if s == "TRUE" => Ok(Value::Bool(true)),
            T::Id(s) if s == "FALSE" => Ok(Value::Bool(false)),
            T::Sym(s) if s == "{" => {
                let mut elems = vec![];
                let mut t = self.adv()?;
                if !matches!(&t, T::Sym(c) if c == "}") {
                    loop {
                        elems.push(self.parse_value(&t)?);
                        t = self.adv()?;
                        if !matches!(&t, T::Sym(c) if c == ",") {
                            break;
                        }
                        t = self.adv()?;
                    }
                }
                if !matches!(&t, T::Sym(c) if c == "}") {
                    return Err(cfg_err(ec::CFG_EXPECTED_SYMBOL, self.lx.line, "}"));
                }
                Value::set_from(elems).map_err(|e| cfg_err(ec::CFG_GENERAL, self.lx.line, &e.msg))
            }
            T::Eof => Err(cfg_err(ec::CFG_EXPECTED_SYMBOL, self.lx.line, "a value")),
            other => {
                let img = tok_image(other);
                self.note(&img);
                let id = intern::intern(&img);
                crate::value::register_model(id);
                Ok(Value::Model(id))
            }
        }
    }
}

pub fn parse(text: &str) -> Result<ModelConfig, CfgError> {
    let mut src = text.to_string();
    src.push('\n');
    let mut p = P { lx: Lx { chars: src.chars().collect(), i: 0, line: 1 }, cur: T::Eof, order: vec![] };
    p.cur = p.lx.next()?;
    let mut cfg = ModelConfig::default();
    let mut tt = p.adv()?;
    let mut seen_deadlock = false;
    while tt != T::Eof {
        let tval = tok_image(&tt);
        let loc = p.lx.line;
        let single = |p: &mut P, slot: &mut String, kw: &str| -> Result<T, CfgError> {
            let t = p.adv()?;
            if t == T::Eof {
                return Err(cfg_err(ec::CFG_MISSING_ID, loc, kw));
            }
            if !slot.is_empty() {
                return Err(cfg_err(ec::CFG_TWICE_KEYWORD, loc, kw));
            }
            *slot = tok_image(&t);
            p.adv()
        };
        let list = |p: &mut P, v: &mut Vec<String>| -> Result<T, CfgError> {
            loop {
                let t = p.adv()?;
                if t == T::Eof {
                    return Ok(T::Eof);
                }
                if is_keyword(&tok_image(&t)) {
                    return Ok(t);
                }
                v.push(tok_image(&t));
            }
        };
        match tval.as_str() {
            "INIT" => tt = single(&mut p, &mut cfg.init, "INIT")?,
            "NEXT" => tt = single(&mut p, &mut cfg.next, "NEXT")?,
            "SPECIFICATION" => tt = single(&mut p, &mut cfg.spec, "SPECIFICATION")?,
            "VIEW" => tt = single(&mut p, &mut cfg.view, "VIEW")?,
            "SYMMETRY" => tt = single(&mut p, &mut cfg.symmetry, "SYMMETRY")?,
            "ALIAS" => tt = single(&mut p, &mut cfg.alias, "ALIAS")?,
            "_PERIODIC" => tt = single(&mut p, &mut cfg.periodic, "_PERIODIC")?,
            "_RL_REWARD" => {
                let mut dummy = String::new();
                tt = single(&mut p, &mut dummy, "_RL_REWARD")?
            }
            "POSTCONDITION" | "POSTCONDITIONS" => {
                let mut v = vec![];
                tt = list(&mut p, &mut v)?;
                cfg.postconditions.extend(v);
            }
            "INVARIANT" | "INVARIANTS" => {
                let mut v = vec![];
                tt = list(&mut p, &mut v)?;
                cfg.invariants.extend(v);
            }
            "PROPERTY" | "PROPERTIES" => {
                let mut v = vec![];
                tt = list(&mut p, &mut v)?;
                cfg.properties.extend(v);
            }
            "CONSTRAINT" | "CONSTRAINTS" => {
                let mut v = vec![];
                tt = list(&mut p, &mut v)?;
                cfg.constraints.extend(v);
            }
            "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => {
                let mut v = vec![];
                tt = list(&mut p, &mut v)?;
                cfg.action_constraints.extend(v);
            }
            "_POSSIBLE" => {
                let mut v = vec![];
                tt = list(&mut p, &mut v)?;
                cfg.possible.extend(v);
            }
            "CHECK_DEADLOCK" => {
                let t = p.adv()?;
                if t == T::Eof {
                    return Err(cfg_err(ec::CFG_MISSING_ID, loc, "CHECK_DEADLOCK"));
                }
                let val = match tok_image(&t).as_str() {
                    "TRUE" => true,
                    "FALSE" => false,
                    _ => return Err(cfg_err(ec::CFG_EXPECTED_SYMBOL, p.lx.line, "TRUE or FALSE")),
                };
                if seen_deadlock {
                    return Err(cfg_err(ec::CFG_TWICE_KEYWORD, loc, "CHECK_DEADLOCK"));
                }
                seen_deadlock = true;
                cfg.check_deadlock = Some(val);
                tt = p.adv()?;
            }
            "CONSTANT" | "CONSTANTS" => {
                loop {
                    tt = p.adv()?;
                    if tt == T::Eof || is_keyword(&tok_image(&tt)) {
                        break;
                    }
                    let mut lhs = tok_image(&tt);
                    let mut t = p.adv()?;
                    while tok_image(&t) == "!" {
                        t = p.adv()?;
                        lhs = format!("{}!{}", lhs, tok_image(&t));
                        t = p.adv()?;
                    }
                    let mut args: Vec<Value> = vec![];
                    if tok_image(&t) == "<-" {
                        t = p.adv()?;
                        if tok_image(&t) == "[" {
                            let m = p.adv()?;
                            if m == T::Eof {
                                return Err(cfg_err(ec::CFG_EXPECT_ID, p.lx.line, "<-["));
                            }
                            let modname = tok_image(&m);
                            t = p.adv()?;
                            if tok_image(&t) != "]" {
                                return Err(cfg_err(ec::CFG_EXPECTED_SYMBOL, p.lx.line, "]"));
                            }
                            t = p.adv()?;
                            if t == T::Eof {
                                return Err(cfg_err(ec::CFG_EXPECT_ID, p.lx.line, "<-[mod]"));
                            }
                            cfg.mod_overrides.entry(modname).or_default().push((lhs, tok_image(&t)));
                        } else {
                            if t == T::Eof {
                                return Err(cfg_err(ec::CFG_EXPECT_ID, p.lx.line, "<-"));
                            }
                            cfg.overrides.push((lhs, tok_image(&t)));
                        }
                    } else {
                        if tok_image(&t) == "(" {
                            loop {
                                t = p.adv()?;
                                let v = p.parse_value(&t)?;
                                args.push(v);
                                t = p.adv()?;
                                if tok_image(&t) != "," {
                                    break;
                                }
                            }
                            if tok_image(&t) != ")" {
                                return Err(cfg_err(ec::CFG_GENERAL, loc, ""));
                            }
                            t = p.adv()?;
                        }
                        if tok_image(&t) != "=" {
                            return Err(cfg_err(ec::CFG_EXPECTED_SYMBOL, p.lx.line, "= or <-"));
                        }
                        t = p.adv()?;
                        if tok_image(&t) == "[" {
                            let m = p.adv()?;
                            if m == T::Eof {
                                return Err(cfg_err(ec::CFG_EXPECT_ID, p.lx.line, "=["));
                            }
                            let modname = tok_image(&m);
                            t = p.adv()?;
                            if tok_image(&t) != "]" {
                                return Err(cfg_err(ec::CFG_EXPECTED_SYMBOL, p.lx.line, "]"));
                            }
                            t = p.adv()?;
                            let v = p.parse_value(&t)?;
                            cfg.mod_constants.entry(modname).or_default().push(ConstAssign { name: lhs, args, value: v });
                        } else {
                            let v = p.parse_value(&t)?;
                            cfg.constants.push(ConstAssign { name: lhs, args, value: v });
                        }
                    }
                }
            }
            _ => return Err(cfg_err(ec::CFG_EXPECTED_SYMBOL, p.lx.line, "a keyword")),
        }
    }
    cfg.value_order = std::mem::take(&mut p.order);
    Ok(cfg)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_typical_config() {
        let c = parse("SPECIFICATION Spec\nCONSTANT N = 3\n  S = {a, b}\n  Foo <- Bar\nINVARIANT TypeOK Inv\n\\* comment\nCHECK_DEADLOCK FALSE\n").unwrap();
        assert_eq!(c.spec, "Spec");
        assert_eq!(c.constants.len(), 2);
        assert_eq!(c.overrides, vec![("Foo".to_string(), "Bar".to_string())]);
        assert_eq!(c.invariants, vec!["TypeOK", "Inv"]);
        assert_eq!(c.check_deadlock, Some(false));
    }
}
