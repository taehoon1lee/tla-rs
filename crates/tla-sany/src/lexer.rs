//! Port of the token manager generated from `TT/javacc/tla+.jj` (SPEC lexical state) + `SimpleCharStream`.
//!
//! JavaCC semantics reproduced: longest match wins, ties go to the token declared first (keywords and
//! punctuation before identifiers); `(* ... *)` nested block comments and `\* ...` line comments are
//! skipped; positions are 1-based with tab stops of 8 (SimpleCharStream.UpdateLineColumn).

use std::sync::Arc;

/// Token kinds (the subset of `TLAplusParserConstants` the grammar distinguishes). Operator tokens are grouped:
/// the exact operator is identified by the token image (see `ops.rs`).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Tk {
    Eof,
    BeginModule, // _BM0/_BM1/_BM2
    Separator,
    EndModule,
    Action,
    Assume,
    BoxAssume,
    Assumption,
    Case,
    Choose,
    Constant,
    Else,
    Except,
    Exists,
    Extends,
    Forall,
    If,
    Instance,
    Let,
    LetIn,
    Local,
    Module,
    New,
    Other,
    Proposition,
    Sf,
    TExists,
    TForall,
    Then,
    By,
    Only,
    Define,
    Df,
    Theorem,
    Use,
    Hide,
    Have,
    Obvious,
    Omitted,
    Lambda,
    Take,
    Proof,
    Prove,
    BoxProve,
    Qed,
    Recursive,
    State,
    Temporal,
    Pick,
    Witness,
    Suffices,
    Variable,
    Wf,
    With,
    Comma,
    Colon,
    ColonColon,
    Dot,
    Us,
    Def,
    Lbr,
    Rbr,
    DefBreak,
    Lsb,
    Arsb,
    Rsb,
    Lbc,
    Rbc,
    Lab,
    Arab,
    Rab,
    Bang,
    Arrow,
    Substitute,
    MapTo,
    NumberLiteral,
    StringLiteral,
    Identifier,
    ProofStepLexeme,
    ProofImplicitStepLexeme,
    ProofStepDotLexeme,
    BareLevelLexeme,
    UnnumberedStepLexeme,
    // ---- operator tokens
    Postfix, // ' ^+ ^* ^#
    MinusDot, // -.   (op_76, prefix)
    Prefix,  // \lnot \neg ~ <> ENABLED UNCHANGED SUBSET UNION DOMAIN  (op_26 op_29 op_58 op_61 op_112..116)
    CaseSep, // [] (prefix op and CASE separator)
    And,
    Or,
    In,
    Equals,
    Minus,  // - (op_77), infix and (mixfix) prefix
    Infix,  // every other infix operator
    /// lexical error (carries the message in `image`)
    Error,
}

impl Tk {
    pub fn is_op(self) -> bool {
        matches!(
            self,
            Tk::Postfix | Tk::MinusDot | Tk::Prefix | Tk::CaseSep | Tk::And | Tk::Or | Tk::In | Tk::Equals | Tk::Minus | Tk::Infix
        )
    }
    pub fn is_infix(self) -> bool {
        matches!(self, Tk::And | Tk::Or | Tk::In | Tk::Equals | Tk::Minus | Tk::Infix)
    }
    pub fn is_postfix(self) -> bool {
        self == Tk::Postfix
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: Tk,
    pub image: Arc<str>,
    pub bl: u32,
    pub bc: u32,
    pub el: u32,
    pub ec: u32,
}

impl Token {
    pub fn synthetic(kind: Tk, image: &str, like: &Token) -> Token {
        Token { kind, image: image.into(), bl: like.bl, bc: like.bc, el: like.el, ec: like.ec }
    }
}

fn kw(s: &str) -> Option<Tk> {
    Some(match s {
        "ACTION" | "ACTIONS" => Tk::Action,
        "ASSUME" => Tk::Assume,
        "[]ASSUME" => Tk::BoxAssume,
        "ASSUMPTION" | "AXIOM" => Tk::Assumption,
        "CASE" => Tk::Case,
        "CHOOSE" => Tk::Choose,
        "CONSTANT" | "CONSTANTS" => Tk::Constant,
        "ELSE" => Tk::Else,
        "EXCEPT" => Tk::Except,
        "\\E" | "\\exists" | "∃" => Tk::Exists,
        "EXTENDS" => Tk::Extends,
        "\\A" | "\\forall" | "∀" => Tk::Forall,
        "IF" => Tk::If,
        "INSTANCE" => Tk::Instance,
        "LET" => Tk::Let,
        "IN" => Tk::LetIn,
        "LOCAL" => Tk::Local,
        "MODULE" => Tk::Module,
        "NEW" => Tk::New,
        "OTHER" => Tk::Other,
        "PROPOSITION" | "LEMMA" | "COROLLARY" => Tk::Proposition,
        "SF_" => Tk::Sf,
        "\\EE" => Tk::TExists,
        "\\AA" => Tk::TForall,
        "THEN" => Tk::Then,
        "BY" => Tk::By,
        "ONLY" => Tk::Only,
        "DEFINE" => Tk::Define,
        "DEF" | "DEFS" => Tk::Df,
        "THEOREM" => Tk::Theorem,
        "USE" => Tk::Use,
        "HIDE" => Tk::Hide,
        "HAVE" => Tk::Have,
        "OBVIOUS" => Tk::Obvious,
        "OMITTED" => Tk::Omitted,
        "LAMBDA" => Tk::Lambda,
        "TAKE" => Tk::Take,
        "PROOF" => Tk::Proof,
        "PROVE" => Tk::Prove,
        "[]PROVE" => Tk::BoxProve,
        "QED" => Tk::Qed,
        "RECURSIVE" => Tk::Recursive,
        "STATE" => Tk::State,
        "TEMPORAL" | "TEMPORALS" => Tk::Temporal,
        "PICK" => Tk::Pick,
        "WITNESS" => Tk::Witness,
        "SUFFICES" => Tk::Suffices,
        "VARIABLE" | "VARIABLES" => Tk::Variable,
        "WF_" => Tk::Wf,
        "WITH" => Tk::With,
        "," => Tk::Comma,
        ":" => Tk::Colon,
        "::" | "∷" => Tk::ColonColon,
        "." => Tk::Dot,
        "_" => Tk::Us,
        "==" | "≜" => Tk::Def,
        "(" => Tk::Lbr,
        ")" => Tk::Rbr,
        "-|-" => Tk::DefBreak,
        "[" => Tk::Lsb,
        "]_" => Tk::Arsb,
        "]" => Tk::Rsb,
        "{" => Tk::Lbc,
        "}" => Tk::Rbc,
        "<<" | "⟨" => Tk::Lab,
        ">>_" | "⟩_" => Tk::Arab,
        ">>" | "⟩" => Tk::Rab,
        "!" => Tk::Bang,
        "->" | "→" => Tk::Arrow,
        "<-" | "←" => Tk::Substitute,
        "|->" | "↦" => Tk::MapTo,
        _ => return None,
    })
}

/// Operator token spellings (everything in the `op_*` run + AND/OR/IN/EQUALS/CASESEP).
fn op_kind(s: &str) -> Option<Tk> {
    Some(match s {
        "'" | "^+" | "⁺" | "^*" | "^#" => Tk::Postfix,
        "-." => Tk::MinusDot,
        "\\lnot" | "¬" | "\\neg" | "~" | "<>" | "◇" | "ENABLED" | "UNCHANGED" | "SUBSET" | "UNION" | "DOMAIN" => Tk::Prefix,
        "[]" | "□" => Tk::CaseSep,
        "/\\" | "∧" => Tk::And,
        "\\/" | "∨" => Tk::Or,
        "\\in" | "∈" => Tk::In,
        "=" => Tk::Equals,
        "-" => Tk::Minus,
        _ => {
            if INFIX_OPS.contains(&s) {
                Tk::Infix
            } else {
                return None;
            }
        }
    })
}

const INFIX_OPS: &[&str] = &[
    "//", "/=", "/", "\\approx", "\\asymp", "\\bigcirc", "\\bullet", "\\cap", "\\cdot", "\\circ", "\\cong", "\\cup", "\\div",
    "\\doteq", "\\equiv", "\\geq", "\\gg", "\\intersect", "\\union", "\\land", "\\leq", "\\ll", "\\lor", "\\o", "\\odot",
    "\\ominus", "\\oplus", "\\oslash", "\\otimes", "\\prec", "\\preceq", "\\propto", "\\sim", "\\simeq", "\\sqcap", "\\sqcup",
    "\\sqsubset", "\\sqsupset", "\\sqsubseteq", "\\sqsupseteq", "\\star", "\\subset", "\\subseteq", "\\succ", "\\succeq",
    "\\supset", "\\supseteq", "\\uplus", "\\wr", "\\", "~>", "=>", "=<", "=|", "##", "#", "^^", "^", "--", "-|", "-+->", "**",
    "*", "++", "+", "<=>", "<:", "<=", "<", ">=", ">", "...", "..", "||", "|", "|-", "|=", "&&", "&", "$$", "$", "??", "%%",
    "%", "@@", "!!", ":>", ":=", "::=", "(+)", "(-)", "(.)", "(/)", "(\\X)", "\\notin", "≈", "≔", "≍", "◯", "⩴", "●", "∩", "⋅",
    "∘", "≅", "∪", "÷", "≐", "‥", "…", "≡", "‼", "≥", "≫", "⇔", "⇒", "⫤", "↝", "≤", "≪", "⊣", "≠", "∉", "⊙", "⊖", "⊕", "⊘",
    "⊗", "⇸", "≺", "⪯", "∝", "⁇", "⊨", "⊢", "∼", "≃", "⊓", "⊔", "⊏", "⊑", "⊐", "⊒", "⋆", "⊂", "⊆", "≻", "⪰", "⊃", "⊇", "×",
    "⊎", "‖", "≀", "\\times", "\\X",
];

/// All fixed-spelling tokens, longest spellings first (for longest-match lookup).
struct Fixed {
    /// by first char: candidate spellings sorted by length descending
    table: std::collections::HashMap<char, Vec<(&'static str, Tk)>>,
}

fn build_fixed() -> Fixed {
    const KEYWORDS: &[&str] = &[
        "ACTION", "ACTIONS", "ASSUME", "[]ASSUME", "ASSUMPTION", "AXIOM", "CASE", "CHOOSE", "CONSTANT", "CONSTANTS", "ELSE", "EXCEPT",
        "\\E", "\\exists", "∃", "EXTENDS", "\\A", "\\forall", "∀", "IF", "INSTANCE", "LET", "IN", "LOCAL", "MODULE", "NEW", "OTHER",
        "PROPOSITION", "LEMMA", "COROLLARY", "SF_", "\\EE", "\\AA", "THEN", "BY", "ONLY", "DEFINE", "DEF", "DEFS", "THEOREM", "USE",
        "HIDE", "HAVE", "OBVIOUS", "OMITTED", "LAMBDA", "TAKE", "PROOF", "PROVE", "[]PROVE", "QED", "RECURSIVE", "STATE", "TEMPORAL",
        "TEMPORALS", "PICK", "WITNESS", "SUFFICES", "VARIABLE", "VARIABLES", "WF_", "WITH", ",", ":", "::", "∷", ".", "_", "==", "≜",
        "(", ")", "-|-", "[", "]_", "]", "{", "}", "<<", "⟨", ">>_", "⟩_", ">>", "⟩", "!", "->", "→", "<-", "←", "|->", "↦",
    ];
    const OPS_EXTRA: &[&str] = &[
        "'", "^+", "⁺", "^*", "^#", "-.", "\\lnot", "¬", "\\neg", "~", "[]", "□", "<>", "◇", "ENABLED", "UNCHANGED", "SUBSET", "UNION",
        "DOMAIN", "/\\", "∧", "\\/", "∨", "\\in", "∈", "=", "-",
    ];
    let mut table: std::collections::HashMap<char, Vec<(&'static str, Tk)>> = Default::default();
    for s in KEYWORDS {
        table.entry(s.chars().next().unwrap()).or_default().push((s, kw(s).unwrap()));
    }
    for s in OPS_EXTRA.iter().chain(INFIX_OPS.iter()) {
        table.entry(s.chars().next().unwrap()).or_default().push((s, op_kind(s).unwrap()));
    }
    for v in table.values_mut() {
        v.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
    }
    Fixed { table }
}

thread_local! {
    static FIXED: Fixed = build_fixed();
}

pub struct LexError {
    pub msg: String,
    pub line: u32,
    pub col: u32,
}

fn is_letter(c: char) -> bool {
    c.is_ascii_alphabetic()
}
fn is_digit(c: char) -> bool {
    c.is_ascii_digit()
}

struct Lexer<'a> {
    chars: Vec<char>,
    // position (line, col) *after* each char index i (col of the char at i is cols[i])
    lines: Vec<u32>,
    cols: Vec<u32>,
    pos: usize,
    src: &'a str,
}

/// Compute line/col of every char exactly like `SimpleCharStream.UpdateLineColumn`.
fn positions(chars: &[char]) -> (Vec<u32>, Vec<u32>) {
    let mut lines = Vec::with_capacity(chars.len());
    let mut cols = Vec::with_capacity(chars.len());
    let (mut line, mut col) = (1u32, 0u32);
    let (mut prev_lf, mut prev_cr) = (false, false);
    for &c in chars {
        col += 1;
        if prev_lf {
            prev_lf = false;
            col = 1;
            line += 1;
        } else if prev_cr {
            prev_cr = false;
            if c == '\n' {
                prev_lf = true;
            } else {
                col = 1;
                line += 1;
            }
        }
        match c {
            '\r' => prev_cr = true,
            '\n' => prev_lf = true,
            '\t' => {
                col -= 1;
                col += 8 - (col % 8);
            }
            _ => {}
        }
        lines.push(line);
        cols.push(col);
    }
    (lines, cols)
}

impl<'a> Lexer<'a> {
    fn at(&self, i: usize) -> Option<char> {
        self.chars.get(i).copied()
    }
    fn starts_with(&self, i: usize, s: &str) -> bool {
        let mut j = i;
        for c in s.chars() {
            if self.at(j) != Some(c) {
                return false;
            }
            j += 1;
        }
        true
    }

    /// Longest identifier-regex match at `i` (length in chars; 0 if none).
    fn ident_len(&self, i: usize) -> usize {
        let c0 = match self.at(i) {
            Some(c) => c,
            None => return 0,
        };
        if c0 == '@' {
            return 1;
        }
        if c0 == 'ℕ' || c0 == 'ℤ' || c0 == 'ℝ' {
            return 1;
        }
        // maximal run of [A-Za-z0-9_]
        let mut j = i;
        while let Some(c) = self.at(j) {
            if is_letter(c) || is_digit(c) || c == '_' {
                j += 1;
            } else {
                break;
            }
        }
        let run: Vec<char> = self.chars[i..j].to_vec();
        if run.is_empty() {
            return 0;
        }
        let has_letter = run.iter().any(|&c| is_letter(c));
        let mut best = 0usize;
        // CASE0: "_" (L|_|D)* L (L|_|D)*  /  CASE1, CASEN: D (L|_|D)* L (L|_|D)*
        if (run[0] == '_' || is_digit(run[0])) && has_letter {
            best = run.len();
        }
        // CASE6 : [a-zA-Z minus S,W] (L|_|D)*
        if is_letter(run[0]) && run[0] != 'S' && run[0] != 'W' {
            best = run.len();
        }
        // CASE2 : (W|S) ( ([a-zA-Z minus F] | "_" | D) (L|_|D)* )?
        if run[0] == 'W' || run[0] == 'S' {
            if run.len() == 1 {
                best = best.max(1);
            } else {
                let c1 = run[1];
                let ok1 = (is_letter(c1) && c1 != 'F') || c1 == '_' || is_digit(c1);
                if ok1 {
                    best = best.max(run.len());
                } else {
                    best = best.max(1); // just "W"/"S"
                }
                // CASE3 : ("WF"|"SF") ( (L|D) (L|_|D)* )?
                if c1 == 'F' {
                    if run.len() == 2 {
                        best = best.max(2);
                    } else {
                        let c2 = run[2];
                        if is_letter(c2) || is_digit(c2) {
                            best = best.max(run.len());
                        } else {
                            best = best.max(2);
                        }
                    }
                }
            }
        }
        best
    }

    /// number literal length
    fn number_len(&self, i: usize) -> usize {
        let c = match self.at(i) {
            Some(c) => c,
            None => return 0,
        };
        if is_digit(c) {
            let mut j = i;
            while self.at(j).map_or(false, is_digit) {
                j += 1;
            }
            return j - i;
        }
        if c == '\\' {
            if let Some(k) = self.at(i + 1) {
                let pred: Option<fn(char) -> bool> = match k {
                    'o' | 'O' => Some(|c: char| ('0'..='7').contains(&c)),
                    'b' | 'B' => Some(|c: char| c == '0' || c == '1'),
                    'h' | 'H' => Some(|c: char| c.is_ascii_hexdigit()),
                    _ => None,
                };
                if let Some(p) = pred {
                    let mut j = i + 2;
                    while self.at(j).map_or(false, p) {
                        j += 1;
                    }
                    if j > i + 2 {
                        return j - i;
                    }
                }
            }
        }
        0
    }

    /// proof-step lexemes starting with '<'; returns (len, kind)
    fn step_lexeme(&self, i: usize) -> Option<(usize, Tk)> {
        if self.at(i) != Some('<') {
            return None;
        }
        let mut j = i + 1;
        let lvl_start = j;
        let c = self.at(j)?;
        let numeric;
        if is_digit(c) {
            while self.at(j).map_or(false, is_digit) {
                j += 1;
            }
            numeric = true;
        } else if c == '+' || c == '*' {
            j += 1;
            numeric = false;
        } else {
            return None;
        }
        let _ = lvl_start;
        if self.at(j) != Some('>') {
            return None;
        }
        j += 1;
        let after_gt = j;
        // candidates (longest wins)
        let mut best_len = after_gt - i;
        let mut best = Tk::BareLevelLexeme;
        // UnnumberedStepLexeme: ( "*" (".")* | "-" (".")* | (".")+ )
        {
            let mut k = after_gt;
            let mut ok = false;
            match self.at(k) {
                Some('*') | Some('-') => {
                    k += 1;
                    while self.at(k) == Some('.') {
                        k += 1;
                    }
                    ok = true;
                }
                Some('.') => {
                    while self.at(k) == Some('.') {
                        k += 1;
                    }
                    ok = true;
                }
                _ => {}
            }
            if ok && k - i > best_len {
                best_len = k - i;
                best = Tk::UnnumberedStepLexeme;
            }
        }
        // ProofStepLexeme / ProofStepDotLexeme / ProofImplicitStepLexeme
        {
            let mut k = after_gt;
            let allow_us = numeric;
            while let Some(ch) = self.at(k) {
                if is_letter(ch) || is_digit(ch) || (allow_us && ch == '_') {
                    k += 1;
                } else {
                    break;
                }
            }
            if k > after_gt {
                let base_kind = if numeric { Tk::ProofStepLexeme } else { Tk::ProofImplicitStepLexeme };
                if k - i > best_len || (k - i == best_len && false) {
                    best_len = k - i;
                    best = base_kind;
                }
                // dot lexeme: step + (DOT)+  (also for implicit kinds: ProofStepDotLexeme allows + and *)
                let mut m = k;
                if !numeric {
                    // ProofStepDotLexeme allows (L|D|_)+ after '>' for +/* too
                    let mut k2 = after_gt;
                    while let Some(ch) = self.at(k2) {
                        if is_letter(ch) || is_digit(ch) || ch == '_' {
                            k2 += 1;
                        } else {
                            break;
                        }
                    }
                    m = k2;
                }
                let mut d = m;
                while self.at(d) == Some('.') {
                    d += 1;
                }
                if d > m && d - i > best_len {
                    best_len = d - i;
                    best = Tk::ProofStepDotLexeme;
                }
            } else if !numeric {
                // nothing
            }
        }
        Some((best_len, best))
    }

    fn string_len(&self, i: usize) -> Option<usize> {
        if self.at(i) != Some('"') {
            return None;
        }
        let mut j = i + 1;
        loop {
            match self.at(j) {
                None => return None,
                Some('"') => return Some(j + 1 - i),
                Some('\n') | Some('\r') => return None,
                Some('\\') => match self.at(j + 1) {
                    Some('n') | Some('t') | Some('r') | Some('f') | Some('\\') | Some('"') => j += 2,
                    _ => return None,
                },
                Some(_) => j += 1,
            }
        }
    }

    fn fixed_match(&self, i: usize) -> Option<(usize, Tk)> {
        let c = self.at(i)?;
        FIXED.with(|f| {
            if let Some(v) = f.table.get(&c) {
                for (s, k) in v {
                    if self.starts_with(i, s) {
                        return Some((s.chars().count(), *k));
                    }
                }
            }
            None
        })
    }

    /// `----+ (spaces) MODULE` at i (BEGIN_MODULE); returns length
    fn begin_module_len(&self, i: usize) -> Option<usize> {
        if !self.starts_with(i, "----") {
            return None;
        }
        let mut j = i + 4;
        while self.at(j) == Some('-') {
            j += 1;
        }
        while self.at(j) == Some(' ') {
            j += 1;
        }
        if self.starts_with(j, "MODULE") {
            Some(j + 6 - i)
        } else {
            None
        }
    }

    fn make(&self, kind: Tk, start: usize, len: usize) -> Token {
        let end = start + len - 1;
        let image: String = self.chars[start..start + len].iter().collect();
        Token { kind, image: image.into(), bl: self.lines[start], bc: self.cols[start], el: self.lines[end], ec: self.cols[end] }
    }
}

/// Tokenize a module source. Returns the tokens up to and including the final top-level `====` (nesting-aware),
/// followed by an `Eof` token; or up to a lexical error (an `Error` token followed by Eof).
/// `src` text before the first `---- MODULE` is skipped (DEFAULT lexical state).
pub fn tokenize(src: &str) -> Vec<Token> {
    let chars: Vec<char> = src.chars().collect();
    let (lines, cols) = positions(&chars);
    let lx = Lexer { chars, lines, cols, pos: 0, src };
    let _ = lx.src;
    let mut out: Vec<Token> = Vec::new();
    let n = lx.chars.len();
    let mut i = 0usize;
    // DEFAULT state: skip to BEGIN_MODULE
    let mut started = false;
    while i < n {
        if let Some(len) = lx.begin_module_len(i) {
            out.push(lx.make(Tk::BeginModule, i, len));
            i += len;
            started = true;
            break;
        }
        i += 1;
    }
    let _ = lx.pos;
    if !started {
        out.push(eof_token(&lx));
        return out;
    }
    let mut depth = 1i32;
    while i < n {
        let c = lx.chars[i];
        // whitespace
        if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
            i += 1;
            continue;
        }
        // comments
        if lx.starts_with(i, "(*") {
            // nested block comment
            let start = i;
            let mut d = 0i32;
            let mut j = i;
            let mut closed = false;
            while j < n {
                if lx.starts_with(j, "(*") {
                    d += 1;
                    j += 2;
                } else if lx.starts_with(j, "*)") {
                    d -= 1;
                    j += 2;
                    if d == 0 {
                        closed = true;
                        break;
                    }
                } else {
                    j += 1;
                }
            }
            if !closed {
                let msg = format!(
                    "Lexical error at line {}, column {}.  Encountered: <EOF> after : \"\"",
                    lx.lines[start], lx.cols[start]
                );
                let mut t = lx.make(Tk::Error, start, 1);
                t.image = format!("Lexical {{error: EOF reached, possibly open comment starting around line {}", lx.lines[start]).into();
                let _ = msg;
                out.push(t);
                out.push(eof_token(&lx));
                return out;
            }
            i = j;
            continue;
        }
        if lx.starts_with(i, "\\*") {
            while i < n && lx.chars[i] != '\n' && lx.chars[i] != '\r' {
                i += 1;
            }
            continue;
        }
        // candidates
        let mut best_len = 0usize;
        let mut best_kind = Tk::Error;
        let mut consider = |len: usize, kind: Tk| {
            if len > best_len {
                best_len = len;
                best_kind = kind;
            }
        };
        // order of declaration for ties: fixed tokens (keywords/punct) first, then literals, then ops, then ident
        if let Some(len) = lx.begin_module_len(i) {
            consider(len, Tk::BeginModule);
        }
        if lx.starts_with(i, "----") {
            let mut j = i + 4;
            while lx.at(j) == Some('-') {
                j += 1;
            }
            consider(j - i, Tk::Separator);
        }
        if lx.starts_with(i, "====") {
            let mut j = i + 4;
            while lx.at(j) == Some('=') {
                j += 1;
            }
            consider(j - i, Tk::EndModule);
        }
        if let Some((len, k)) = lx.fixed_match(i) {
            consider(len, k);
        }
        let nl = lx.number_len(i);
        if nl > 0 {
            consider(nl, Tk::NumberLiteral);
        }
        if let Some(len) = lx.string_len(i) {
            consider(len, Tk::StringLiteral);
        }
        let il = lx.ident_len(i);
        if il > 0 {
            consider(il, Tk::Identifier);
        }
        if let Some((len, k)) = lx.step_lexeme(i) {
            consider(len, k);
        }
        if best_len == 0 {
            // lexical error
            let mut t = lx.make(Tk::Error, i, 1);
            t.image = format!(
                "Lexical error at line {}, column {}.  Encountered: {} (0x{:x}), after : \"\"",
                lx.lines[i],
                lx.cols[i],
                if c.is_control() { format!("{:?}", c) } else { format!("\"{}\"", c) },
                c as u32
            )
            .into();
            out.push(t);
            out.push(eof_token(&lx));
            return out;
        }
        let tok = lx.make(best_kind, i, best_len);
        i += best_len;
        match best_kind {
            Tk::BeginModule => depth += 1,
            Tk::EndModule => {
                depth -= 1;
                out.push(tok);
                if depth <= 0 {
                    out.push(eof_token(&lx));
                    return out;
                }
                continue;
            }
            _ => {}
        }
        out.push(tok);
    }
    out.push(eof_token(&lx));
    out
}

fn eof_token(lx: &Lexer) -> Token {
    let n = lx.chars.len();
    let (l, c) = if n > 0 { (lx.lines[n - 1], lx.cols[n - 1] + 1) } else { (1, 1) };
    Token { kind: Tk::Eof, image: "".into(), bl: l, bc: c, el: l, ec: c }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(s: &str) -> Vec<(Tk, String)> {
        tokenize(s).into_iter().map(|t| (t.kind, t.image.to_string())).collect()
    }

    #[test]
    fn basic_module() {
        let k = kinds("---- MODULE M ----\nVARIABLE x\nA == x' = x + 1\n====\n");
        assert_eq!(k[0].0, Tk::BeginModule);
        assert_eq!(k[1], (Tk::Identifier, "M".into()));
        assert_eq!(k[2].0, Tk::Separator);
        assert_eq!(k[3].0, Tk::Variable);
        assert!(k.iter().any(|(t, i)| *t == Tk::Postfix && i == "'"));
        assert_eq!(k.last().unwrap().0, Tk::Eof);
        assert_eq!(k[k.len() - 2].0, Tk::EndModule);
    }

    #[test]
    fn fairness_and_idents() {
        let k = kinds("---- MODULE M ----\nWF_vars(A) W_x WFx SF_y S Wa\n====\n");
        let v: Vec<_> = k.iter().map(|(t, i)| (*t, i.as_str())).collect();
        assert!(v.contains(&(Tk::Wf, "WF_")));
        assert!(v.contains(&(Tk::Identifier, "W_x")));
        assert!(v.contains(&(Tk::Identifier, "WFx")));
        assert!(v.contains(&(Tk::Sf, "SF_")));
        assert!(v.contains(&(Tk::Identifier, "S")));
    }

    #[test]
    fn comments_and_positions() {
        let toks = tokenize("---- MODULE M ----\n(* a (* b *) c *)\n\\* line\nx\t== 1\n====\n");
        let x = toks.iter().find(|t| &*t.image == "x").unwrap();
        assert_eq!((x.bl, x.bc), (4, 1));
        let def = toks.iter().find(|t| t.kind == Tk::Def).unwrap();
        assert_eq!(def.bc, 9); // tab stop of 8
    }

    #[test]
    fn step_lexemes() {
        let k = kinds("---- MODULE M ----\n<1>2. <2>a <3>. <*>b <1>\n====\n");
        let v: Vec<_> = k.iter().map(|(t, _)| *t).collect();
        assert!(v.contains(&Tk::ProofStepDotLexeme));
        assert!(v.contains(&Tk::ProofStepLexeme));
        assert!(v.contains(&Tk::UnnumberedStepLexeme));
        assert!(v.contains(&Tk::ProofImplicitStepLexeme));
        assert!(v.contains(&Tk::BareLevelLexeme));
    }

    #[test]
    fn ops_longest_match() {
        let k = kinds("---- MODULE M ----\na \\in b \\intersect c \\notin d <= e /\\ f \\/ g [] h => i ~> j\n====\n");
        let imgs: Vec<_> = k.iter().map(|(_, i)| i.as_str()).collect();
        assert!(imgs.contains(&"\\intersect"));
        assert!(imgs.contains(&"\\notin"));
        assert!(imgs.contains(&"~>"));
    }
}
