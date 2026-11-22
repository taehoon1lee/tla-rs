//! Port of `tla2sany/parser/{Operator,Operators}.java`: precedence ranges, associativity, fixity, synonyms.

use std::collections::HashMap;
use std::sync::OnceLock;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Assoc {
    None,
    Left,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fix {
    Nofix,
    Prefix,
    Postfix,
    Infix,
    Nfix,
}

#[derive(Debug)]
pub struct Operator {
    pub id: &'static str,
    pub low: i32,
    pub high: i32,
    pub assoc: Assoc,
    pub fix: Fix,
}

impl Operator {
    pub fn is_prefix(&self) -> bool {
        self.fix == Fix::Prefix
    }
    pub fn is_infix(&self) -> bool {
        self.fix == Fix::Infix || self.fix == Fix::Nfix
    }
    pub fn is_postfix(&self) -> bool {
        self.fix == Fix::Postfix
    }
    pub fn is_nfix(&self) -> bool {
        self.fix == Fix::Nfix
    }
    pub fn assoc_left(&self) -> bool {
        self.assoc == Assoc::Left
    }
    pub fn assoc_right(&self) -> bool {
        self.assoc == Assoc::Right
    }
    /// `succ(left, right)`
    pub fn succ(left: &Operator, right: &Operator) -> bool {
        left.low > right.high
    }
    /// `prec(left, right)`
    pub fn prec(left: &Operator, right: &Operator) -> bool {
        left.high < right.low
    }
}

use Assoc::{Left as L, None as N};
use Fix::{Infix as I, Nfix as NF, Postfix as PO, Prefix as PR};

const CANON: &[(&str, i32, i32, Assoc, Fix)] = &[
    ("[", 160, 160, L, PO),
    (".", 170, 170, L, I),
    ("'", 150, 150, N, PO),
    ("^", 140, 140, N, I),
    ("/", 130, 130, N, I),
    ("*", 130, 130, L, I),
    ("-", 110, 110, L, I),
    ("-.", 120, 120, N, PR),
    ("+", 100, 100, L, I),
    ("=", 50, 50, N, I),
    ("\\lnot", 40, 40, L, PR),
    ("\\land", 30, 30, L, I),
    ("\\lor", 30, 30, L, I),
    ("~>", 20, 20, N, I),
    ("=>", 10, 10, N, I),
    ("[]", 40, 150, N, PR),
    ("<>", 40, 150, N, PR),
    ("ENABLED", 40, 150, N, PR),
    ("UNCHANGED", 40, 150, N, PR),
    ("SUBSET", 80, 80, N, PR),
    ("UNION", 80, 80, N, PR),
    ("DOMAIN", 90, 90, N, PR),
    ("^+", 150, 150, N, PO),
    ("^*", 150, 150, N, PO),
    ("^#", 150, 150, N, PO),
    ("\\cdot", 50, 140, L, I),
    ("\\equiv", 20, 20, N, I),
    ("-+->", 20, 20, N, I),
    ("/=", 50, 50, N, I),
    ("\\subseteq", 50, 50, N, I),
    ("\\in", 50, 50, N, I),
    ("\\notin", 50, 50, N, I),
    ("<", 50, 50, N, I),
    ("\\leq", 50, 50, N, I),
    (">", 50, 50, N, I),
    ("\\geq", 50, 50, N, I),
    ("\\times", 100, 130, L, NF),
    ("\\", 80, 80, N, I),
    ("\\intersect", 80, 80, L, I),
    ("\\union", 80, 80, L, I),
    ("...", 90, 90, N, I),
    ("..", 90, 90, N, I),
    ("|", 100, 110, L, I),
    ("||", 100, 110, L, I),
    ("&&", 130, 130, L, I),
    ("&", 130, 130, L, I),
    ("$$", 90, 130, L, I),
    ("$", 90, 130, L, I),
    ("??", 90, 130, L, I),
    ("%%", 100, 110, L, I),
    ("%", 100, 110, N, I),
    ("##", 90, 130, L, I),
    ("++", 100, 100, L, I),
    ("--", 110, 110, L, I),
    ("**", 130, 130, L, I),
    ("//", 130, 130, N, I),
    ("^^", 140, 140, N, I),
    ("@@", 60, 60, L, I),
    ("!!", 90, 130, N, I),
    ("|-", 50, 50, N, I),
    ("|=", 50, 50, N, I),
    ("-|", 50, 50, N, I),
    ("=|", 50, 50, N, I),
    ("<:", 70, 70, N, I),
    (":>", 70, 70, N, I),
    (":=", 50, 50, N, I),
    ("::=", 50, 50, N, I),
    ("\\oplus", 100, 100, L, I),
    ("\\ominus", 110, 110, L, I),
    ("\\odot", 130, 130, L, I),
    ("\\oslash", 130, 130, N, I),
    ("\\otimes", 130, 130, L, I),
    ("\\uplus", 90, 130, L, I),
    ("\\sqcap", 90, 130, L, I),
    ("\\sqcup", 90, 130, L, I),
    ("\\div", 130, 130, N, I),
    ("\\wr", 90, 140, N, I),
    ("\\star", 130, 130, L, I),
    ("\\o", 130, 130, L, I),
    ("\\bigcirc", 130, 130, L, I),
    ("\\bullet", 130, 130, L, I),
    ("\\prec", 50, 50, N, I),
    ("\\succ", 50, 50, N, I),
    ("\\preceq", 50, 50, N, I),
    ("\\succeq", 50, 50, N, I),
    ("\\sim", 50, 50, N, I),
    ("\\simeq", 50, 50, N, I),
    ("\\ll", 50, 50, N, I),
    ("\\gg", 50, 50, N, I),
    ("\\asymp", 50, 50, N, I),
    ("\\subset", 50, 50, N, I),
    ("\\supset", 50, 50, N, I),
    ("\\supseteq", 50, 50, N, I),
    ("\\approx", 50, 50, N, I),
    ("\\cong", 50, 50, N, I),
    ("\\sqsubset", 50, 50, N, I),
    ("\\sqsubseteq", 50, 50, N, I),
    ("\\sqsupset", 50, 50, N, I),
    ("\\sqsupseteq", 50, 50, N, I),
    ("\\doteq", 50, 50, N, I),
    ("\\propto", 50, 50, N, I),
];

const SYNONYMS: &[&[&str]] = &[
    &["\\lnot", "~", "\\neg", "¬"],
    &["[]", "□"],
    &["<>", "◇"],
    &["\\land", "/\\", "∧"],
    &["\\lor", "\\/", "∨"],
    &["\\equiv", "<=>", "≡", "⇔"],
    &["/=", "#", "≠"],
    &["\\leq", "<=", "=<", "≤"],
    &["\\geq", ">=", "≥"],
    &["\\times", "\\X", "×"],
    &["\\intersect", "\\cap", "∩"],
    &["\\union", "\\cup", "∪"],
    &["\\o", "\\circ", "∘"],
    &["\\oplus", "(+)", "⊕"],
    &["\\ominus", "(-)", "⊖"],
    &["\\odot", "(.)", "⊙"],
    &["\\oslash", "(/)", "⊘"],
    &["\\otimes", "(\\X)", "⊗"],
    &["\\approx", "≈"],
    &[":=", "≔"],
    &["\\asymp", "≍"],
    &["\\bigcirc", "◯"],
    &["::=", "⩴"],
    &["\\bullet", "●"],
    &["\\cdot", "⋅"],
    &["\\cong", "≅"],
    &["\\div", "÷"],
    &["\\doteq", "≐"],
    &["..", "‥"],
    &["...", "…"],
    &["!!", "‼"],
    &["\\gg", "≫"],
    &["=>", "⇒"],
    &["\\in", "∈"],
    &["=|", "⫤"],
    &["~>", "↝"],
    &["\\ll", "≪"],
    &["-|", "⊣"],
    &["\\notin", "∉"],
    &["-+->", "⇸"],
    &["\\prec", "≺"],
    &["\\preceq", "⪯"],
    &["\\propto", "∝"],
    &["??", "⁇"],
    &["|=", "⊨"],
    &["|-", "⊢"],
    &["\\sim", "∼"],
    &["\\simeq", "≃"],
    &["\\sqcap", "⊓"],
    &["\\sqcup", "⊔"],
    &["\\sqsubset", "⊏"],
    &["\\sqsubseteq", "⊑"],
    &["\\sqsupset", "⊐"],
    &["\\sqsupseteq", "⊒"],
    &["\\star", "⋆"],
    &["\\subset", "⊂"],
    &["\\subseteq", "⊆"],
    &["\\succ", "≻"],
    &["\\succeq", "⪰"],
    &["\\supset", "⊃"],
    &["\\supseteq", "⊇"],
    &["\\uplus", "⊎"],
    &["||", "‖"],
    &["\\wr", "≀"],
    &["^+", "⁺"],
];

fn table() -> &'static HashMap<&'static str, &'static Operator> {
    static T: OnceLock<HashMap<&'static str, &'static Operator>> = OnceLock::new();
    T.get_or_init(|| {
        let mut m: HashMap<&'static str, &'static Operator> = HashMap::new();
        for &(id, low, high, assoc, fix) in CANON {
            let op: &'static Operator = Box::leak(Box::new(Operator { id, low, high, assoc, fix }));
            m.insert(id, op);
        }
        for syn in SYNONYMS {
            let canon = *m.get(syn[0]).expect("canonical operator");
            for s in &syn[1..] {
                m.insert(s, canon);
            }
        }
        m
    })
}

/// Java `Operators.getOperator`
pub fn get_operator(name: &str) -> Option<&'static Operator> {
    table().get(name).copied()
}

/// Java `Operators.getMixfix`: prefix `-` -> `-.`
pub fn get_mixfix(op: &'static Operator) -> Option<&'static Operator> {
    if op.is_prefix() {
        Some(op)
    } else {
        let id = format!("{}.", op.id);
        get_operator(&id)
    }
}

/// Java `Operators.resolveSynonym`: canonical spelling of an operator symbol (unchanged if it has no entry).
pub fn resolve_synonym(name: &str) -> String {
    match get_operator(name) {
        Some(op) => op.id.to_string(),
        None => name.to_string(),
    }
}

pub fn void_operator() -> &'static Operator {
    static V: OnceLock<Operator> = OnceLock::new();
    V.get_or_init(|| Operator { id: "$$_void", low: 0, high: 0, assoc: Assoc::None, fix: Fix::Infix })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn synonyms_and_mixfix() {
        assert_eq!(resolve_synonym("/\\"), "\\land");
        assert_eq!(resolve_synonym("#"), "/=");
        assert_eq!(resolve_synonym("(+)"), "\\oplus");
        let minus = get_operator("-").unwrap();
        let mix = get_mixfix(minus).unwrap();
        assert_eq!(mix.id, "-.");
        assert!(mix.is_prefix());
        assert!(get_mixfix(get_operator("+").unwrap()).is_none());
    }
}
