//! Port of `tlc2.pprint.{PrettyPrint,Parse,Format,Node}`: the pretty printer TLC applies to the flat text of values
//! (`Values.ppr`) when printing states and `Print` output. Width is `tlc2.value.Values.width` = 80.

pub const WIDTH: usize = 80;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Constant,
    Set,
    Sequence,
    Record,
    RecordPair,
    Function,
    FunctionPair,
    Subset,
}

struct Node {
    kind: Kind,
    first: usize,
    last: usize,
    children: Vec<Node>,
}

impl Node {
    fn length(&self) -> usize {
        self.last - self.first + 1
    }
}

struct Parser<'a> {
    s: &'a [char],
}

type PR<T> = Result<T, ()>;

impl<'a> Parser<'a> {
    fn at(&self, i: usize) -> PR<char> {
        self.s.get(i).copied().ok_or(())
    }

    fn skip_ws(&self, mut i: usize) -> PR<usize> {
        loop {
            let c = self.at(i)?;
            if c.is_whitespace() {
                i += 1;
            } else {
                return Ok(i);
            }
        }
    }

    fn matches(&self, i: usize, t: &str) -> bool {
        let mut k = i;
        for c in t.chars() {
            if self.s.get(k) != Some(&c) {
                return false;
            }
            k += 1;
        }
        true
    }

    fn parse(&self, index: usize) -> PR<Node> {
        if self.s.is_empty() || index >= self.s.len() {
            return Err(());
        }
        let index = self.skip_ws(index)?;
        match self.at(index)? {
            '{' => self.parse_list(index, Kind::Set, '{', '}', false),
            '<' => self.parse_list(index, Kind::Sequence, '<', '>', false),
            '[' => self.parse_list(index, Kind::Record, '[', ']', true),
            '(' => self.parse_function(index),
            _ => {
                if self.matches(index, "SUBSET") {
                    return self.parse_subset(index);
                }
                self.parse_constant(index)
            }
        }
    }

    fn parse_list(&self, index: usize, kind: Kind, open: char, close: char, pairs: bool) -> PR<Node> {
        let _ = open;
        let mut last = index;
        let mut children = vec![];
        last += if kind == Kind::Sequence { 2 } else { 1 };
        last = self.skip_ws(last)?;
        while self.at(last)? != close {
            let elt = if pairs { self.parse_record_pair(last)? } else { self.parse(last)? };
            last = elt.last + 1;
            children.push(elt);
            last = self.skip_ws(last)?;
            if self.at(last)? == ',' {
                last += 1;
            }
            last = self.skip_ws(last)?;
        }
        if kind == Kind::Sequence {
            last += 1;
        }
        Ok(Node { kind, first: index, last, children })
    }

    fn parse_record_pair(&self, index: usize) -> PR<Node> {
        let field = self.parse(index)?;
        let mut last = field.last + 1;
        last = self.skip_ws(last)?;
        if !self.matches(last, "|->") {
            return Err(());
        }
        last += 3;
        last = self.skip_ws(last)?;
        let value = self.parse(last)?;
        let l = value.last;
        Ok(Node { kind: Kind::RecordPair, first: index, last: l, children: vec![field, value] })
    }

    fn parse_function(&self, index: usize) -> PR<Node> {
        let mut last = index + 1;
        let mut children = vec![];
        last = self.skip_ws(last)?;
        while self.at(last)? != ')' {
            let pair = self.parse_function_pair(last)?;
            last = pair.last + 1;
            children.push(pair);
            last = self.skip_ws(last)?;
            if self.matches(last, "@@") {
                last += 2;
            }
            last = self.skip_ws(last)?;
        }
        Ok(Node { kind: Kind::Function, first: index, last, children })
    }

    fn parse_function_pair(&self, index: usize) -> PR<Node> {
        let domain = self.parse(index)?;
        let mut last = domain.last + 1;
        last = self.skip_ws(last)?;
        if !self.matches(last, ":>") {
            return Err(());
        }
        last += 2;
        last = self.skip_ws(last)?;
        let range = self.parse(last)?;
        let l = range.last;
        Ok(Node { kind: Kind::FunctionPair, first: index, last: l, children: vec![domain, range] })
    }

    fn parse_subset(&self, index: usize) -> PR<Node> {
        let mut last = index + 6;
        last = self.skip_ws(last)?;
        let elt = self.parse(last)?;
        let l = elt.last;
        Ok(Node { kind: Kind::Subset, first: index, last: l, children: vec![elt] })
    }

    fn parse_constant(&self, index: usize) -> PR<Node> {
        let first = self.skip_ws(index)?;
        let mut last = first;
        if self.at(first)? == '"' {
            loop {
                last += 1;
                if self.at(last)? == '"' {
                    break;
                }
            }
            return Ok(Node { kind: Kind::Constant, first, last, children: vec![] });
        }
        if self.at(last)?.is_ascii_digit() {
            if let Some(n) = self.parse_interval(index) {
                return Ok(n);
            }
        }
        if self.at(last)? == '-' {
            last += 1;
            while self.at(last)?.is_ascii_digit() {
                last += 1;
                if last == self.s.len() {
                    break;
                }
            }
            last -= 1;
            return Ok(Node { kind: Kind::Constant, first, last, children: vec![] });
        }
        if self.at(last)?.is_alphanumeric() {
            while self.at(last)?.is_alphanumeric() {
                last += 1;
                if last == self.s.len() {
                    break;
                }
            }
            last -= 1;
            return Ok(Node { kind: Kind::Constant, first, last, children: vec![] });
        }
        Err(())
    }

    fn parse_interval(&self, index: usize) -> Option<Node> {
        let first = index;
        let mut last = first;
        if !self.at(last).ok()?.is_ascii_digit() {
            return None;
        }
        while last < self.s.len() && self.s[last].is_ascii_digit() {
            last += 1;
        }
        if !self.matches(last, "..") {
            return None;
        }
        last += 2;
        if !self.at(last).ok()?.is_ascii_digit() {
            return None;
        }
        while self.at(last).ok()?.is_ascii_digit() {
            last += 1;
            if last == self.s.len() {
                break;
            }
        }
        last -= 1;
        Some(Node { kind: Kind::Constant, first, last, children: vec![] })
    }
}

struct Fmt<'a> {
    s: &'a [char],
}

impl<'a> Fmt<'a> {
    fn value(&self, n: &Node) -> String {
        self.s[n.first..=n.last].iter().collect()
    }

    fn format(&self, n: &Node, width: i64, trailer: i64, pad: &str) -> String {
        if n.length() as i64 <= width - trailer {
            return self.value(n);
        }
        match n.kind {
            Kind::Constant => self.value(n),
            Kind::Set => self.simple(n, width, trailer, pad, "{ ", " }", "  ", ","),
            Kind::Sequence => self.simple(n, width, trailer, pad, "<< ", " >>", "   ", ","),
            Kind::Function => self.pair(n, width, trailer, pad, "( ", " )", "  ", " @@", " :>", "    "),
            Kind::Record => self.pair(n, width, trailer, pad, "[ ", " ]", "  ", ",", " |->", "    "),
            Kind::Subset => self.simple(n, width, trailer, pad, "SUBSET ", " ", " ", ","),
            _ => self.value(n),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn simple(&self, n: &Node, width: i64, trailer: i64, pad: &str, open: &str, close: &str, p: &str, sep: &str) -> String {
        let w = width - open.len().max(p.len()) as i64;
        let t = trailer + close.len() as i64;
        let lp = format!("{}{}", pad, p);
        let mut out = String::from(open);
        let cnt = n.children.len();
        for (i, v) in n.children.iter().enumerate() {
            if i + 1 < cnt {
                out.push_str(&self.format(v, w, sep.len() as i64, &lp));
                out.push_str(sep);
                out.push('\n');
                out.push_str(&lp);
            } else {
                out.push_str(&self.format(v, w, t, &lp));
            }
        }
        out.push_str(close);
        out
    }

    #[allow(clippy::too_many_arguments)]
    fn pair(&self, n: &Node, width: i64, trailer: i64, pad: &str, open: &str, close: &str, p: &str, sep: &str, div: &str, divpad: &str) -> String {
        let w = width - open.len().max(p.len()) as i64;
        let t = trailer + close.len() as i64;
        let lp = format!("{}{}", pad, p);
        let mut out = String::from(open);
        let cnt = n.children.len();
        for (i, pr) in n.children.iter().enumerate() {
            let arg = &pr.children[0];
            let val = &pr.children[1];
            let (al, vl, dl, sl) = (arg.length() as i64, val.length() as i64, div.len() as i64, sep.len() as i64);
            if i + 1 < cnt {
                if al + dl + 1 + vl + sl <= w {
                    out.push_str(&format!("{}{} {}{}\n{}", self.value(arg), div, self.value(val), sep, lp));
                    continue;
                }
                if al + dl <= w {
                    let lp2 = format!("{}{}", lp, divpad);
                    out.push_str(&format!(
                        "{}{}\n{}{}{}{}\n{}",
                        self.value(arg),
                        div,
                        lp,
                        divpad,
                        self.format(val, w - divpad.len() as i64, sl, &lp2),
                        sep,
                        lp
                    ));
                    continue;
                }
                let lp2 = format!("{}{}", lp, divpad);
                out.push_str(&format!(
                    "{}{}\n{}{}{}{}\n{}",
                    self.format(arg, w, t + dl, &lp),
                    div,
                    lp,
                    divpad,
                    self.format(val, w - divpad.len() as i64, sl, &lp2),
                    sep,
                    lp
                ));
                continue;
            }
            if al + dl + 1 + vl <= w - t {
                out.push_str(&format!("{}{} {}", self.value(arg), div, self.value(val)));
                continue;
            }
            let lp2 = format!("{}{}", lp, divpad);
            if al + dl <= w {
                out.push_str(&format!(
                    "{}{}\n{}{}{}",
                    self.value(arg),
                    div,
                    lp,
                    divpad,
                    self.format(val, w - divpad.len() as i64, t, &lp2)
                ));
                continue;
            }
            out.push_str(&format!(
                "{}{}\n{}{}{}",
                self.format(arg, w, t + dl, &lp),
                div,
                lp,
                divpad,
                self.format(val, w - divpad.len() as i64, t, &lp2)
            ));
        }
        out.push_str(close);
        out
    }
}

/// `PrettyPrint.mypp(value, width)`
pub fn mypp(value: &str, width: usize) -> String {
    let chars: Vec<char> = value.chars().collect();
    let p = Parser { s: &chars };
    match p.parse(0) {
        Ok(tree) => {
            if tree.last + 1 < chars.len() {
                return value.to_string();
            }
            let f = Fmt { s: &chars };
            f.format(&tree, width as i64, 0, "")
        }
        Err(()) => value.to_string(),
    }
}

/// `Values.ppr(String)`
pub fn ppr(value: &str) -> String {
    mypp(value, WIDTH)
}
