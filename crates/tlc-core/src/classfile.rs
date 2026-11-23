//! Port of the loading of user module overrides (`tlc2.tool.impl.SpecProcessor.processModuleOverrides` for a class of the user's own).
//!
//! TLC loads the class named after a module from the specification's directory and replaces every operator of that module for which
//! the class has a `public static` method of the same name and arity.  There is no JVM here: the class file is read, the methods are
//! matched (and reported) exactly like Java does, and a method body is executed by a small interpreter of the bytecodes that a
//! method returning a TLC value computed from constants consists of (`getstatic BoolValue.ValTrue`, `IntValue.gen(constant)`,
//! `areturn`).  A body outside that subset is reported as not ported instead of being guessed.

use crate::value::Value;

#[derive(Clone, Debug)]
enum Cp {
    None,
    Utf8(String),
    Int(i32),
    Class(u16),
    Str(u16),
    Field(u16, u16),
    Method(u16, u16),
    NameType(u16, u16),
    Other,
}

pub struct JavaMethod {
    pub name: String,
    pub descriptor: String,
    pub access: u16,
    code: Option<Vec<u8>>,
}

pub struct JavaClass {
    pub name: String,
    cp: Vec<Cp>,
    pub methods: Vec<JavaMethod>,
}

struct Rd<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Rd<'a> {
    fn u1(&mut self) -> Option<u8> {
        let v = *self.b.get(self.p)?;
        self.p += 1;
        Some(v)
    }
    fn u2(&mut self) -> Option<u16> {
        Some(((self.u1()? as u16) << 8) | self.u1()? as u16)
    }
    fn u4(&mut self) -> Option<u32> {
        Some(((self.u2()? as u32) << 16) | self.u2()? as u32)
    }
    fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        let s = self.b.get(self.p..self.p + n)?;
        self.p += n;
        Some(s)
    }
}

/// modified UTF-8 as the class file stores it (only the plain cases are decoded)
fn decode_utf8(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

impl JavaClass {
    pub fn parse(bytes: &[u8]) -> Option<JavaClass> {
        let mut r = Rd { b: bytes, p: 0 };
        if r.u4()? != 0xCAFEBABE {
            return None;
        }
        r.u2()?;
        r.u2()?;
        let n = r.u2()? as usize;
        let mut cp = vec![Cp::None; n];
        let mut i = 1;
        while i < n {
            let tag = r.u1()?;
            cp[i] = match tag {
                1 => {
                    let len = r.u2()? as usize;
                    Cp::Utf8(decode_utf8(r.bytes(len)?))
                }
                3 => Cp::Int(r.u4()? as i32),
                4 => {
                    r.u4()?;
                    Cp::Other
                }
                5 | 6 => {
                    r.u4()?;
                    r.u4()?;
                    i += 1;
                    Cp::Other
                }
                7 => Cp::Class(r.u2()?),
                8 => Cp::Str(r.u2()?),
                9 => Cp::Field(r.u2()?, r.u2()?),
                10 | 11 => Cp::Method(r.u2()?, r.u2()?),
                12 => Cp::NameType(r.u2()?, r.u2()?),
                15 => {
                    r.u1()?;
                    r.u2()?;
                    Cp::Other
                }
                16 | 19 | 20 => {
                    r.u2()?;
                    Cp::Other
                }
                17 | 18 => {
                    r.u2()?;
                    r.u2()?;
                    Cp::Other
                }
                _ => return None,
            };
            i += 1;
        }
        let utf = |cp: &Vec<Cp>, i: u16| -> Option<String> {
            match cp.get(i as usize)? {
                Cp::Utf8(s) => Some(s.clone()),
                _ => None,
            }
        };
        r.u2()?; // access flags
        let this_class = r.u2()?;
        r.u2()?; // super class
        let ni = r.u2()? as usize;
        for _ in 0..ni {
            r.u2()?;
        }
        // fields: skipped
        let nf = r.u2()? as usize;
        for _ in 0..nf {
            r.u2()?;
            r.u2()?;
            r.u2()?;
            let na = r.u2()? as usize;
            for _ in 0..na {
                r.u2()?;
                let len = r.u4()? as usize;
                r.bytes(len)?;
            }
        }
        let nm = r.u2()? as usize;
        let mut methods = vec![];
        for _ in 0..nm {
            let access = r.u2()?;
            let name = utf(&cp, r.u2()?)?;
            let descriptor = utf(&cp, r.u2()?)?;
            let na = r.u2()? as usize;
            let mut code = None;
            for _ in 0..na {
                let an = utf(&cp, r.u2()?)?;
                let len = r.u4()? as usize;
                let body = r.bytes(len)?;
                if an == "Code" {
                    // max_stack u2, max_locals u2, code_length u4, code
                    let mut c = Rd { b: body, p: 4 };
                    let clen = c.u4()? as usize;
                    code = Some(c.bytes(clen)?.to_vec());
                }
            }
            methods.push(JavaMethod { name, descriptor, access, code });
        }
        let name = match cp.get(this_class as usize)? {
            Cp::Class(i) => utf(&cp, *i)?.replace('/', "."),
            _ => return None,
        };
        Some(JavaClass { name, cp, methods })
    }

    fn utf8(&self, i: u16) -> Option<&str> {
        match self.cp.get(i as usize)? {
            Cp::Utf8(s) => Some(s),
            _ => None,
        }
    }

    /// `(class name, member name, descriptor)` of a field or method reference
    fn member_ref(&self, i: u16) -> Option<(String, String, String)> {
        let (c, nt) = match self.cp.get(i as usize)? {
            Cp::Field(c, nt) | Cp::Method(c, nt) => (*c, *nt),
            _ => return None,
        };
        let cname = match self.cp.get(c as usize)? {
            Cp::Class(n) => self.utf8(*n)?.to_string(),
            _ => return None,
        };
        let (n, d) = match self.cp.get(nt as usize)? {
            Cp::NameType(n, d) => (self.utf8(*n)?.to_string(), self.utf8(*d)?.to_string()),
            _ => return None,
        };
        Some((cname, n, d))
    }

    /// the parameter types of a method descriptor, as `Class.getName()` prints them
    fn descriptor_types(desc: &str) -> (Vec<String>, String) {
        fn one(s: &[u8], i: &mut usize) -> String {
            let mut dims = 0;
            while s.get(*i) == Some(&b'[') {
                dims += 1;
                *i += 1;
            }
            let base = match s.get(*i) {
                Some(b'B') => "byte".to_string(),
                Some(b'C') => "char".to_string(),
                Some(b'D') => "double".to_string(),
                Some(b'F') => "float".to_string(),
                Some(b'I') => "int".to_string(),
                Some(b'J') => "long".to_string(),
                Some(b'S') => "short".to_string(),
                Some(b'Z') => "boolean".to_string(),
                Some(b'V') => "void".to_string(),
                Some(b'L') => {
                    let end = s[*i..].iter().position(|&c| c == b';').map(|p| *i + p).unwrap_or(s.len());
                    let n = String::from_utf8_lossy(&s[*i + 1..end]).replace('/', ".");
                    *i = end;
                    n
                }
                _ => "?".to_string(),
            };
            *i += 1;
            format!("{}{}", base, "[]".repeat(dims))
        }
        let s = desc.as_bytes();
        let mut i = 1;
        let mut params = vec![];
        while i < s.len() && s[i] != b')' {
            params.push(one(s, &mut i));
        }
        i += 1;
        let ret = one(s, &mut i);
        (params, ret)
    }

    pub fn param_count(&self, m: &JavaMethod) -> usize {
        Self::descriptor_types(&m.descriptor).0.len()
    }

    /// `public static` method that is not a constructor or an initializer
    pub fn is_public_static(&self, m: &JavaMethod) -> bool {
        m.access & 0x0001 != 0 && m.access & 0x0008 != 0 && !m.name.starts_with('<')
    }

    /// Java: `MethodValue.toString`: `<Java Method: ` + `Method.toString()` + `>`
    pub fn signature(&self, m: &JavaMethod) -> String {
        let (params, ret) = Self::descriptor_types(&m.descriptor);
        let mut mods = vec![];
        if m.access & 0x0001 != 0 {
            mods.push("public");
        }
        if m.access & 0x0004 != 0 {
            mods.push("protected");
        }
        if m.access & 0x0002 != 0 {
            mods.push("private");
        }
        if m.access & 0x0008 != 0 {
            mods.push("static");
        }
        format!("<Java Method: {} {} {}.{}({})>", mods.join(" "), ret, self.name, m.name, params.join(","))
    }

    /// Execute a method whose result only depends on constants.  `None`: the body uses something else (arguments, other calls).
    pub fn run_constant(&self, m: &JavaMethod) -> Option<Value> {
        #[derive(Clone)]
        enum V {
            Val(Value),
            Int(i32),
        }
        let code = m.code.as_ref()?;
        let mut stack: Vec<V> = vec![];
        let mut pc = 0usize;
        while pc < code.len() {
            let op = code[pc];
            pc += 1;
            match op {
                0x00 => {}
                0x02..=0x08 => stack.push(V::Int(op as i32 - 3)),
                0x10 => {
                    stack.push(V::Int(*code.get(pc)? as i8 as i32));
                    pc += 1;
                }
                0x11 => {
                    let v = ((*code.get(pc)? as i16) << 8) | *code.get(pc + 1)? as i16;
                    stack.push(V::Int(v as i32));
                    pc += 2;
                }
                0x12 => {
                    let idx = *code.get(pc)? as u16;
                    pc += 1;
                    match self.cp.get(idx as usize)? {
                        Cp::Int(i) => stack.push(V::Int(*i)),
                        _ => return None,
                    }
                }
                // getstatic
                0xb2 => {
                    let idx = ((*code.get(pc)? as u16) << 8) | *code.get(pc + 1)? as u16;
                    pc += 2;
                    let (class, name, _) = self.member_ref(idx)?;
                    match (class.as_str(), name.as_str()) {
                        ("tlc2/value/impl/BoolValue", "ValTrue") => stack.push(V::Val(Value::Bool(true))),
                        ("tlc2/value/impl/BoolValue", "ValFalse") => stack.push(V::Val(Value::Bool(false))),
                        _ => return None,
                    }
                }
                // invokestatic
                0xb8 => {
                    let idx = ((*code.get(pc)? as u16) << 8) | *code.get(pc + 1)? as u16;
                    pc += 2;
                    let (class, name, _) = self.member_ref(idx)?;
                    match (class.as_str(), name.as_str(), stack.pop()?) {
                        ("tlc2/value/impl/IntValue", "gen", V::Int(i)) => stack.push(V::Val(Value::Int(i))),
                        _ => return None,
                    }
                }
                // areturn
                0xb0 => {
                    return match stack.pop()? {
                        V::Val(v) => Some(v),
                        _ => None,
                    };
                }
                _ => return None,
            }
        }
        let _ = Cp::Str(0);
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// a class with `public static Value Get() { return BoolValue.ValTrue; }` and `Get2(Value)`
    #[test]
    fn reads_the_override_class_of_a_test_model() {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reference/tlaplus/tlatools/org.lamport.tlatools/test-model/UserModuleOverride.class");
        let Ok(bytes) = std::fs::read(&p) else { return };
        let c = JavaClass::parse(&bytes).unwrap();
        assert_eq!(c.name, "UserModuleOverride");
        let get = c.methods.iter().find(|m| m.name == "Get").unwrap();
        assert!(c.is_public_static(get));
        assert_eq!(c.param_count(get), 0);
        assert_eq!(c.signature(get), "<Java Method: public static tlc2.value.impl.Value UserModuleOverride.Get()>");
        assert!(matches!(c.run_constant(get), Some(Value::Bool(true))));
        let get2 = c.methods.iter().find(|m| m.name == "Get2").unwrap();
        assert_eq!(c.param_count(get2), 1);
        assert_eq!(c.signature(get2), "<Java Method: public static tlc2.value.impl.Value UserModuleOverride.Get2(tlc2.value.impl.Value)>");
    }
}

// ---------------------------------------------------------------------------------------------- the user's module overrides

/// what loading the override classes of a specification yields
#[derive(Default)]
pub struct UserOverrides {
    /// `(is a warning, code, text)` in the order Java prints them
    pub messages: Vec<(bool, i32, String)>,
    /// the replaced operators: `(module, operator, arity, value)`
    pub values: Vec<(String, String, usize, Value)>,
    /// loaded methods whose body this port cannot run: the operator keeps its TLA+ definition (the Java method is expected to compute
    /// the same, as in the examples that ship a `Bits.class`)
    pub unsupported: Vec<String>,
}

/// `file:/D:/dir/X.class` as `URL.toExternalForm` prints a file URL
fn file_url(p: &std::path::Path) -> String {
    let abs = std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    let s = abs.to_string_lossy().replace('\\', "/");
    let s = s.strip_prefix("//?/").unwrap_or(&s).to_string();
    if s.starts_with('/') {
        format!("file:{}", s)
    } else {
        format!("file:/{}", s)
    }
}

/// Java: `SpecProcessor.processModuleOverrides`, for the classes found next to the specification: a method matches an operator of
/// the module of the same name and arity.
pub fn load_user_overrides(dir: &std::path::Path, sem: &tla_sany::analyze::SemSpec) -> UserOverrides {
    let mut out = UserOverrides::default();
    for name in &sem.order {
        let Some(module) = sem.modules.get(name) else { continue };
        if module.is_standard.get() {
            continue;
        }
        let path = dir.join(format!("{}.class", name));
        let Ok(bytes) = std::fs::read(&path) else { continue };
        let Some(class) = JavaClass::parse(&bytes) else { continue };
        let url = file_url(&path);
        // the arity of the operators the module defines itself
        let mut arity: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for d in module.defs.borrow().iter() {
            if *d.module == **name {
                arity.insert(d.name.to_string(), d.params.borrow().len());
            }
        }
        let mut loaded: Vec<(bool, i32, String)> = vec![];
        for m in &class.methods {
            if !class.is_public_static(m) {
                continue;
            }
            let sig = class.signature(m);
            let n = class.param_count(m);
            if arity.get(&m.name) != Some(&n) {
                out.messages.push((true, crate::ec::TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH, format!("Failed to match {} operator override from {} with signature: {}.", m.name, url, sig)));
            } else {
                loaded.push((false, crate::ec::TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED, format!("Loading {} operator override from {} with signature: {}.", m.name, url, sig)));
                match class.run_constant(m) {
                    Some(v) => out.values.push((name.to_string(), m.name.clone(), n, v)),
                    None => out.unsupported.push(sig),
                }
            }
        }
        out.messages.extend(loaded);
    }
    out
}
