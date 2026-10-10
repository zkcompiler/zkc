//! Rust data bindings for a trusted Entry publication. No protocol code is emitted.
use super::{
    Package,
    interface::raw::{Field, Kind, Port, Schema},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;
const MAX_BYTES: usize = 16 * 1024 * 1024;

// One allocator owns all generated namespaces. Source escapes are injective;
// allocation also resolves generated type/member and preferred-name collisions.
#[derive(Default)]
struct Names {
    used: BTreeMap<usize, BTreeSet<String>>,
    next: BTreeMap<(usize, String), usize>,
    scopes: usize,
}
const MAX_NAME_BYTES: usize = 1024 * 1024;
impl Names {
    fn scope(&mut self) -> usize {
        self.scopes += 1;
        self.scopes
    }
    fn ty(&mut self, preferred: &str) -> Result<String> {
        // Escape original UTF-8 before case conversion: mathematical names and
        // the reserved escape prefix must never lose spelling information.
        let name = if needs_escape(preferred) {
            source_name(preferred)?
        } else {
            let mut name = String::new();
            for word in preferred.split('_').filter(|w| !w.is_empty()) {
                let mut chars = word.chars();
                if let Some(first) = chars.next() {
                    name.push(first.to_ascii_uppercase());
                    name.extend(chars);
                }
            }
            source_name(&name)?
        };
        self.allocate(0, &name)
    }
    fn member(&mut self, scope: usize, source: &str) -> Result<String> {
        self.allocate(scope, &source_name(source)?)
    }
    fn allocate(&mut self, scope: usize, base: &str) -> Result<String> {
        if base.len() > MAX_NAME_BYTES {
            return Err("entry-bindings-limit".into());
        }
        let mut name = base.to_owned();
        let next = self.next.entry((scope, base.to_owned())).or_insert(2);
        let used = self.used.entry(scope).or_default();
        while !used.insert(name.clone()) {
            name = format!("{base}{next}");
            *next += 1;
            if name.len() > MAX_NAME_BYTES {
                return Err("entry-bindings-limit".into());
            }
        }
        Ok(format!("r#{name}"))
    }
}
fn needs_escape(name: &str) -> bool {
    !name.is_ascii()
        || name.starts_with("__zkc_")
        || name.is_empty()
        || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
        || name.as_bytes()[0].is_ascii_digit()
        || matches!(
            name,
            "_" | "as"
                | "async"
                | "await"
                | "break"
                | "const"
                | "continue"
                | "crate"
                | "dyn"
                | "else"
                | "enum"
                | "extern"
                | "false"
                | "fn"
                | "for"
                | "if"
                | "impl"
                | "in"
                | "let"
                | "loop"
                | "match"
                | "mod"
                | "move"
                | "mut"
                | "pub"
                | "ref"
                | "return"
                | "self"
                | "Self"
                | "static"
                | "struct"
                | "super"
                | "trait"
                | "true"
                | "type"
                | "unsafe"
                | "use"
                | "where"
                | "while"
                | "abstract"
                | "become"
                | "box"
                | "do"
                | "final"
                | "gen"
                | "macro"
                | "override"
                | "priv"
                | "try"
                | "typeof"
                | "unsized"
                | "virtual"
                | "yield"
        )
}
fn source_name(name: &str) -> Result<String> {
    if needs_escape(name) {
        if name.len() > (MAX_NAME_BYTES - 6) / 2 {
            return Err("entry-bindings-limit".into());
        }
        Ok(format!(
            "__zkc_{}",
            crate::source_names::encode_nominal_identity(name)
        ))
    } else if name.len() > MAX_NAME_BYTES {
        Err("entry-bindings-limit".into())
    } else {
        Ok(name.to_owned())
    }
}
struct Generator {
    names: Names,
    types: BTreeMap<String, String>,
    code: String,
}
struct Member {
    source: String,
    name: String,
    ty: String,
}
impl Generator {
    fn add(&mut self, text: impl AsRef<str>) -> Result<()> {
        let text = text.as_ref();
        if text.len() > MAX_BYTES.saturating_sub(self.code.len()) {
            return Err("entry-bindings-limit".into());
        }
        self.code.push_str(text);
        Ok(())
    }
    fn members(&mut self, fields: &[Field], prefix: &str) -> Result<Vec<Member>> {
        let scope = self.names.scope();
        fields
            .iter()
            .map(|field| {
                let label = if field.name.bytes().all(|c| c.is_ascii_digit()) {
                    format!("item_{}", field.name)
                } else {
                    field.name.clone()
                };
                Ok(Member {
                    source: field.name.clone(),
                    name: self.names.member(scope, &label)?,
                    ty: self.schema(&field.schema, &format!("{prefix}_{}", field.name))?,
                })
            })
            .collect()
    }
    fn schema(&mut self, schema: &Schema, prefix: &str) -> Result<String> {
        let simple = match schema.kind {
            Kind::Boolean => Some("::core::primitive::bool"),
            Kind::Index => Some("::core::primitive::u64"),
            Kind::Unit => Some("()"),
            Kind::Field | Kind::Group | Kind::Builtin => Some("::zkc_tools::entry::Value"),
            _ => None,
        };
        if let Some(simple) = simple {
            return Ok(simple.into());
        }
        if let Some(name) = self.types.get(&schema.identity) {
            return Ok(name.clone());
        }
        if schema.kind == Kind::Array {
            let element = if let Some(field) = schema.fields.first() {
                self.schema(&field.schema, &format!("{prefix}_Item"))?
            } else {
                "::zkc_tools::entry::Value".into()
            };
            let ty = format!("[{element};{}]", schema.fields.len());
            self.types.insert(schema.identity.clone(), ty.clone());
            return Ok(ty);
        }
        let preferred = if matches!(schema.kind, Kind::Record | Kind::Variant)
            && schema
                .display_type
                .split("::")
                .all(crate::source_names::is_source_identifier)
        {
            if schema.display_type.is_ascii() {
                schema.display_type.replace("::", "_")
            } else {
                schema.display_type.clone()
            }
        } else {
            prefix.to_owned()
        };
        let name = self.names.ty(&preferred)?;
        self.types.insert(schema.identity.clone(), name.clone());
        if schema.kind == Kind::Variant {
            let mut arms = Vec::new();
            let scope = self.names.scope();
            for arm in &schema.alternatives {
                arms.push((
                    arm.name.clone(),
                    self.names.member(scope, &arm.name)?,
                    self.members(&arm.fields, &format!("{prefix}_{}", arm.name))?,
                ));
            }
            self.add(format!("#[allow(non_camel_case_types, non_snake_case)]\n#[derive(::core::fmt::Debug)]\npub enum {name} {{\n"))?;
            for (_, arm, fields) in &arms {
                self.add(format!("{arm} {{"))?;
                for f in fields {
                    self.add(format!("{}: {},", f.name, f.ty))?;
                }
                self.add("},\n")?;
            }
            self.add("}\n")?;
            self.add(format!("#[allow(non_snake_case)]\nimpl ::core::convert::From<{name}> for ::zkc_tools::entry::Value {{fn from(value: {name})->Self {{match value {{\n"))?;
            for (source, arm, fields) in &arms {
                self.add(format!("{name}:: {arm}{{"))?;
                // Source field names can resolve to variants or constants in
                // Rust patterns; bind each field to a generated local instead.
                for (index, f) in fields.iter().enumerate() {
                    self.add(format!("{}: __zkc_field_{index},", f.name))?;
                }
                self.add(format!(
                    "}}=>Self::Variant{{alternative: {source:?}.into(),fields:["
                ))?;
                for (index, f) in fields.iter().enumerate() {
                    self.add(format!(
                        "({:?}.into(),__zkc_field_{index}.into()),",
                        f.source
                    ))?;
                }
                self.add("].into()},\n")?;
            }
            self.add("}}}\n")?;
            let mutable = if arms.iter().any(|(_, _, fields)| !fields.is_empty()) {
                "mut "
            } else {
                ""
            };
            self.add(format!("impl ::core::convert::TryFrom<::zkc_tools::entry::Value> for {name} {{type Error=::std::string::String;fn try_from(value: ::zkc_tools::entry::Value)->::core::result::Result<Self,::std::string::String>{{let ::zkc_tools::entry::Value::Variant{{alternative,{mutable}fields}}=value else{{return ::core::result::Result::Err(\"entry-binding-value\".into());}};let result=match alternative.as_str(){{\n"))?;
            for (source, arm, fields) in &arms {
                self.add(format!("{source:?}=>Self:: {arm}{{"))?;
                self.decode_fields(fields, "fields")?;
                self.add("},\n")?;
            }
            self.add("_=>return ::core::result::Result::Err(\"entry-binding-alternative\".into()),};if !fields.is_empty(){return ::core::result::Result::Err(\"entry-binding-fields\".into());}::core::result::Result::Ok(result)}}\n")?;
        } else {
            let fields = self.members(&schema.fields, prefix)?;
            self.structure(&name, &fields)?;
            let variant = match schema.kind {
                Kind::Record => "Record",
                Kind::Tuple => "Tuple",
                Kind::Associated => "Associated",
                _ => return Err("entry-bindings-schema".into()),
            };
            let parameter = if fields.is_empty() { "_value" } else { "value" };
            self.add(format!("#[allow(non_snake_case)]\nimpl ::core::convert::From<{name}> for ::zkc_tools::entry::Value {{fn from({parameter}: {name})->Self {{Self:: {variant}("))?;
            match schema.kind {
                Kind::Record => {
                    self.add("[")?;
                    for f in &fields {
                        self.add(format!("({:?}.into(),value.{}.into()),", f.source, f.name))?;
                    }
                    self.add("].into()")?;
                }
                Kind::Tuple => {
                    self.add("::std::vec![")?;
                    for f in &fields {
                        self.add(format!("value.{}.into(),", f.name))?;
                    }
                    self.add("]")?;
                }
                Kind::Associated => self.add(format!(
                    "::std::boxed::Box::new(value.{}.into())",
                    fields[0].name
                ))?,
                _ => unreachable!(),
            }
            self.add(")}}\n")?;
            self.add(format!("impl ::core::convert::TryFrom<::zkc_tools::entry::Value> for {name} {{type Error=::std::string::String;fn try_from(value: ::zkc_tools::entry::Value)->::core::result::Result<Self,::std::string::String>{{let ::zkc_tools::entry::Value:: {variant}(values)=value else{{return ::core::result::Result::Err(\"entry-binding-value\".into());}};"))?;
            match schema.kind {
                Kind::Record => {
                    if !fields.is_empty() {
                        self.add("let mut values=values;")?;
                    }
                    self.add("let result=Self{")?;
                    self.decode_fields(&fields, "values")?;
                    self.add("};if !values.is_empty(){return ::core::result::Result::Err(\"entry-binding-fields\".into());}::core::result::Result::Ok(result)")?;
                }
                Kind::Tuple => {
                    self.add("let mut values=values.into_iter();let result=Self{")?;
                    for f in &fields {
                        self.add(format!(
                            "{}:__zkc_decode(values.next().ok_or(\"entry-binding-fields\")?)?,",
                            f.name
                        ))?;
                    }
                    self.add("};if values.next().is_some(){return ::core::result::Result::Err(\"entry-binding-fields\".into());}::core::result::Result::Ok(result)")?;
                }
                Kind::Associated => self.add(format!(
                    "::core::result::Result::Ok(Self{{{}:__zkc_decode(*values)?}})",
                    fields[0].name
                ))?,
                _ => unreachable!(),
            }
            self.add("}}\n")?;
        }
        Ok(name)
    }
    fn structure(&mut self, name: &str, fields: &[Member]) -> Result<()> {
        self.add(format!(
            "#[allow(non_camel_case_types, non_snake_case)]\n#[derive(::core::fmt::Debug)]\npub struct {name} {{\n"
        ))?;
        for f in fields {
            self.add(format!("pub {}: {},\n", f.name, f.ty))?;
        }
        self.add("}\n")
    }
    fn decode_fields(&mut self, fields: &[Member], map: &str) -> Result<()> {
        for f in fields {
            self.add(format!(
                "{}:__zkc_decode({map}.remove({:?}).ok_or(\"entry-binding-fields\")?)?,",
                f.name, f.source
            ))?;
        }
        Ok(())
    }
    fn ports<'a>(&mut self, name: &str, ports: impl Iterator<Item = &'a Port>) -> Result<()> {
        let preferred = name.strip_prefix("r#").unwrap_or(name);
        let mut fields = Vec::new();
        let scope = self.names.scope();
        for port in ports {
            fields.push(Member {
                source: port.name.clone(),
                name: self.names.member(scope, &port.name)?,
                ty: self.schema(&port.schema, &format!("{preferred}_{}", port.name))?,
            });
        }
        self.structure(name, &fields)?;
        let parameter = if fields.is_empty() { "_value" } else { "value" };
        self.add(format!(
            "impl ::core::convert::From<{name}> for ::zkc_tools::entry::NamedValues {{fn from({parameter}: {name})->Self {{["
        ))?;
        for f in &fields {
            self.add(format!("({:?}.into(),value.{}.into()),", f.source, f.name))?;
        }
        self.add("].into()}}\n")?;
        let mutable = if fields.is_empty() { "" } else { "mut " };
        self.add(format!("impl ::core::convert::TryFrom<::zkc_tools::entry::NamedValues> for {name} {{type Error=::std::string::String;fn try_from({mutable}values: ::zkc_tools::entry::NamedValues)->::core::result::Result<Self,::std::string::String>{{let result=Self{{"))?;
        self.decode_fields(&fields, "values")?;
        self.add(
            "};if !values.is_empty(){return ::core::result::Result::Err(\"entry-binding-fields\".into());}::core::result::Result::Ok(result)}}\n",
        )?;
        Ok(())
    }
}
/// Generate convenience data types and an admission helper pinned to this exact
/// trusted package. Mathematical leaves use entry::Value and keep native checks;
/// this is not protocol algorithm generation or a new authority source.
pub fn rust(package: &Package) -> Result<String> {
    let interface = crate::entry::BoundInterface::read(package).map_err(|e| e.to_string())?;
    super::arguments::check_ports(&interface)?;
    let mut generator = Generator {
        names: Names::default(),
        types: BTreeMap::new(),
        code: String::new(),
    };
    generator.names.used.insert(
        0,
        [
            "__zkc_decode",
            "PACKAGE_SHA256",
            "admit",
            "setups",
            "services",
            "PROVER",
            "VERIFIER",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
    );
    generator.add("// Generated from an authenticated zkc Entry package.\n// Mathematical leaves retain checked ::zkc_tools::entry::Value ingress.\n#[allow(dead_code)]\nfn __zkc_decode<T: ::core::convert::TryFrom<::zkc_tools::entry::Value>>(value: ::zkc_tools::entry::Value) -> ::core::result::Result<T, ::std::string::String> where T::Error: ::core::fmt::Display { T::try_from(value).map_err(|error| error.to_string()) }\n")?;
    generator.add(format!(
        "pub const PACKAGE_SHA256:[::core::primitive::u8;32]={:?};\n",
        package.identity()
    ))?;
    let (host, options) = if interface.is_proof() {
        (
            "::zkc_tools::entry::ProofEntry",
            "::zkc_tools::entry::ProofOptions",
        )
    } else {
        (
            "::zkc_tools::entry::RunEntry",
            "::zkc_tools::run::HostLimits",
        )
    };
    generator.add(format!("/// Authenticate this exact package and admit its interface, program and application limits.\n/// Artifact bytes stay immutable; no caller verification flag or CLI transport is involved.\npub fn admit(bytes:&[::core::primitive::u8],options: {options},setups: ::zkc_tools::entry::SetupAuthority)->::core::result::Result<{host},::zkc_tools::entry::EntryError>{{let package=::zkc_tools::entry::Package::capture(bytes,&PACKAGE_SHA256,::zkc_tools::entry::Package::MAX_BYTES)?;{host}::admit(package,options,setups)}}\n"))?;
    let public_name = interface
        .is_proof()
        .then(|| generator.names.ty("PublicInputs"))
        .transpose()?;
    let role_names: Vec<_> = interface
        .roles()
        .iter()
        .map(|role| {
            Ok((
                generator.names.ty(&format!("{}Inputs", role.name))?,
                generator.names.ty(&format!("{}Outputs", role.name))?,
            ))
        })
        .collect::<Result<_>>()?;
    if interface.is_proof() {
        generator.ports(
            public_name.as_ref().expect("proof public name reserved"),
            interface
                .public_ports()
                .filter(|p| p.named())
                .map(|p| p.definition),
        )?;
    }
    for (ports, (input, output)) in interface.roles().iter().zip(role_names) {
        let role = &ports.name;
        generator.ports(&input, interface.named_inputs(ports).map(|p| p.definition))?;
        generator.ports(&output, interface.output_ports(ports))?;
        generator.add(format!("impl {input} {{ pub const ROLE: &'static ::core::primitive::str = {role:?}; pub fn into_inputs(self) -> ::zkc_tools::entry::RoleInputs {{ ::zkc_tools::entry::RoleInputs {{ inputs: self.into(), ..::core::default::Default::default() }} }} pub fn into_role(self) -> (::std::string::String, ::zkc_tools::entry::RoleInputs) {{ (Self::ROLE.into(), self.into_inputs()) }} }}\n"))?;
        generator.add(format!("impl {output} {{ pub const ROLE: &'static ::core::primitive::str = {role:?}; pub fn take(values: &mut ::zkc_tools::entry::RoleValues) -> ::core::result::Result<Self, ::std::string::String> {{ ::core::convert::TryFrom::try_from(values.remove(Self::ROLE).ok_or(\"entry-binding-role\")?) }} }}\n"))?;
    }
    for (module, names) in [
        ("setups", interface.setup_names().collect::<Vec<_>>()),
        (
            "services",
            interface
                .roles()
                .iter()
                .flat_map(|role| interface.services(role))
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>(),
        ),
    ] {
        generator.add(format!(
            "#[allow(non_upper_case_globals)]\npub mod {module} {{\n"
        ))?;
        let scope = generator.names.scope();
        for name in names {
            let member = generator.names.member(scope, name)?;
            generator.add(format!(
                "pub const {}: &::core::primitive::str = {name:?};\n",
                member
            ))?;
        }
        generator.add("}\n")?;
    }
    if let Some(proof) = interface.proof() {
        let prover = &interface.roles()[proof.prover].name;
        let verifier = &interface.roles()[proof.verifier].name;
        generator.add(format!(
            "pub const PROVER: &::core::primitive::str = {prover:?};\npub const VERIFIER: &::core::primitive::str = {verifier:?};\n"
        ))?;
    }
    Ok(generator.code)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn full_byte_escapes_and_generated_names_have_separate_expansion_limits() {
        let name = "α".repeat(64); // The source identifier's 128-byte ceiling.
        let escaped = source_name(&name).unwrap();
        assert_eq!(escaped, format!("__zkc_{}", "ceb1".repeat(64)));
        let mut names = Names::default();
        let first = format!("{}a", "x".repeat(127));
        let second = format!("{}b", "x".repeat(127));
        let a = names.ty(&first).unwrap();
        let b = names.ty(&second).unwrap();
        assert!(a.ends_with('a') && b.ends_with('b')); // No 96-byte truncation.
        assert_ne!(a, b);
        assert_eq!(
            source_name(&"α".repeat(MAX_NAME_BYTES / 4)).unwrap_err(),
            "entry-bindings-limit"
        );
        assert_eq!(
            source_name(&"a".repeat(MAX_NAME_BYTES + 1)).unwrap_err(),
            "entry-bindings-limit"
        );
    }
}
