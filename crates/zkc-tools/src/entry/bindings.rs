//! Rust data bindings for a trusted Entry publication. No protocol code is emitted.
use super::{
    Interface, Package,
    interface::raw::{Field, Kind, Port, Schema},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;
const MAX_BYTES: usize = 16 * 1024 * 1024;

#[derive(Default)]
struct Names {
    used: BTreeSet<String>,
    next: BTreeMap<String, usize>,
}
impl Names {
    fn ty(&mut self, preferred: &str) -> String {
        let mut name = String::new();
        for word in preferred.split('_').filter(|w| !w.is_empty()) {
            let mut chars = word.chars();
            if let Some(first) = chars.next() {
                name.extend(first.to_uppercase());
                name.extend(chars);
            }
        }
        if name == "Self" {
            name = "ValueSelf".into();
        }
        self.allocate(&name)
    }
    fn allocate(&mut self, preferred: &str) -> String {
        let base: String = preferred
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
            .take(96)
            .collect();
        let base = if base.chars().all(|c| c == '_') || base.as_bytes()[0].is_ascii_digit() {
            format!("Value{base}")
        } else {
            base
        };
        let base = if matches!(base.as_str(), "Self" | "self" | "super" | "crate") {
            format!("value_{base}")
        } else {
            base
        };
        let mut name = base.clone();
        let next = self.next.entry(base.clone()).or_insert(2);
        while !self.used.insert(name.clone()) {
            name = format!("{base}{next}");
            *next += 1;
        }
        // Raw identifiers also cover future reserved keywords. Special path names
        // above cannot be raw, so they get ordinary unique names instead.
        format!("r#{name}")
    }
}
fn source_name(name: &str) -> String {
    let name = if matches!(name, "self" | "Self" | "super" | "crate" | "_")
        || name.starts_with("__zkc_")
    {
        format!("__zkc_{}", crate::host::inputs::hex(name.as_bytes()))
    } else {
        name.to_owned()
    };
    format!("r#{name}")
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
                    name: source_name(&label),
                    ty: self.schema(&field.schema, &format!("{prefix}_{}", field.name))?,
                })
            })
            .collect()
    }
    fn schema(&mut self, schema: &Schema, prefix: &str) -> Result<String> {
        let simple = match schema.kind {
            Kind::Boolean => Some("bool"),
            Kind::Index => Some("u64"),
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
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b':')
        {
            schema.display_type.replace("::", "_")
        } else {
            prefix.to_owned()
        };
        let name = self.names.ty(&preferred);
        self.types.insert(schema.identity.clone(), name.clone());
        if schema.kind == Kind::Variant {
            let mut arms = Vec::new();
            for arm in &schema.alternatives {
                arms.push((
                    arm.name.clone(),
                    source_name(&arm.name),
                    self.members(&arm.fields, &format!("{prefix}_{}", arm.name))?,
                ));
            }
            self.add(format!("#[allow(non_camel_case_types, non_snake_case)]\n#[derive(Debug)]\npub enum {name} {{\n"))?;
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
                for f in fields {
                    self.add(format!("{},", f.name))?;
                }
                self.add(format!(
                    "}}=>Self::Variant{{alternative: {source:?}.into(),fields:["
                ))?;
                for f in fields {
                    self.add(format!("({:?}.into(),{}.into()),", f.source, f.name))?;
                }
                self.add("].into()},\n")?;
            }
            self.add("}}}\n")?;
            let mutable = if arms.iter().any(|(_, _, fields)| !fields.is_empty()) {
                "mut "
            } else {
                ""
            };
            self.add(format!("impl ::core::convert::TryFrom<::zkc_tools::entry::Value> for {name} {{type Error=::std::string::String;fn try_from(value: ::zkc_tools::entry::Value)->::core::result::Result<Self,::std::string::String>{{let ::zkc_tools::entry::Value::Variant{{alternative,{mutable}fields}}=value else{{return Err(\"entry-binding-value\".into());}};let result=match alternative.as_str(){{\n"))?;
            for (source, arm, fields) in &arms {
                self.add(format!("{source:?}=>Self:: {arm}{{"))?;
                self.decode_fields(fields, "fields")?;
                self.add("},\n")?;
            }
            self.add("_=>return Err(\"entry-binding-alternative\".into()),};if !fields.is_empty(){return Err(\"entry-binding-fields\".into());}Ok(result)}}\n")?;
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
                    self.add("vec![")?;
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
            self.add(format!("impl ::core::convert::TryFrom<::zkc_tools::entry::Value> for {name} {{type Error=::std::string::String;fn try_from(value: ::zkc_tools::entry::Value)->::core::result::Result<Self,::std::string::String>{{let ::zkc_tools::entry::Value:: {variant}(values)=value else{{return Err(\"entry-binding-value\".into());}};"))?;
            match schema.kind {
                Kind::Record => {
                    if !fields.is_empty() {
                        self.add("let mut values=values;")?;
                    }
                    self.add("let result=Self{")?;
                    self.decode_fields(&fields, "values")?;
                    self.add("};if !values.is_empty(){return Err(\"entry-binding-fields\".into());}Ok(result)")?;
                }
                Kind::Tuple => {
                    self.add("let mut values=values.into_iter();let result=Self{")?;
                    for f in &fields {
                        self.add(format!(
                            "{}:__zkc_decode(values.next().ok_or(\"entry-binding-fields\")?)?,",
                            f.name
                        ))?;
                    }
                    self.add("};if values.next().is_some(){return Err(\"entry-binding-fields\".into());}Ok(result)")?;
                }
                Kind::Associated => self.add(format!(
                    "Ok(Self{{{}:__zkc_decode(*values)?}})",
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
            "#[allow(non_snake_case)]\n#[derive(Debug)]\npub struct {name} {{\n"
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
    fn ports<'a>(
        &mut self,
        preferred: &str,
        ports: impl Iterator<Item = &'a Port>,
        interface: &Interface,
        inputs: bool,
    ) -> Result<String> {
        let name = self.names.ty(preferred);
        let mut fields = Vec::new();
        for port in ports {
            if inputs
                && super::setups::key_kind(interface, port)
                    == Some(zkc_runtime::interactive::Type::VerifierKey)
            {
                continue;
            }
            fields.push(Member {
                source: port.name.clone(),
                name: source_name(&port.name),
                ty: self.schema(&port.schema, &format!("{preferred}_{}", port.name))?,
            });
        }
        self.structure(&name, &fields)?;
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
            "};if !values.is_empty(){return Err(\"entry-binding-fields\".into());}Ok(result)}}\n",
        )?;
        Ok(name)
    }
}
/// Generate convenience data types and an admission helper pinned to this exact
/// trusted package. Mathematical leaves use entry::Value and keep native checks;
/// this is not protocol algorithm generation or a new authority source.
pub fn rust(package: &Package) -> Result<String> {
    let interface = Interface::read(package).map_err(|e| e.to_string())?;
    let protocol = interface.selected_protocol();
    let mut generator = Generator {
        names: Names::default(),
        types: BTreeMap::new(),
        code: String::new(),
    };
    generator.add("// Generated from an authenticated zkc Entry package.\n// Mathematical leaves retain checked ::zkc_tools::entry::Value ingress.\n#[allow(dead_code)]\nfn __zkc_decode<T: ::core::convert::TryFrom<::zkc_tools::entry::Value>>(value: ::zkc_tools::entry::Value) -> ::core::result::Result<T, ::std::string::String> where T::Error: ::core::fmt::Display { T::try_from(value).map_err(|error| error.to_string()) }\n")?;
    generator.add(format!(
        "pub const PACKAGE_SHA256:[u8;32]={:?};\n",
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
            "::zkc_tools::protocol::run::HostLimits",
        )
    };
    generator.add(format!("pub fn admit(bytes:&[u8],options: {options},setups: ::zkc_tools::entry::SetupAuthority)->::core::result::Result<{host},::std::string::String>{{let package=::zkc_tools::entry::Package::capture(bytes,&PACKAGE_SHA256,::zkc_tools::entry::Package::MAX_BYTES).map_err(|e|e.to_string())?;{host}::admit(package,options,setups)}}\n"))?;
    if let super::interface::raw::Job::Proof { public, .. } = &interface.document.job {
        generator.ports(
            "PublicInputs",
            public.iter().map(|i| &protocol.inputs[*i as usize]),
            &interface,
            true,
        )?;
    }
    for role in &protocol.roles {
        let input = generator.ports(
            &format!("{role}Inputs"),
            protocol.inputs.iter().filter(|p| p.roles.contains(role)),
            &interface,
            true,
        )?;
        let output = generator.ports(
            &format!("{role}Outputs"),
            protocol.outputs.iter().filter(|p| p.roles.contains(role)),
            &interface,
            false,
        )?;
        generator.add(format!("impl {input} {{ pub const ROLE: &'static str = {role:?}; pub fn into_role(self) -> (::std::string::String, ::zkc_tools::entry::RoleInputs) {{ (Self::ROLE.into(), ::zkc_tools::entry::RoleInputs {{ inputs: self.into(), ..::core::default::Default::default() }}) }} }}\n"))?;
        generator.add(format!("impl {output} {{ pub const ROLE: &'static str = {role:?}; pub fn take(values: &mut ::zkc_tools::entry::RoleValues) -> ::core::result::Result<Self, ::std::string::String> {{ ::core::convert::TryFrom::try_from(values.remove(Self::ROLE).ok_or(\"entry-binding-role\")?) }} }}\n"))?;
    }
    for (module, names) in [
        (
            "setups",
            interface
                .document
                .setups
                .iter()
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>(),
        ),
        (
            "services",
            protocol
                .services
                .iter()
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>(),
        ),
    ] {
        generator.add(format!(
            "#[allow(non_upper_case_globals)]\npub mod {module} {{\n"
        ))?;
        for name in names {
            generator.add(format!(
                "pub const {}: &str = {name:?};\n",
                source_name(name)
            ))?;
        }
        generator.add("}\n")?;
    }
    if let super::interface::raw::Job::Proof {
        prover, verifier, ..
    } = &interface.document.job
    {
        generator.add(format!(
            "pub const PROVER: &str = {prover:?};\npub const VERIFIER: &str = {verifier:?};\n"
        ))?;
    }
    Ok(generator.code)
}
