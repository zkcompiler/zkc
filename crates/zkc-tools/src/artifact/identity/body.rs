//! Declaration-local occurrence numbering and scope-aware SSA normalization.
use super::{
    Json, Result, array,
    bounds::Builder,
    list,
    model::{Source, strings},
    text,
};
use std::collections::BTreeMap;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Flavor {
    Function,
    Generic,
    Protocol,
}
#[derive(Clone)]
pub(super) struct Site {
    pub coordinate: String,
    pub kind: String,
}
pub(super) type Sites = BTreeMap<String, Site>;
pub(super) type SiteMaps = BTreeMap<String, Sites>;

fn instruction(value: &Json, flavor: Flavor) -> Result<&[Json]> {
    let r = list(value)?;
    let tag = text(r.first().ok_or("identity-instruction")?)?;
    let n = match (tag, flavor) {
        ("return" | "yield", _) => 2,
        ("if", Flavor::Function | Flavor::Generic) => 7,
        ("for", Flavor::Function | Flavor::Generic) => 9,
        ("op", Flavor::Function) => 6,
        ("apply", Flavor::Function | Flavor::Generic) => 6,
        ("op", Flavor::Generic) => 7,
        ("local", Flavor::Protocol) => 6,
        ("message" | "loop", Flavor::Protocol) => 7,
        ("call", Flavor::Protocol) => 5,
        ("stop", Flavor::Protocol) => 4,
        _ => return Err("identity-instruction".into()),
    };
    array(value, n)
}

pub(super) fn gather(source: &Source<'_>) -> Result<SiteMaps> {
    fn body(
        value: &Json,
        flavor: Flavor,
        sites: &mut Sites,
        count: &mut usize,
        nested: bool,
    ) -> Result<()> {
        let ops = list(value)?;
        if ops.is_empty() {
            return Err("identity-body".into());
        }
        for (index, op) in ops.iter().enumerate() {
            *count += 1;
            if *count > 32_768 {
                return Err("identity-instruction-limit".into());
            }
            let r = instruction(op, flavor)?;
            let tag = text(&r[0])?;
            let terminal = matches!(tag, "return" | "yield" | "stop");
            if terminal != (index + 1 == ops.len())
                || tag == "return" && nested
                || tag == "yield" && !nested
            {
                return Err("identity-terminator".into());
            }
            if matches!(tag, "return" | "yield") {
                strings(&r[1])?;
                continue;
            }
            let label = text(&r[1])?;
            let coordinate = format!("site{}", sites.len());
            if label.is_empty()
                || sites
                    .insert(
                        label.to_owned(),
                        Site {
                            coordinate,
                            kind: tag.to_owned(),
                        },
                    )
                    .is_some()
            {
                return Err("identity-duplicate-site".into());
            }
            match tag {
                "loop" => body(&r[5], flavor, sites, count, true)?,
                "if" => {
                    body(&r[4], flavor, sites, count, true)?;
                    body(&r[5], flavor, sites, count, true)?;
                }
                "for" => body(&r[7], flavor, sites, count, true)?,
                _ => {}
            }
        }
        Ok(())
    }
    let mut maps = SiteMaps::new();
    let mut count = 0;
    for (records, flavor, body_index) in [
        (&source.functions, Flavor::Function, 4),
        (&source.definitions, Flavor::Generic, 6),
        (&source.protocols, Flavor::Protocol, 7),
    ] {
        for (&name, r) in records {
            let mut sites = Sites::new();
            body(&r[body_index], flavor, &mut sites, &mut count, false)?;
            maps.insert(name.to_owned(), sites);
        }
    }
    Ok(maps)
}

#[derive(Default)]
struct Env<'a>(BTreeMap<&'a str, usize>);
impl<'a> Env<'a> {
    fn bind(&mut self, v: &'a Json) -> Result<usize> {
        let name = text(v)?;
        let index = self.0.len();
        if name.is_empty() || self.0.insert(name, index).is_some() {
            return Err("identity-ssa-binding".into());
        }
        Ok(index)
    }
    fn get(&self, v: &Json) -> Result<usize> {
        self.0
            .get(text(v)?)
            .copied()
            .ok_or("identity-ssa-reference".into())
    }
}

pub(super) struct Transform<'a, 'b> {
    pub source: &'b Source<'a>,
    pub sites: &'b SiteMaps,
    pub normalized: bool,
    pub output: Builder,
}
impl<'a> Transform<'a, '_> {
    fn name(&mut self, original: &Json, index: usize, depth: usize) -> Result<Json> {
        if self.normalized {
            self.output.string(&format!("v{index}"), depth)
        } else {
            self.output.copy(original, depth)
        }
    }
    fn refs(&mut self, values: &'a Json, env: &Env<'a>, depth: usize) -> Result<Json> {
        let values = list(values)?;
        let mut out = self.output.array(values.len(), depth)?;
        for v in values {
            out.push(self.name(v, env.get(v)?, depth + 1)?);
        }
        Ok(Json::Array(out))
    }
    fn binders(&mut self, values: &'a Json, env: &mut Env<'a>, depth: usize) -> Result<Json> {
        let values = list(values)?;
        let mut out = self.output.array(values.len(), depth)?;
        for v in values {
            out.push(self.name(v, env.bind(v)?, depth + 1)?);
        }
        Ok(Json::Array(out))
    }

    fn captures(
        &mut self,
        value: &'a Json,
        outer: &Env<'a>,
        inner: &mut Env<'a>,
        depth: usize,
    ) -> Result<Json> {
        let values = list(value)?;
        let mut out = self.output.array(values.len(), depth)?;
        for v in values {
            let rhs = outer.get(v)?;
            let lhs = inner.bind(v)?;
            out.push(if self.normalized {
                let mut pair = self.output.array(2, depth + 1)?;
                pair.push(self.name(v, lhs, depth + 2)?);
                pair.push(self.name(v, rhs, depth + 2)?);
                Json::Array(pair)
            } else {
                self.output.copy(v, depth + 1)?
            });
        }
        Ok(Json::Array(out))
    }

    pub fn declaration(
        &mut self,
        record: &'a [Json],
        flavor: Flavor,
        depth: usize,
    ) -> Result<Json> {
        let (inputs, body) = match flavor {
            Flavor::Function => (2, 4),
            Flavor::Generic => (4, 6),
            Flavor::Protocol => (4, 7),
        };
        let mut env = Env::default();
        let mut out = self.output.array(record.len(), depth)?;
        for (i, v) in record.iter().enumerate() {
            out.push(if i == inputs {
                let ports = list(v)?;
                let mut args = self.output.array(ports.len(), depth + 1)?;
                for p in ports {
                    let p = array(p, if flavor == Flavor::Protocol { 3 } else { 2 })?;
                    let index = env.bind(&p[0])?;
                    let mut arg = self.output.array(p.len(), depth + 2)?;
                    arg.push(if flavor == Flavor::Protocol {
                        self.output.copy(&p[0], depth + 3)?
                    } else {
                        self.name(&p[0], index, depth + 3)?
                    });
                    for v in &p[1..] {
                        arg.push(self.output.copy(v, depth + 3)?);
                    }
                    args.push(Json::Array(arg));
                }
                Json::Array(args)
            } else if i == body {
                self.body(v, &mut env, flavor, text(&record[1])?, depth + 1)?
            } else {
                self.output.copy(v, depth + 1)?
            });
        }
        Ok(Json::Array(out))
    }

    fn body(
        &mut self,
        value: &'a Json,
        env: &mut Env<'a>,
        flavor: Flavor,
        declaration: &str,
        depth: usize,
    ) -> Result<Json> {
        let ops = list(value)?;
        let mut out = self.output.array(ops.len(), depth)?;
        for op in ops {
            let r = instruction(op, flavor)?;
            let tag = text(&r[0])?;
            let mut row = self.output.array(r.len(), depth + 1)?;
            let d = depth + 2;
            row.push(self.output.copy(&r[0], d)?);
            if matches!(tag, "return" | "yield") {
                row.push(self.refs(&r[1], env, d)?);
                out.push(Json::Array(row));
                continue;
            }
            let site = self
                .sites
                .get(declaration)
                .and_then(|m| m.get(text(&r[1]).ok()?))
                .ok_or("identity-site-reference")?;
            row.push(self.output.string(&site.coordinate, d)?);
            match tag {
                "if" => {
                    row.push(self.name(&r[2], env.get(&r[2])?, d)?);
                    let mut inner = Env::default();
                    row.push(self.captures(&r[3], env, &mut inner, d)?);
                    let mut other = Env(inner.0.clone());
                    row.push(self.body(&r[4], &mut inner, flavor, declaration, d)?);
                    row.push(self.body(&r[5], &mut other, flavor, declaration, d)?);
                    row.push(self.binders(&r[6], env, d)?);
                }
                "for" => {
                    let mut inner = Env::default();
                    row.push(self.name(&r[2], inner.bind(&r[2])?, d)?);
                    row.push(self.name(&r[3], env.get(&r[3])?, d)?);
                    row.push(self.name(&r[4], env.get(&r[4])?, d)?);
                    let pairs = list(&r[5])?;
                    let mut carried = self.output.array(pairs.len(), d)?;
                    for p in pairs {
                        let p = array(p, 2)?;
                        let rhs = env.get(&p[1])?;
                        let lhs = inner.bind(&p[0])?;
                        let mut pair = self.output.array(2, d + 1)?;
                        pair.push(self.name(&p[0], lhs, d + 2)?);
                        pair.push(self.name(&p[1], rhs, d + 2)?);
                        carried.push(Json::Array(pair));
                    }
                    row.push(Json::Array(carried));
                    row.push(self.captures(&r[6], env, &mut inner, d)?);
                    row.push(self.body(&r[7], &mut inner, flavor, declaration, d)?);
                    row.push(self.binders(&r[8], env, d)?);
                }
                "op" => {
                    let generic = flavor == Flavor::Generic;
                    text(&r[2])?;
                    if generic {
                        row.push(self.output.copy(&r[2], d)?);
                    } else {
                        let binding = self
                            .source
                            .bindings
                            .get(text(&r[2])?)
                            .ok_or("identity-binding-reference")?;
                        row.push(if self.normalized {
                            let mut b = self.output.array(3, d)?;
                            b.push(self.output.string("operation", d + 1)?);
                            b.push(self.output.copy(&binding[1], d + 1)?);
                            b.push(self.output.copy(&binding[2], d + 1)?);
                            Json::Array(b)
                        } else {
                            self.output.copy(&r[2], d)?
                        });
                    }
                    let attrs = if generic { 4 } else { 3 };
                    for v in &r[3..=attrs] {
                        strings(v)?;
                        row.push(self.output.copy(v, d)?);
                    }
                    row.push(self.refs(&r[attrs + 1], env, d)?);
                    row.push(self.binders(&r[attrs + 2], env, d)?);
                }
                "local" | "call" | "apply" => {
                    let offset = usize::from(tag == "local");
                    for v in &r[2..=2 + offset] {
                        text(v)?;
                        row.push(self.output.copy(v, d)?);
                    }
                    let target = text(&r[2 + offset])?;
                    if tag == "apply" {
                        if !self.source.functions.contains_key(target)
                            && !self.source.definitions.contains_key(target)
                            && !self.source.configurations.contains_key(target)
                        {
                            return Err("identity-callee-reference".into());
                        }
                    } else if tag == "local" {
                        if !self.source.functions.contains_key(target)
                            && !self.source.configurations.contains_key(target)
                        {
                            return Err("identity-callee-reference".into());
                        }
                    } else {
                        let dependencies = self
                            .source
                            .dependencies
                            .get(declaration)
                            .ok_or("identity-protocol-reference")?;
                        if !dependencies.contains(target) {
                            return Err("identity-dependency-reference".into());
                        }
                    }
                    let offset = if tag == "apply" {
                        strings(&r[3])?;
                        row.push(self.output.copy(&r[3], d)?);
                        1
                    } else {
                        offset
                    };
                    row.push(self.refs(&r[3 + offset], env, d)?);
                    row.push(self.binders(&r[4 + offset], env, d)?);
                }
                "message" => {
                    for v in &r[2..5] {
                        text(v)?;
                        row.push(self.output.copy(v, d)?);
                    }
                    row.push(self.name(&r[5], env.get(&r[5])?, d)?);
                    row.push(self.name(&r[6], env.bind(&r[6])?, d)?);
                }
                "stop" => {
                    text(&r[2])?;
                    text(&r[3])?;
                    row.push(self.output.copy(&r[2], d)?);
                    row.push(self.output.copy(&r[3], d)?);
                }
                "loop" => {
                    let count = array(&r[2], 2)?;
                    match text(&count[0])? {
                        "constant" => {
                            super::super::io::natural(&count[1])?;
                        }
                        "parameter" => {
                            text(&count[1])?;
                        }
                        _ => return Err("identity-loop-count".into()),
                    }
                    row.push(self.output.copy(&r[2], d)?);
                    let mut inner = Env::default();
                    let pairs = list(&r[3])?;
                    let mut carried = self.output.array(pairs.len(), d)?;
                    for p in pairs {
                        let p = array(p, 2)?;
                        // Evaluate RHS only in outer, bind LHS only in fresh inner.
                        let rhs = env.get(&p[1])?;
                        let lhs = inner.bind(&p[0])?;
                        let mut pair = self.output.array(2, d + 1)?;
                        pair.push(self.name(&p[0], lhs, d + 2)?);
                        pair.push(self.name(&p[1], rhs, d + 2)?);
                        carried.push(Json::Array(pair));
                    }
                    row.push(Json::Array(carried));
                    let values = list(&r[4])?;
                    let mut captures = self.output.array(values.len(), d)?;
                    for v in values {
                        let rhs = env.get(v)?;
                        let lhs = inner.bind(v)?;
                        captures.push(if self.normalized {
                            let mut pair = self.output.array(2, d + 1)?;
                            pair.push(self.name(v, lhs, d + 2)?);
                            pair.push(self.name(v, rhs, d + 2)?);
                            Json::Array(pair)
                        } else {
                            self.output.copy(v, d + 1)?
                        });
                    }
                    row.push(Json::Array(captures));
                    row.push(self.body(&r[5], &mut inner, flavor, declaration, d)?);
                    // Results do not become available to the nested body.
                    row.push(self.binders(&r[6], env, d)?);
                }
                _ => return Err("identity-instruction".into()),
            }
            out.push(Json::Array(row));
        }
        Ok(Json::Array(out))
    }
}
