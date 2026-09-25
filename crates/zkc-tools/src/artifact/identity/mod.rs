//! Normalized construction source resolution and protocol identity.
//!
//! This is an independent, bounded structural derivation from ORIGINAL source.
//! It neither specializes generic bodies nor admits cryptographic semantics.
//! CheckedBundle must first authenticate the complete original source/candidate.
use super::io::{self, Result, array, list, text};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

mod body;
mod bounds;
mod model;
use body::{Flavor, SiteMaps, Transform};
use bounds::Builder;
use model::{Closure, Source};

pub(super) struct Identity {
    pub source: Json,
    pub descriptor: Json,
    pub normalized: Json,
    sites: SiteMaps,
    instance_protocols: BTreeMap<String, String>,
}

impl Identity {
    /// Call only after complete original admission in the execution path.
    /// Inspection uses the same structural code, but makes no admission claim.
    pub fn derive(original: &Json, descriptor: &Json) -> Result<Self> {
        bounds::source_tree(original)?;
        bounds::source_tree(descriptor)?;
        let source = Source::parse(original)?;
        let sites = body::gather(&source)?;
        let resolved_descriptor = resolve_descriptor(descriptor, &source, &sites)?;
        let closure = Closure::select(&source, text(&array(descriptor, 9)?[1])?)?;
        // Also validates full bodies, including excluded declarations. Full
        // type/affinity/installed-operation admission still belongs to the host.
        let resolved_source = resolve_source(original, &source, &sites)?;
        let normalized = normalize(&source, &sites, &closure, text(&resolved_descriptor[1])?)?;
        let instance_protocols = source
            .instances
            .iter()
            .map(|(&name, r)| Ok((name.to_owned(), text(&r[2])?.to_owned())))
            .collect::<Result<_>>()?;
        Ok(Self {
            source: resolved_source,
            descriptor: resolved_descriptor,
            normalized,
            sites,
            instance_protocols,
        })
    }

    pub fn source_bytes(&self) -> Result<Vec<u8>> {
        bounds::serialize(&self.source, 1 << 20)
    }

    /// Retain all key bytes, registry names, selections and list order. Only
    /// receive selectors change, through the original instance's protocol.
    pub fn configuration(&self, original: &Json) -> Result<Json> {
        Builder::default().measure(original, 0, io::INPUT_LIMIT)?;
        let r = array(original, 4)?;
        if r[0] != "zkc.public-configuration/1" {
            return Err("identity-configuration-version".into());
        }
        for group in &r[1..3] {
            for row in list(group)? {
                let row = array(row, 3)?;
                for v in row {
                    text(v)?;
                }
            }
        }
        let mut b = Builder::default();
        let mut out = b.array(4, 0)?;
        for v in &r[..3] {
            out.push(b.copy(v, 1)?);
        }
        let rows = list(&r[3])?;
        let mut receives = b.array(rows.len(), 1)?;
        for row in rows {
            let r = array(row, 4)?;
            let protocol = self
                .instance_protocols
                .get(text(&r[0])?)
                .ok_or("identity-receive-instance")?;
            let site = self
                .sites
                .get(protocol)
                .and_then(|m| m.get(text(&r[2]).ok()?))
                .filter(|s| s.kind == "message")
                .ok_or("identity-receive-site")?;
            text(&r[1])?;
            text(&r[3])?;
            let mut row = b.array(4, 2)?;
            for (i, v) in r.iter().enumerate() {
                row.push(if i == 2 {
                    b.string(&site.coordinate, 3)?
                } else {
                    b.copy(v, 3)?
                });
            }
            receives.push(Json::Array(row));
        }
        out.push(Json::Array(receives));
        Ok(Json::Array(out))
    }

    pub fn binding(&self, context: &Json, public: &Json, configuration: &Json) -> Result<Vec<u8>> {
        let mut b = Builder::default();
        let mut root = b.array(6, 0)?;
        // One root for both identity policies: the descriptor it embeds names
        // the policy, so the two kinds of root never coincide.
        root.push(b.string("zkc.artifact-binding/1", 1)?);
        // Incremental aggregate accounting precedes each subtree clone. In
        // particular, configuration/static-argument amplification is bounded.
        for v in [
            &self.normalized,
            &self.descriptor,
            context,
            public,
            configuration,
        ] {
            root.push(b.copy(v, 1)?);
        }
        zkc_runtime::logical::encode_tree(&Json::Array(root)).map_err(|e| e.to_string())
    }
}

// Source admission permits ordinary helper copies to share a concrete name's
// logical origin. Normalized selection must preserve membership in both
// directions, rather than assume those bodies number their labels alike.
#[derive(Default)]
struct SelectorCoordinates {
    forward: BTreeMap<(String, String), Option<String>>,
    reverse: BTreeMap<(String, String), Option<String>>,
}
impl SelectorCoordinates {
    fn derive(source: &Source<'_>, sites: &SiteMaps) -> Result<Self> {
        fn insert(
            index: &mut BTreeMap<(String, String), Option<String>>,
            owner: &str,
            label: &str,
            target: &str,
        ) {
            index
                .entry((owner.to_owned(), label.to_owned()))
                .and_modify(|old| {
                    if old.as_deref() != Some(target) {
                        *old = None;
                    }
                })
                .or_insert_with(|| Some(target.to_owned()));
        }
        let mut result = Self::default();
        for (&name, record) in &source.functions {
            let origin = text(&array(&record[5], 2)?[0])?;
            if let Some(body) = sites.get(name) {
                for (label, site) in body {
                    for owner in [name, origin] {
                        insert(&mut result.forward, owner, label, &site.coordinate);
                        insert(&mut result.reverse, owner, &site.coordinate, label);
                    }
                }
            }
        }
        Ok(result)
    }

    fn check(&self, owner: &str, raw: &str, coordinate: &str) -> Result<()> {
        for (index, key, expected) in [
            (&self.forward, raw, coordinate),
            (&self.reverse, coordinate, raw),
        ] {
            if let Some(actual) = index.get(&(owner.to_owned(), key.to_owned()))
                && actual.as_deref() != Some(expected)
            {
                return Err("construction-selector-coordinates".into());
            }
        }
        Ok(())
    }
}

fn resolve_descriptor(value: &Json, source: &Source<'_>, sites: &SiteMaps) -> Result<Json> {
    let r = array(value, 9)?;
    if r[0] != "zkc.construction/1"
        || r[8] != "normalized"
        || !matches!(
            r[7].as_str(),
            Some(
                "merlin3.bls12-381.fr64be/1"
                    | "merlin3.ristretto255.scalar64le/1"
                    | "merlin3.koala-bear.ext8-binomial3.rejection31le/1"
                    | "spongefish0.7.4.keccak.bls12-381.fr64be/1"
            )
        )
    {
        return Err("identity-descriptor".into());
    }
    for i in [1, 2, 3] {
        text(&r[i])?;
    }
    io::natural(&r[6])?;
    for binding in list(&r[4])? {
        let binding = array(binding, 2)?;
        text(&binding[0])?;
        for port in list(&binding[1])? {
            let port = array(port, 2)?;
            text(&port[0])?;
            text(&port[1])?;
        }
    }
    let draws = array(&r[5], 2)?;
    text(&draws[0])?;
    let coordinates = SelectorCoordinates::derive(source, sites)?;
    let mut b = Builder::default();
    let mut out = b.array(9, 0)?;
    for (i, v) in r.iter().enumerate() {
        out.push(if i == 5 {
            let mut selection = b.array(2, 1)?;
            selection.push(b.copy(&draws[0], 2)?);
            let mut rows = b.array(list(&draws[1])?.len(), 2)?;
            for draw in list(&draws[1])? {
                let p = array(draw, 2)?;
                let name = text(&p[0])?;
                let target = if source.functions.contains_key(name)
                    || source.definitions.contains_key(name)
                {
                    name
                } else {
                    source
                        .finals
                        .get(name)
                        .copied()
                        .ok_or("identity-draw-target")?
                };
                let site = sites
                    .get(target)
                    .and_then(|m| m.get(text(&p[1]).ok()?))
                    .ok_or("identity-draw-site")?;
                // The owner's site supplies coordinates, not proof that this
                // owner executes the draw. An origin alias may also reach a
                // primitive in another function at the same raw label while
                // its own occurrence is a call. Construction checks actual
                // selected primitives after expansion; preserve that family.
                coordinates.check(name, text(&p[1])?, &site.coordinate)?;
                let mut row = b.array(2, 3)?;
                row.push(b.copy(&p[0], 4)?);
                row.push(b.string(&site.coordinate, 4)?);
                rows.push(Json::Array(row));
            }
            selection.push(Json::Array(rows));
            Json::Array(selection)
        } else {
            b.copy(v, 1)?
        });
    }
    Ok(Json::Array(out))
}

fn resolve_source(original: &Json, source: &Source<'_>, sites: &SiteMaps) -> Result<Json> {
    let mut t = Transform {
        source,
        sites,
        normalized: false,
        output: Builder::default(),
    };
    fn common(t: &mut Transform<'_, '_>, depth: usize) -> Result<Json> {
        let mut out = t.output.array(6, depth)?;
        for (i, v) in t.source.common.iter().enumerate() {
            out.push(if matches!(i, 2 | 3) {
                let mut group = t.output.array(list(v)?.len(), depth + 1)?;
                for r in list(v)? {
                    group.push(t.declaration(
                        list(r)?,
                        if i == 2 {
                            Flavor::Function
                        } else {
                            Flavor::Protocol
                        },
                        depth + 2,
                    )?);
                }
                Json::Array(group)
            } else {
                t.output.copy(v, depth + 1)?
            });
        }
        Ok(Json::Array(out))
    }
    if original[0] == "zkc.protocol/1" {
        return common(&mut t, 0);
    }
    let mut out = t.output.array(4, 0)?;
    out.push(t.output.string("zkc.library/1", 1)?);
    let mut definitions = t.output.array(list(&original[1])?.len(), 1)?;
    for r in list(&original[1])? {
        definitions.push(t.declaration(list(r)?, Flavor::Generic, 2)?);
    }
    out.push(Json::Array(definitions));
    let mut configurations = t.output.array(list(&original[2])?.len(), 1)?;
    for v in list(&original[2])? {
        let r = array(v, 5)?;
        let target = source
            .finals
            .get(text(&r[1])?)
            .ok_or("identity-configuration-reference")?;
        let map = sites.get(*target).ok_or("identity-site-reference")?;
        let mut row = t.output.array(5, 2)?;
        for v in &r[..4] {
            row.push(t.output.copy(v, 3)?);
        }
        let mut choices = t.output.array(list(&r[4])?.len(), 3)?;
        for p in list(&r[4])? {
            let p = array(p, 2)?;
            let site = map
                .get(text(&p[0])?)
                .filter(|s| s.kind == "op")
                .ok_or("identity-using-site")?;
            let mut pair = t.output.array(2, 4)?;
            pair.push(t.output.string(&site.coordinate, 5)?);
            pair.push(t.output.copy(&p[1], 5)?);
            choices.push(Json::Array(pair));
        }
        row.push(Json::Array(choices));
        configurations.push(Json::Array(row));
    }
    out.push(Json::Array(configurations));
    out.push(common(&mut t, 1)?);
    Ok(Json::Array(out))
}

fn normalize(
    source: &Source<'_>,
    sites: &SiteMaps,
    closure: &Closure<'_>,
    entry: &str,
) -> Result<Json> {
    let mut t = Transform {
        source,
        sites,
        normalized: true,
        output: Builder::default(),
    };
    let mut out = t.output.array(7, 0)?;
    out.push(t.output.string("zkc.protocol-identity/1", 1)?);
    out.push(
        t.output.record(
            source
                .entries
                .get(entry)
                .ok_or("identity-entry-reference")?,
            1,
        )?,
    );
    let mut instances = t.output.array(closure.instances.len(), 1)?;
    for name in &closure.instances {
        instances.push(t.output.record(source.instances[name], 2)?);
    }
    out.push(Json::Array(instances));
    for (selected, records, flavor) in [
        (&closure.protocols, &source.protocols, Flavor::Protocol),
        (&closure.functions, &source.functions, Flavor::Function),
        (&closure.definitions, &source.definitions, Flavor::Generic),
    ] {
        let mut group = t.output.array(selected.len(), 1)?;
        for name in selected {
            group.push(t.declaration(records[name], flavor, 2)?);
        }
        out.push(Json::Array(group));
    }
    let mut configurations = t.output.array(closure.configurations.len(), 1)?;
    let mut work = 0;
    for &name in &closure.configurations {
        let r = source.configurations[name];
        let assignments = source.assignments(
            name,
            &mut work,
            closure.closed_configurations.contains(name),
        )?;
        let mut row = t.output.array(5, 2)?;
        row.push(t.output.copy(&r[0], 3)?);
        row.push(t.output.copy(&r[1], 3)?);
        row.push(t.output.string(source.finals[name], 3)?);
        let mut args = t.output.array(assignments.len(), 3)?;
        for (parameter, value) in assignments {
            let mut pair = t.output.array(2, 4)?;
            pair.push(t.output.copy(parameter, 5)?);
            pair.push(t.output.copy(value, 5)?);
            args.push(Json::Array(pair));
        }
        row.push(Json::Array(args));
        row.push(Json::Array(t.output.array(0, 3)?));
        configurations.push(Json::Array(row));
    }
    out.push(Json::Array(configurations));
    Ok(Json::Array(out))
}

/// `zkc inspect-artifact-identity SOURCE DESCRIPTOR [CONFIGURATION]`.
/// The output is for independent vectors, not source/candidate admission.
pub fn inspect(args: &[String]) -> Result<Json> {
    let (source, descriptor, configuration) = match args {
        [s, d] => (s, d, None),
        [s, d, c] => (s, d, Some(c)),
        _ => {
            return Err(
                "usage: zkc inspect-artifact-identity SOURCE DESCRIPTOR [CONFIGURATION]".into(),
            );
        }
    };
    let bytes = io::read(source, 1 << 20)?;
    let original = io::parse(&bytes, 1 << 20)?;
    let descriptor = io::parse(&io::read(descriptor, 1 << 20)?, 1 << 20)?;
    let identity = Identity::derive(&original, &descriptor)?;
    let configuration = configuration
        .map(|p| {
            let c = io::parse(&io::read(p, io::INPUT_LIMIT)?, io::INPUT_LIMIT)?;
            identity.configuration(&c)
        })
        .transpose()?;
    Ok(json!({
        "status": "inspected", "admission": "not-checked",
        "source_sha256": io::hex(&Sha256::digest(&bytes)),
        "resolved_source": identity.source,
        "resolved_descriptor": identity.descriptor,
        "normalized_protocol": identity.normalized,
        "resolved_configuration": configuration,
    }))
}

#[cfg(test)]
mod tests;
