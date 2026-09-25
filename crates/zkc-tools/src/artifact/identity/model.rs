//! Borrowed declaration indexes. These check shapes and references, not types,
//! capabilities, affine use, or source-to-candidate correspondence.
use super::{Json, Result, array, list, text};
use std::collections::{BTreeMap, BTreeSet};

pub(super) type Records<'a> = BTreeMap<&'a str, &'a [Json]>;

pub(super) struct Source<'a> {
    pub common: &'a [Json],
    pub bindings: Records<'a>,
    pub functions: Records<'a>,
    pub protocols: Records<'a>,
    pub dependencies: BTreeMap<&'a str, BTreeSet<&'a str>>,
    pub instances: Records<'a>,
    pub entries: Records<'a>,
    pub definitions: Records<'a>,
    pub configurations: Records<'a>,
    /// Configuration -> final generic definition; never generated callables.
    pub finals: BTreeMap<&'a str, &'a str>,
}

pub(super) fn strings(v: &Json) -> Result<()> {
    for v in list(v)? {
        text(v)?;
    }
    Ok(())
}
pub(super) fn pairs(v: &Json) -> Result<()> {
    let mut names = BTreeSet::new();
    for v in list(v)? {
        let r = array(v, 2)?;
        if !names.insert(text(&r[0])?) {
            return Err("identity-duplicate-name".into());
        }
        text(&r[1])?;
    }
    Ok(())
}
fn records<'a>(v: &'a Json, tag: &str, len: usize) -> Result<Records<'a>> {
    let mut out = BTreeMap::new();
    for v in list(v)? {
        let r = array(v, len)?;
        if text(&r[0])? != tag {
            return Err("identity-declaration".into());
        }
        let name = text(&r[1])?;
        if name.is_empty() || out.insert(name, r).is_some() {
            return Err("identity-duplicate-symbol".into());
        }
    }
    Ok(out)
}
impl<'a> Source<'a> {
    pub fn parse(value: &'a Json) -> Result<Self> {
        let top = list(value)?;
        let (common, definitions, configurations) = match top.first().and_then(Json::as_str) {
            Some("zkc.protocol/1") => (array(value, 6)?, BTreeMap::new(), BTreeMap::new()),
            Some("zkc.library/1") => {
                let r = array(value, 4)?;
                (
                    array(&r[3], 6)?,
                    records(&r[1], "generic_function", 7)?,
                    records(&r[2], "configure", 5)?,
                )
            }
            _ => return Err("identity-source-version".into()),
        };
        if common[0] != "zkc.protocol/1" {
            return Err("identity-source-version".into());
        }
        let mut bindings = BTreeMap::new();
        for v in list(&common[1])? {
            let r = array(v, 4)?;
            if bindings.insert(text(&r[0])?, r).is_some() {
                return Err("identity-duplicate-symbol".into());
            }
            text(&r[1])?;
            strings(&r[2])?;
            text(&r[3])?;
        }
        let functions = records(&common[2], "function", 6)?;
        let protocols = records(&common[3], "protocol", 8)?;
        let instances = records(&common[4], "instance", 6)?;
        let entries = records(&common[5], "entry", 3)?;
        // The original carrier has a single declaration namespace. Do not
        // silently resolve an ambiguous function/configuration by precedence.
        let mut names = BTreeSet::new();
        for group in [
            &bindings,
            &functions,
            &protocols,
            &instances,
            &entries,
            &definitions,
            &configurations,
        ] {
            for &name in group.keys() {
                if !names.insert(name) {
                    return Err("identity-duplicate-symbol".into());
                }
            }
        }
        for r in functions.values() {
            pairs(&r[2])?;
            strings(&r[3])?;
            let origin = array(&r[5], 2)?;
            text(&origin[0])?;
            pairs(&origin[1])?;
        }
        for r in definitions.values() {
            pairs(&r[2])?;
            pairs(&r[4])?;
            strings(&r[5])?;
            for q in list(&r[3])? {
                let q = array(q, 2)?;
                text(&q[0])?;
                strings(&q[1])?;
            }
        }
        let mut protocol_dependencies = BTreeMap::new();
        for (&name, r) in &protocols {
            strings(&r[2])?;
            strings(&r[3])?;
            let mut ports = BTreeSet::new();
            for p in list(&r[4])? {
                let p = array(p, 3)?;
                if !ports.insert(text(&p[0])?) {
                    return Err("identity-duplicate-name".into());
                }
                text(&p[1])?;
                text(&p[2])?;
            }
            for p in list(&r[5])? {
                let p = array(p, 2)?;
                text(&p[0])?;
                text(&p[1])?;
            }
            let mut dependencies = BTreeSet::new();
            for dep in list(&r[6])? {
                let d = array(dep, 3)?;
                if !dependencies.insert(text(&d[0])?) {
                    return Err("identity-duplicate-name".into());
                }
                if !protocols.contains_key(text(&d[1])?) {
                    return Err("identity-protocol-reference".into());
                }
                pairs(&d[2])?;
            }
            protocol_dependencies.insert(name, dependencies);
        }
        for r in instances.values() {
            if !protocols.contains_key(text(&r[2])?) {
                return Err("identity-protocol-reference".into());
            }
            pairs(&r[3])?;
            pairs(&r[4])?;
            pairs(&r[5])?;
            for dep in list(&r[4])? {
                if !instances.contains_key(text(&array(dep, 2)?[1])?) {
                    return Err("identity-instance-reference".into());
                }
            }
        }
        for r in entries.values() {
            if !instances.contains_key(text(&r[2])?) {
                return Err("identity-instance-reference".into());
            }
        }
        for r in configurations.values() {
            text(&r[2])?;
            pairs(&r[3])?;
            pairs(&r[4])?;
        }
        let mut source = Self {
            common,
            bindings,
            functions,
            protocols,
            dependencies: protocol_dependencies,
            instances,
            entries,
            definitions,
            configurations,
            finals: BTreeMap::new(),
        };
        source.resolve_finals()?;
        Ok(source)
    }

    fn resolve_finals(&mut self) -> Result<()> {
        // Iterative memoization: long configuration chains do not consume the
        // native stack, or duplicate inherited assignment maps for every node.
        for &name in self.configurations.keys() {
            let mut current = name;
            let mut chain = BTreeSet::new();
            let final_name = loop {
                if self.definitions.contains_key(current) {
                    break current;
                }
                if let Some(&target) = self.finals.get(current) {
                    break target;
                }
                if !chain.insert(current) {
                    return Err("identity-configuration-cycle".into());
                }
                let r = self
                    .configurations
                    .get(current)
                    .ok_or("identity-configuration-reference")?;
                current = text(&r[2])?;
            };
            for node in chain {
                self.finals.insert(node, final_name);
            }
        }
        Ok(())
    }

    pub fn assignments(
        &self,
        name: &'a str,
        work: &mut usize,
        closed: bool,
    ) -> Result<Vec<(&'a Json, &'a Json)>> {
        let final_name = self
            .finals
            .get(name)
            .ok_or("identity-configuration-reference")?;
        let definition = self.definitions[final_name];
        let mut assigned = BTreeMap::new();
        let mut current = name;
        while let Some(r) = self.configurations.get(current) {
            *work = work
                .checked_add(1 + list(&r[3])?.len())
                .ok_or("identity-work-limit")?;
            if *work > 200_000 {
                return Err("identity-work-limit".into());
            }
            for v in list(&r[3])? {
                let p = array(v, 2)?;
                if assigned.insert(text(&p[0])?, &p[1]).is_some() {
                    return Err("identity-configuration-rebinding".into());
                }
            }
            current = text(&r[2])?;
        }
        let mut out = Vec::new();
        for p in list(&definition[2])? {
            let p = array(p, 2)?;
            if let Some(value) = assigned.remove(text(&p[0])?) {
                out.push((&p[0], value));
            } else if closed {
                return Err("identity-open-configuration".into());
            }
        }
        if !assigned.is_empty() {
            return Err("identity-configuration-parameter".into());
        }
        Ok(out)
    }
}

#[derive(Default)]
pub(super) struct Closure<'a> {
    pub instances: BTreeSet<&'a str>,
    pub protocols: BTreeSet<&'a str>,
    pub functions: BTreeSet<&'a str>,
    pub definitions: BTreeSet<&'a str>,
    pub configurations: BTreeSet<&'a str>,
    pub closed_configurations: BTreeSet<&'a str>,
}
impl<'a> Closure<'a> {
    pub fn select(source: &Source<'a>, entry: &str) -> Result<Self> {
        let entry = source
            .entries
            .get(entry)
            .ok_or("identity-entry-reference")?;
        let mut out = Self::default();
        // Each declaration is queued only once, including shared children and
        // uncalled declared dependencies. Loops are never unrolled.
        let root = text(&entry[2])?;
        let mut pending = vec![root];
        out.instances.insert(root);
        while let Some(name) = pending.pop() {
            let r = source
                .instances
                .get(name)
                .ok_or("identity-instance-reference")?;
            out.protocols.insert(text(&r[2])?);
            for dep in list(&r[4])? {
                let child = text(&array(dep, 2)?[1])?;
                if out.instances.insert(child) {
                    pending.push(child);
                }
            }
        }
        pending.extend(out.protocols.iter().copied());
        while let Some(name) = pending.pop() {
            let r = source
                .protocols
                .get(name)
                .ok_or("identity-protocol-reference")?;
            for dep in list(&r[6])? {
                let child = text(&array(dep, 3)?[1])?;
                if out.protocols.insert(child) {
                    pending.push(child);
                }
            }
            out.callees(&r[7], source)?;
        }
        // Local callable structure contributes its entire transitive body to
        // identity, including helpers with no direct protocol call.
        pending.extend(out.functions.iter().copied());
        pending.extend(out.definitions.iter().copied());
        let mut visited = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if !visited.insert(name) {
                continue;
            }
            let body = if let Some(record) = source.functions.get(name) {
                &record[4]
            } else {
                &source
                    .definitions
                    .get(name)
                    .ok_or("identity-callee-reference")?[6]
            };
            let mut bodies = vec![body];
            while let Some(body) = bodies.pop() {
                for instruction in list(body)? {
                    let row = list(instruction)?;
                    match row.first().and_then(Json::as_str) {
                        Some("if") => {
                            let r = array(instruction, 7)?;
                            bodies.push(&r[4]);
                            bodies.push(&r[5]);
                        }
                        Some("for") => bodies.push(&array(instruction, 9)?[7]),
                        _ => {}
                    }
                    if row.first().and_then(Json::as_str) == Some("apply") {
                        let row = array(instruction, 6)?;
                        let callee = text(&row[2])?;
                        if source.functions.contains_key(callee) {
                            if out.functions.insert(callee) {
                                pending.push(callee);
                            }
                        } else if source.definitions.contains_key(callee) {
                            if out.definitions.insert(callee) {
                                pending.push(callee);
                            }
                        } else {
                            let definition = source
                                .finals
                                .get(callee)
                                .ok_or("identity-callee-reference")?;
                            out.configurations.insert(callee);
                            if source.functions.contains_key(name) && list(&row[3])?.is_empty() {
                                out.closed_configurations.insert(callee);
                            }
                            if out.definitions.insert(definition) {
                                pending.push(definition);
                            }
                        }
                    }
                }
            }
        }
        Ok(out)
    }
    fn callees(&mut self, body: &'a Json, source: &Source<'a>) -> Result<()> {
        // Source depth was checked before this traversal.
        for op in list(body)? {
            let r = list(op)?;
            match r.first().and_then(Json::as_str) {
                Some("local") => {
                    let r = array(op, 6)?;
                    let name = text(&r[3])?;
                    if source.functions.contains_key(name) {
                        self.functions.insert(name);
                    } else {
                        let final_name =
                            source.finals.get(name).ok_or("identity-callee-reference")?;
                        self.configurations.insert(name);
                        self.closed_configurations.insert(name);
                        self.definitions.insert(final_name);
                    }
                }
                Some("loop") => self.callees(&array(op, 7)?[5], source)?,
                _ => (),
            }
        }
        Ok(())
    }
}
