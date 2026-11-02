//! Independently reconstructed semantic coverage and ordinary supply views.
use super::{InterfaceError as E, Result, raw::*, require, schemas, validate};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

/// These purposes confer different authority even when their native slices match.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelectionPurpose {
    OrdinarySupply,
    SetupAssociation,
    SpecificationObservation,
}

/// An outstanding structural supply obligation, including zero-storage ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryRequirement {
    pub port: u32,
    pub path: Vec<u32>,
    pub role: String,
    pub output: bool,
    pub facet: Option<Facet>,
    pub reason: &'static str,
}
#[derive(Debug)]
pub(super) struct View {
    pub definition: Port,
    pub path: Vec<u32>,
    pub role: u32,
    pub public: bool,
}

fn child_placement<'a>(s: &Schema, p: &'a Placement, i: usize) -> &'a Placement {
    match p {
        Placement::Product { fields, .. } => &fields[if s.kind == Kind::Array { 0 } else { i }],
        _ => p,
    }
}
/// Ordinary semantic atoms include empty subtrees; physical indices alone cannot
/// distinguish two empty fields or two participants sharing one native operand.
fn atoms(
    s: &Schema,
    p: &Placement,
    path: &mut Vec<u32>,
    role: u32,
    out: &mut BTreeSet<Vec<u32>>,
    work: &mut schemas::Schemas<'_>,
) -> Result<()> {
    work.charge(1 + path.len() + s.fields.len())?;
    if s.kind.is_handle() {
        return Ok(());
    }
    if s.fields.is_empty() {
        if super::placement::ordinary_roles(s, p).is_some_and(|roles| roles.contains(&role)) {
            out.insert(path.clone());
        }
    } else {
        for (i, f) in s.fields.iter().enumerate() {
            path.push(i as u32);
            atoms(&f.schema, child_placement(s, p, i), path, role, out, work)?;
            path.pop();
        }
    }
    Ok(())
}
pub(super) fn check_public(
    protocol: &Protocol,
    public: &[PublicSelection],
    verifier: &str,
    work: &mut schemas::Schemas<'_>,
) -> Result<()> {
    let role = protocol
        .roles
        .iter()
        .position(|r| r == verifier)
        .ok_or(E::Selection)? as u32;
    let mut required = BTreeSet::new();
    for port in &protocol.inputs {
        let mut paths = BTreeSet::new();
        atoms(
            &port.schema,
            &port.placement,
            &mut Vec::new(),
            role,
            &mut paths,
            work,
        )?;
        required.extend(paths.into_iter().map(|p| (port.index, p)));
    }
    let mut covered = BTreeSet::new();
    let mut previous: Option<&PublicSelection> = None;
    for selected in public {
        work.charge(1 + selected.path.len())?;
        require(selected.role == verifier, E::Selection)?;
        if let Some(old) = previous {
            require(
                (old.port, &old.path) < (selected.port, &selected.path)
                    && (old.port != selected.port || !selected.path.starts_with(&old.path)),
                E::Selection,
            )?;
        }
        previous = Some(selected);
        let port = protocol
            .inputs
            .get(selected.port as usize)
            .ok_or(E::Selection)?;
        let (s, p) =
            validate::selected_schema(port, &selected.path, SelectionPurpose::OrdinarySupply)?;
        validate::public_data(s, work)?;
        require(
            super::placement::ordinary_roles(s, p).is_some_and(|roles| roles.contains(&role)),
            E::Selection,
        )?;
        let mut paths = BTreeSet::new();
        atoms(s, p, &mut selected.path.clone(), role, &mut paths, work)?;
        for path in paths {
            require(covered.insert((selected.port, path)), E::Selection)?;
        }
    }
    require(covered == required, E::Selection)
}

/// Alias generation is deterministic but never authority. Reserve all original
/// names before naming projected children, including unused original names.
fn alias_candidate(port: &Port, path: &[u32]) -> String {
    let mut s = &port.schema;
    let mut name = port.name.clone();
    for &i in path {
        let f = &s.fields[i as usize];
        name.push('_');
        name.push_str(&f.name);
        s = &f.schema;
    }
    bounded_alias(port, path, name)
}
fn bounded_alias(port: &Port, path: &[u32], mut name: String) -> String {
    if name.len() > 120 {
        let mut coordinate = port.index.to_string().into_bytes();
        for step in path {
            let text = step.to_string();
            coordinate.extend_from_slice(&(text.len() as u64).to_le_bytes());
            coordinate.extend_from_slice(text.as_bytes());
        }
        let hash = crate::io::bytes::hex(&Sha256::digest(&coordinate));
        let mut end = 48.min(name.len());
        while !name.is_char_boundary(end) {
            end -= 1;
        }
        name = format!("{}_{}", &name[..end], hash);
    }
    name
}
fn allocate_alias_metered(
    mut name: String,
    used: &mut BTreeSet<String>,
    mut work: Option<&mut Work>,
) -> Result<String> {
    let base = name.clone();
    let mut ordinal = 2;
    loop {
        if let Some(work) = work.as_deref_mut() {
            work.lookup(used.len())?;
            work.charge(name.len())?;
        }
        if used.insert(name.clone()) {
            return Ok(name);
        }
        name = format!("{base}_{ordinal}");
        ordinal += 1;
    }
}

/// Generated families allocate aliases from their exact filtered field roster.
/// The SDK's invocation aliases may include additional context fields; mapping
/// between these rosters always uses coordinates, never alias parsing.
pub(super) fn family_aliases(coordinates: &[(&Port, &[u32])]) -> Vec<String> {
    family_aliases_metered(coordinates, None).expect("unmetered alias allocation")
}
fn alias_bytes(port: &Port, path: &[u32]) -> usize {
    let mut schema = &port.schema;
    let mut bytes = port.name.len();
    for &step in path {
        let field = &schema.fields[step as usize];
        bytes += 1 + field.name.len();
        schema = &field.schema;
    }
    bytes
}
fn family_aliases_metered(
    coordinates: &[(&Port, &[u32])],
    mut work: Option<&mut Work>,
) -> Result<Vec<String>> {
    let mut used = BTreeSet::new();
    let mut result = vec![String::new(); coordinates.len()];
    for whole in [true, false] {
        for (i, (port, path)) in coordinates.iter().enumerate() {
            if let Some(work) = work.as_deref_mut() {
                work.charge(1 + path.len())?;
            }
            if path.is_empty() != whole {
                continue;
            }
            if let Some(work) = work.as_deref_mut() {
                work.charge(alias_bytes(port, path))?;
            }
            // Generated families also bound and collision-check whole names.
            let name = alias_candidate(port, path);
            result[i] = allocate_alias_metered(name, &mut used, work.as_deref_mut())?;
        }
    }
    Ok(result)
}

/// A separate admission algorithm has one cumulative work allowance across
/// indexing, both supply directions, coverage and classification. Each
/// reconstructed supply plan separately charges its retained descriptors.
pub(super) struct Work {
    pub remaining: usize,
    descriptor_bytes: usize,
}
impl Work {
    pub fn new(limits: super::InterfaceLimits) -> Self {
        Self {
            remaining: limits.work,
            descriptor_bytes: limits.descriptor_bytes,
        }
    }
    pub fn charge(&mut self, count: usize) -> Result<()> {
        self.remaining = self.remaining.checked_sub(count).ok_or(E::WorkLimit)?;
        Ok(())
    }
    pub(super) fn lookup(&mut self, entries: usize) -> Result<()> {
        self.charge(1 + entries.checked_ilog2().unwrap_or(0) as usize)
    }
}
/// Per-node facts shared by every placed role's walk over one supply plan.
/// Keys are the addresses of the admitted document's schema and placement
/// nodes, which outlive the reconstruction.
#[derive(Default)]
struct Memo {
    ordinary: BTreeMap<(usize, usize), Option<Vec<u32>>>,
    costs: BTreeMap<usize, usize>,
    telescopes: BTreeMap<usize, Vec<u32>>,
}
impl Memo {
    fn key(s: &Schema, p: &Placement) -> (usize, usize) {
        (
            std::ptr::from_ref(s) as usize,
            std::ptr::from_ref(p) as usize,
        )
    }
    /// Whether the placement of a value of schema `s` places `role`, without
    /// allocating its role set. The schema category, not the argument count,
    /// selects the membership test. Data roles, oracle receivers and the
    /// arguments of a structural product or an untelescoped logical record are
    /// strictly increasing sets. A nominal record's arguments are its
    /// telescope substitution in declaration order, any injective order; each
    /// such placement gets one sorted membership index and keeps its ordered
    /// arguments.
    fn places(&mut self, s: &Schema, p: &Placement, role: u32, work: &mut Work) -> Result<bool> {
        Ok(match p {
            Placement::Data { roles } => {
                work.lookup(roles.len())?;
                roles.binary_search(&role).is_ok()
            }
            Placement::Oracle { holder, receivers } => {
                work.lookup(receivers.len())?;
                *holder == role || receivers.binary_search(&role).is_ok()
            }
            Placement::Product { arguments, .. }
                if s.kind == Kind::LogicalRecord && !s.roles.is_empty() =>
            {
                work.lookup(self.telescopes.len())?;
                let members = match self.telescopes.entry(std::ptr::from_ref(p) as usize) {
                    std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                    std::collections::btree_map::Entry::Vacant(entry) => {
                        let sort = 1 + arguments.len().checked_ilog2().unwrap_or(0) as usize;
                        work.charge(arguments.len().saturating_mul(sort))?;
                        let mut members = arguments.clone();
                        members.sort_unstable();
                        entry.insert(members)
                    }
                };
                work.lookup(members.len())?;
                members.binary_search(&role).is_ok()
            }
            Placement::Product { arguments, .. } => {
                work.lookup(arguments.len())?;
                arguments.binary_search(&role).is_ok()
            }
        })
    }
    /// Whether `role` can supply every component of this ordinary subtree.
    fn ordinary(&mut self, s: &Schema, p: &Placement, role: u32, work: &mut Work) -> Result<bool> {
        self.ordinary_roles(s, p, work)?;
        let roles = &self.ordinary[&Self::key(s, p)];
        Ok(match roles {
            Some(roles) => {
                work.lookup(roles.len())?;
                roles.binary_search(&role).is_ok()
            }
            None => false,
        })
    }
    /// The memoized, charged form of `placement::ordinary_roles`. Every
    /// result is strictly increasing, so intersections use binary search.
    fn ordinary_roles(&mut self, s: &Schema, p: &Placement, work: &mut Work) -> Result<()> {
        let key = Self::key(s, p);
        work.lookup(self.ordinary.len())?;
        if self.ordinary.contains_key(&key) {
            return Ok(());
        }
        let roles = if s.is_logical() {
            None
        } else {
            match p {
                Placement::Data { roles } => {
                    work.charge(roles.len())?;
                    Some(roles.clone())
                }
                Placement::Product { fields, .. } => {
                    let mut roles: Option<Vec<u32>> = None;
                    let mut complete = true;
                    for (i, field) in fields.iter().enumerate() {
                        let child = if s.kind == Kind::Array {
                            s.element.as_deref()
                        } else {
                            s.fields.get(i).map(|f| &f.schema)
                        };
                        let Some(child) = child else {
                            complete = false;
                            break;
                        };
                        self.ordinary_roles(child, field, work)?;
                        let Some(next) = &self.ordinary[&Self::key(child, field)] else {
                            complete = false;
                            break;
                        };
                        roles = Some(match roles {
                            Some(previous) => {
                                work.charge(
                                    previous.len()
                                        * (1 + next.len().checked_ilog2().unwrap_or(0) as usize),
                                )?;
                                previous
                                    .into_iter()
                                    .filter(|r| next.binary_search(r).is_ok())
                                    .collect()
                            }
                            None => {
                                work.charge(next.len())?;
                                next.clone()
                            }
                        });
                    }
                    roles.filter(|_| complete)
                }
                Placement::Oracle { .. } => None,
            }
        };
        self.ordinary.insert(key, roles);
        Ok(())
    }
    fn cost(&mut self, s: &Schema, work: &mut Work) -> Result<usize> {
        let key = std::ptr::from_ref(s) as usize;
        work.lookup(self.costs.len())?;
        if let Some(cost) = self.costs.get(&key) {
            return Ok(*cost);
        }
        let cost = schema_cost(s, work)?;
        self.costs.insert(key, cost);
        Ok(cost)
    }
}
#[derive(Default)]
struct PublicNode {
    selected: bool,
    children: BTreeMap<u32, PublicNode>,
}
impl PublicNode {
    fn child(&self, index: u32, work: &mut Work) -> Result<Option<&Self>> {
        work.lookup(self.children.len())?;
        Ok(self.children.get(&index))
    }
}
fn public_index(public: &[PublicSelection], work: &mut Work) -> Result<PublicNode> {
    let mut root = PublicNode::default();
    for selected in public {
        let mut node = &mut root;
        for step in std::iter::once(&selected.port).chain(&selected.path) {
            work.lookup(node.children.len())?;
            node = node.children.entry(*step).or_default();
        }
        node.selected = true;
    }
    Ok(root)
}

pub(super) fn views(
    protocol: &Protocol,
    outputs: bool,
    public: &[PublicSelection],
    setups: &[super::Setup],
    work: &mut Work,
) -> Result<(Vec<View>, Vec<BoundaryRequirement>)> {
    let ports = if outputs {
        &protocol.outputs
    } else {
        &protocol.inputs
    };
    let setup: BTreeSet<_> = setups
        .iter()
        .flat_map(|s| s.inputs.iter().copied())
        .collect();
    work.charge(setup.len())?;
    let public = public_index(public, work)?;
    let mut remaining = work.descriptor_bytes;
    let mut result = Vec::new();
    let mut residual = Vec::new();
    // The same path has the same alias at each participant.
    let mut used = ports.iter().map(|p| p.name.clone()).collect();
    let mut aliases = BTreeMap::new();
    let mut memo = Memo::default();
    for port in ports {
        // Views exist only at a port's placed roles: compute them once and
        // walk only those, so the work grows with placed roles, not the roster.
        let placed = port.placement.roles();
        work.charge(1 + placed.len())?;
        let node = public.child(port.index, work)?;
        for role in placed {
            walk(
                protocol,
                port,
                &port.schema,
                &port.placement,
                &mut Vec::new(),
                0,
                role,
                outputs,
                node,
                false,
                &setup,
                &mut used,
                &mut aliases,
                &mut result,
                &mut residual,
                &mut remaining,
                &mut memo,
                work,
            )?;
        }
    }
    if outputs {
        // Output families have no context fields. Their direct aliases use the
        // same per-participant roster as generated Host result records.
        work.charge(protocol.roles.len() + result.len())?;
        let mut by_role = vec![Vec::new(); protocol.roles.len()];
        for (i, view) in result.iter().enumerate() {
            by_role[view.role as usize].push(i);
        }
        for indices in by_role {
            let coordinates: Vec<_> = indices
                .iter()
                .map(|&i| {
                    (
                        &ports[result[i].definition.index as usize],
                        result[i].path.as_slice(),
                    )
                })
                .collect();
            let names = family_aliases_metered(&coordinates, Some(work))?;
            for (i, name) in indices.into_iter().zip(names) {
                result[i].definition.name = name;
            }
        }
    }
    Ok((result, residual))
}
#[allow(clippy::too_many_arguments)]
fn walk(
    protocol: &Protocol,
    port: &Port,
    s: &Schema,
    p: &Placement,
    path: &mut Vec<u32>,
    offset: usize,
    role: u32,
    outputs: bool,
    public: Option<&PublicNode>,
    inherited_public: bool,
    setups: &BTreeSet<usize>,
    used: &mut BTreeSet<String>,
    aliases: &mut BTreeMap<(u32, Vec<u32>), String>,
    result: &mut Vec<View>,
    residual: &mut Vec<BoundaryRequirement>,
    remaining: &mut usize,
    memo: &mut Memo,
    work: &mut Work,
) -> Result<()> {
    work.charge(1 + path.len())?;
    if !memo.places(s, p, role, work)? {
        return Ok(());
    }
    let cost = memo.cost(s, work)?;
    let mut refuse = |reason| -> Result<()> {
        *remaining = remaining
            .checked_sub(128 + path.len() * 4 + protocol.roles[role as usize].len())
            .ok_or(E::DescriptorLimit)?;
        residual.push(BoundaryRequirement {
            port: port.index,
            path: path.clone(),
            role: protocol.roles[role as usize].clone(),
            output: outputs,
            facet: match reason {
                "custody" => Some(Facet::Custody),
                "handle-origin" => Some(match p {
                    Placement::Oracle { holder, .. } if *holder == role => Facet::OracleData,
                    _ => Facet::OracleAnchor,
                }),
                _ => None,
            },
            reason,
        });
        Ok(())
    };
    if s.custody != 0 {
        refuse("custody")?;
        return Ok(());
    }
    if s.kind.is_handle() {
        refuse("handle-origin")?;
        return Ok(());
    }
    let native = &port.native[offset..offset + schemas::native_width(s)];
    let is_public = inherited_public || public.is_some_and(|node| node.selected);
    let splits_public = public.is_some_and(|node| !node.children.is_empty());
    work.charge(native.len())?;
    let setup_count = native
        .iter()
        .filter(|n| setups.contains(&(**n as usize)))
        .count();
    let selectable_product = matches!(
        s.kind,
        Kind::Record | Kind::Tuple | Kind::Array | Kind::LogicalRecord
    ) && !s.fields.is_empty();
    let split_setup = setup_count != 0 && selectable_product;
    let ordinary = memo.ordinary(s, p, role, work)?;
    if ordinary && !splits_public && !split_setup {
        // Views describe typed transport. Public external ingress independently
        // checks recursive constructor authority; retained values keep their origin.
        if outputs && schemas::check_export(s).is_err() {
            refuse("output-custody")?;
            return Ok(());
        }
        work.lookup(aliases.len())?;
        work.charge(1 + path.len())?;
        let coordinate = (port.index, path.clone());
        let name = if let Some(name) = aliases.get(&coordinate) {
            work.charge(name.len())?;
            name.clone()
        } else {
            work.charge(alias_bytes(port, path))?;
            let name = if path.is_empty() {
                port.name.clone()
            } else {
                allocate_alias_metered(alias_candidate(port, path), used, Some(work))?
            };
            aliases.insert(coordinate, name.clone());
            name
        };
        // Charge retained descriptors before cloning, including empty schemas.
        *remaining = remaining
            .checked_sub(cost + name.len() + 128 + path.len() * 4)
            .ok_or(E::DescriptorLimit)?;
        result.push(View {
            path: path.clone(),
            role,
            public: is_public,
            definition: Port {
                name,
                display_type: s.display_type.clone(),
                placement: Placement::Data { roles: vec![role] },
                components: Vec::new(),
                index: port.index,
                native: native.to_vec(),
                schema: s.clone(),
                maximum_rows: Default::default(),
            },
        });
        return Ok(());
    }
    if s.sealed {
        refuse("sealed")?;
        return Ok(());
    }
    // Logical constructible is deliberately false; sealing/custody/privacy are
    // checked separately at every ancestor. Ordinary ancestors retain constructor authority.
    if !s.is_logical() && !s.constructible {
        refuse("constructor")?;
        return Ok(());
    }
    if s.kind == Kind::Array && s.fields.is_empty() {
        // Validate policy of the retained template without inventing element 0.
        if s.element.as_deref().is_some_and(|e| !template_authority(e)) {
            refuse("element-constructor")?;
        }
        return Ok(());
    }
    let mut next = offset;
    for (i, f) in s.fields.iter().enumerate() {
        let cp = child_placement(s, p, i);
        path.push(i as u32);
        if !f.public && memo.places(&f.schema, cp, role, work)? {
            *remaining = remaining
                .checked_sub(128 + path.len() * 4 + protocol.roles[role as usize].len())
                .ok_or(E::DescriptorLimit)?;
            residual.push(BoundaryRequirement {
                port: port.index,
                path: path.clone(),
                role: protocol.roles[role as usize].clone(),
                output: outputs,
                facet: None,
                reason: "hidden",
            });
        } else {
            walk(
                protocol,
                port,
                &f.schema,
                cp,
                path,
                next,
                role,
                outputs,
                public
                    .map(|node| node.child(i as u32, work))
                    .transpose()?
                    .flatten(),
                is_public,
                setups,
                used,
                aliases,
                result,
                residual,
                remaining,
                memo,
                work,
            )?;
        }
        path.pop();
        next += schemas::native_width(&f.schema);
    }
    Ok(())
}

fn template_authority(s: &Schema) -> bool {
    !s.sealed
        && s.custody == 0
        && (s.is_logical() || schemas::check_import(s).is_ok())
        && s.element.as_deref().is_none_or(template_authority)
        && s.fields
            .iter()
            .all(|f| f.public && template_authority(&f.schema))
}

fn schema_cost(s: &Schema, work: &mut Work) -> Result<usize> {
    work.charge(
        32 + s.identity.len() + s.display_type.len() + s.roles.len() * 16 + s.leaves.len() * 16,
    )?;
    let mut cost =
        256 + s.identity.len() + s.display_type.len() + s.generated.as_ref().map_or(0, String::len);
    for text in s.roles.iter().chain(&s.leaves) {
        work.charge(1 + text.len())?;
        cost += 24 + text.len();
    }
    for child in s
        .element
        .as_deref()
        .into_iter()
        .chain(s.data_schema.get().map(Box::as_ref))
    {
        cost += schema_cost(child, work)?;
    }
    for f in s
        .fields
        .iter()
        .chain(s.alternatives.iter().flat_map(|a| &a.fields))
    {
        work.charge(1 + f.name.len())?;
        cost += 128 + f.name.len() + schema_cost(&f.schema, work)?;
    }
    for a in &s.alternatives {
        work.charge(1 + a.name.len())?;
        cost += 48 + a.name.len();
    }
    Ok(cost)
}
