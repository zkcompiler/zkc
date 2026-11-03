//! Installed-instance tables: nominal domains, logical type instances, frame
//! tags, codecs, aggregate frames, random services, limits and the source
//! vocabulary. Every row is checked against the declarations it references;
//! none is projected into `CATALOG`.
use super::super::{Result, boolean, choice, list, number, object, string};
use super::{Catalog, kinds, require};
use serde_json::Value;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

/// A logical type instance: constructor and domain identity, empty when nullary.
pub(super) type Instance<'a> = (&'a str, &'a str);

const SCHEMES: &[&str] = &["keccak256Rows", "poseidon2Rows", "multilinearKzg"];
const LAYOUTS: &[&str] = &[
    "Scalar",
    "Vector",
    "SparseMatrix",
    "MerkleRoot",
    "MerklePath",
    "DigestRoot",
    "DigestProof",
    "PcsCommitment",
    "PcsProof",
    "Table",
    "Sequence",
    "Variant",
    "FieldArray",
];
/// Each Poseidon2 instance and the field of its pinned parameter set.
const PERMUTATIONS: &[(&str, &str)] = &[
    ("koala-bear.poseidon2-16", "koala-bear"),
    ("baby-bear.poseidon2-16", "baby-bear"),
    ("goldilocks.poseidon2-8", "goldilocks"),
];

/// The frame layout carrying each framed constructor, as the canonical value
/// frames specify it; commitments and proofs follow their scheme.
fn layout(kind: &str, scheme: Option<&str>) -> Option<&'static str> {
    Some(match (kind, scheme) {
        ("bool" | "index" | "field" | "group", _) => "Scalar",
        ("indices" | "bytes" | "vector" | "groups", _) => "Vector",
        ("matrix", _) => "SparseMatrix",
        ("table", _) => "Table",
        ("commitment", Some("keccak256Rows")) => "MerkleRoot",
        ("proof", Some("keccak256Rows")) => "MerklePath",
        ("commitment", Some("poseidon2Rows")) => "DigestRoot",
        ("proof", Some("poseidon2Rows")) => "DigestProof",
        ("commitment", Some("multilinearKzg")) => "PcsCommitment",
        ("proof", Some("multilinearKzg")) => "PcsProof",
        ("sequence", None) => "Sequence",
        ("variant", None) => "Variant",
        ("field_array", None) => "FieldArray",
        _ => return None,
    })
}

/// The catalog name rule: 1 to 256 characters, a letter or `_` first, then
/// letters, digits, `_`, `.`, `-` or `/`.
pub(super) fn identity(v: &Value) -> Result<&str> {
    let name = string(v)?;
    require(
        name.len() <= 256
            && name
                .bytes()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
            && name
                .bytes()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, b'_' | b'.' | b'-' | b'/')),
        &format!("invalid identity {name:?}"),
    )?;
    Ok(name)
}

/// `0|[1-9][0-9]*`.
pub(super) fn canonical(text: &str) -> bool {
    !text.is_empty()
        && text.bytes().all(|c| c.is_ascii_digit())
        && (text == "0" || !text.starts_with('0'))
}

/// A canonical decimal natural, as little-endian 32-bit limbs without
/// leading zero limbs, so equal values have equal limbs.
#[derive(PartialEq, Eq)]
pub(super) struct Natural(Vec<u32>);
impl Natural {
    fn decimal(v: &Value, digits: usize) -> Result<Self> {
        let text = string(v)?;
        require(
            canonical(text) && text.len() <= digits,
            &format!("noncanonical decimal {text:?}"),
        )?;
        let mut limbs: Vec<u32> = Vec::new();
        for digit in text.bytes() {
            let mut carry = u64::from(digit - b'0');
            for limb in &mut limbs {
                let value = u64::from(*limb) * 10 + carry;
                *limb = value as u32;
                carry = value >> 32;
            }
            if carry != 0 {
                limbs.push(carry as u32);
            }
        }
        Ok(Self(limbs))
    }
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    fn is_two(&self) -> bool {
        self.0 == [2]
    }
    /// The number of significant bits: `n < 2^k` exactly when `bits() <= k`.
    pub(super) fn bits(&self) -> usize {
        self.0
            .last()
            .map_or(0, |top| 32 * self.0.len() - top.leading_zeros() as usize)
    }
    /// The least number of bytes holding `self - 1`, for `self >= 2`.
    fn bytes_below(&self) -> usize {
        let power = self
            .0
            .split_last()
            .is_some_and(|(top, rest)| top.is_power_of_two() && rest.iter().all(|&l| l == 0));
        (self.bits() - usize::from(power)).div_ceil(8)
    }
}
impl Ord for Natural {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.iter().rev().cmp(other.0.iter().rev()))
    }
}
impl PartialOrd for Natural {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Copy)]
enum Structure {
    Prime,
    OverBase(usize),
    OverPrimeSubfield(usize),
}
struct Field<'a> {
    characteristic: Natural,
    structure: Structure,
    /// The reduction is the single term `X^degree - c`.
    binomial: bool,
    /// The row's own coset convention; only prime rows have one.
    convention: Option<&'a str>,
}
struct Commitment<'a> {
    scheme: &'a str,
    /// The Poseidon2 permutation's field and the digest word width.
    words: Option<(&'a str, usize)>,
}
enum Facts<'a> {
    Plain,
    Field(Field<'a>),
    /// The challenge decoder.
    Transcript(&'a str),
    Commitment(Commitment<'a>),
}
pub(super) struct Domain<'a> {
    pub(super) sort: &'a str,
    /// Member name to the named domain and the member's result sort.
    members: BTreeMap<&'a str, (&'a str, &'a str)>,
    capabilities: BTreeSet<&'a str>,
    facts: Facts<'a>,
}

struct Tag<'a> {
    layout: &'a str,
    shared: Option<(&'a str, &'a str)>,
}
/// Frame users by tag: a codec's instance, or `None` for an aggregate frame.
type Users<'a> = BTreeMap<usize, Vec<Option<Instance<'a>>>>;

/// The checked installed-instance facts that the native installation
/// document references.
pub(super) struct Instances<'a> {
    pub(super) domains: BTreeMap<&'a str, Domain<'a>>,
    pub(super) instances: BTreeSet<Instance<'a>>,
    /// The codec identity of each encoded instance.
    pub(super) codecs: BTreeMap<Instance<'a>, &'a str>,
    /// The frame layout of each instance whose codec has a frame.
    pub(super) framed: BTreeMap<Instance<'a>, &'a str>,
    /// The `(constructor, domain)` of each aggregate frame.
    pub(super) aggregates: BTreeSet<Instance<'a>>,
}

impl<'a> Instances<'a> {
    pub(super) fn new(v: &'a Value, catalog: &Catalog<'a>) -> Result<Self> {
        let mut this = Self {
            domains: BTreeMap::new(),
            instances: BTreeSet::new(),
            codecs: BTreeMap::new(),
            framed: BTreeMap::new(),
            aggregates: BTreeSet::new(),
        };
        this.read_domains(v, catalog)
            .map_err(|error| format!("domains: {error}"))?;
        this.check_domains()
            .map_err(|error| format!("domains: {error}"))?;
        this.logical_types(v, catalog)
            .map_err(|error| format!("logicalTypes: {error}"))?;
        let tags = frame_tags(v, catalog).map_err(|error| format!("frameTags: {error}"))?;
        let mut users = Users::new();
        let widths = this
            .read_codecs(v, catalog, &tags, &mut users)
            .map_err(|error| format!("codecs: {error}"))?;
        this.aggregate_frames(v, &tags, &mut users)
            .map_err(|error| format!("aggregateFrames: {error}"))?;
        this.tag_ownership(&tags, &users)
            .map_err(|error| format!("frameTags: {error}"))?;
        this.digest_words(&widths)
            .map_err(|error| format!("domains: {error}"))?;
        this.random_services(v)
            .map_err(|error| format!("randomServices: {error}"))?;
        limits(v).map_err(|error| format!("limits: {error}"))?;
        finite_definitions(v).map_err(|error| format!("finiteDefinitions: {error}"))?;
        domain_constructors(v).map_err(|error| format!("domainConstructors: {error}"))?;
        Ok(this)
    }

    /// The characteristic of a declared Field domain.
    pub(super) fn characteristic(&self, name: &str) -> Option<&Natural> {
        self.field(name).map(|field| &field.characteristic)
    }
    fn field(&self, name: &str) -> Option<&Field<'a>> {
        match &self.domains.get(name)?.facts {
            Facts::Field(field) => Some(field),
            _ => None,
        }
    }
    fn scheme(&self, name: &str) -> Option<&'a str> {
        match &self.domains.get(name)?.facts {
            Facts::Commitment(commitment) => Some(commitment.scheme),
            _ => None,
        }
    }
    fn member(&self, owner: &str, member: &str) -> Result<&'a str> {
        self.domains
            .get(owner)
            .and_then(|domain| domain.members.get(member))
            .map(|(target, _)| *target)
            .ok_or_else(|| format!("{owner} has no {member} member"))
    }
    fn field_or_refuse(&self, name: &str) -> Result<&Field<'a>> {
        self.field(name)
            .ok_or_else(|| format!("{name} is not a Field domain"))
    }

    /// The prime base that residue arithmetic on `name` computes over: the
    /// field itself when it is prime, or the prime `BaseField` of a binomial
    /// extension `B[X]/(X^degree - c)`.
    pub(super) fn residue_base(&self, name: &'a str) -> Option<&'a str> {
        let field = self.field(name)?;
        match field.structure {
            Structure::Prime => Some(name),
            Structure::OverBase(_) if field.binomial => {
                let base = self.member(name, "BaseField").ok()?;
                matches!(self.field(base)?.structure, Structure::Prime).then_some(base)
            }
            _ => None,
        }
    }

    /// Follow `BaseField` members to the prime row, if the tower has one.
    fn prime_base(&self, name: &'a str) -> Result<Option<&'a str>> {
        let mut current = name;
        for _ in 0..=self.domains.len() {
            match self.field_or_refuse(current)?.structure {
                Structure::Prime => return Ok(Some(current)),
                Structure::OverPrimeSubfield(_) => return Ok(None),
                Structure::OverBase(_) => current = self.member(current, "BaseField")?,
            }
        }
        Err(format!("{name} has a cyclic BaseField chain"))
    }

    /// The element width that the field structure fixes.
    fn element_width(&self, name: &'a str) -> Result<usize> {
        let mut factor = 1usize;
        let mut current = name;
        for _ in 0..=self.domains.len() {
            let field = self.field_or_refuse(current)?;
            let width = match field.structure {
                Structure::Prime => field.characteristic.bytes_below(),
                Structure::OverPrimeSubfield(degree) => {
                    require(
                        field.characteristic.is_two() && degree % 8 == 0,
                        &format!("{current} has no element width rule"),
                    )?;
                    degree / 8
                }
                Structure::OverBase(degree) => {
                    factor = factor.checked_mul(degree).ok_or("element width overflow")?;
                    current = self.member(current, "BaseField")?;
                    continue;
                }
            };
            return factor
                .checked_mul(width)
                .ok_or_else(|| "element width overflow".into());
        }
        Err(format!("{name} has a cyclic BaseField chain"))
    }

    fn read_domains(&mut self, v: &'a Value, catalog: &Catalog<'a>) -> Result<()> {
        let rules = list(&v["rules"])?
            .iter()
            .map(|rule| Ok((string(&rule[0])?, string(&rule[1])?)))
            .collect::<Result<Vec<_>>>()?;
        for row in list(&v["domains"])? {
            let sort = string(&row["sort"])?;
            let facts = match sort {
                "Field" => Some("field"),
                "Transcript" => Some("transcript"),
                "Commitment" => Some("commitment"),
                _ => None,
            };
            let mut keys = vec!["identity", "sort", "members", "capabilities"];
            keys.extend(facts);
            object(row, &keys, &[])?;
            let name = identity(&row["identity"])?;
            let domain = read_domain(row, sort, facts, catalog, &rules)
                .map_err(|error| format!("{name}: {error}"))?;
            require(
                self.domains.insert(name, domain).is_none(),
                &format!("{name}: identity is not unique across domains and codecs"),
            )?;
        }
        Ok(())
    }

    fn check_domains(&self) -> Result<()> {
        // Member typing precedes every rule that follows a member.
        for (name, domain) in &self.domains {
            for (member, (target, sort)) in &domain.members {
                require(
                    self.domains.get(target).is_some_and(|d| d.sort == *sort),
                    &format!("{name}: member {member} must name a domain of sort {sort}"),
                )?;
            }
        }
        let mut conventions = BTreeSet::new();
        for (&name, domain) in &self.domains {
            self.check_domain(name, domain, &mut conventions)
                .map_err(|error| format!("{name}: {error}"))?;
        }
        Ok(())
    }

    fn check_domain(
        &self,
        name: &'a str,
        domain: &Domain<'a>,
        conventions: &mut BTreeSet<&'a str>,
    ) -> Result<()> {
        match &domain.facts {
            Facts::Field(field) => {
                if let Some(convention) = field.convention {
                    require(
                        conventions.insert(convention),
                        &format!("duplicate two-adic convention {convention}"),
                    )?;
                }
                if let Structure::OverBase(_) = field.structure {
                    let base = self.member(name, "BaseField")?;
                    require(
                        self.field_or_refuse(base)?.characteristic == field.characteristic,
                        "BaseField must have the same characteristic",
                    )?;
                }
                let convention = match self.prime_base(name)? {
                    Some(prime) => self.field_or_refuse(prime)?.convention,
                    None => None,
                };
                require(
                    domain.capabilities.contains("TwoAdicField") == convention.is_some(),
                    "TwoAdicField must hold exactly when the row or its prime base has a convention",
                )?;
                if domain.capabilities.contains("PairingField") {
                    self.pairing(name, domain)?;
                }
            }
            Facts::Transcript(decoder) => {
                let challenge = self.field_or_refuse(self.member(name, "ChallengeField")?)?;
                match *decoder {
                    "fr64be" | "scalar64le" => require(
                        matches!(challenge.structure, Structure::Prime),
                        &format!("{decoder} requires a prime challenge field"),
                    )?,
                    "rejection31le" => require(
                        challenge.characteristic.bits() <= 31,
                        "rejection31le requires a challenge characteristic below 2^31",
                    )?,
                    _ => require(
                        challenge.characteristic.bits() <= 64,
                        "rejection64le requires a challenge characteristic below 2^64",
                    )?,
                }
            }
            Facts::Commitment(commitment) => {
                if let Some((field, _)) = commitment.words {
                    let value = self.member(name, "ValueField")?;
                    require(
                        field == value || self.prime_base(value)? == Some(field),
                        "the permutation field must be the ValueField member or its prime base",
                    )?;
                }
            }
            Facts::Plain => {}
        }
        Ok(())
    }

    fn pairing(&self, name: &str, domain: &Domain<'a>) -> Result<()> {
        let mut groups = BTreeSet::new();
        for member in ["PairingG1", "PairingG2", "PairingGT"] {
            let Some(&(group, _)) = domain.members.get(member) else {
                continue;
            };
            require(groups.insert(group), "pairing groups must be distinct")?;
            let row = &self.domains[group];
            require(
                row.capabilities.contains("ScalarAction")
                    && row
                        .members
                        .get("Scalar")
                        .is_some_and(|(scalar, _)| *scalar == name),
                &format!("{group} must hold ScalarAction with {name} as Scalar"),
            )?;
        }
        Ok(())
    }

    fn logical_types(&mut self, v: &'a Value, catalog: &Catalog<'a>) -> Result<()> {
        for row in list(&v["logicalTypes"])? {
            object(row, &["kind", "domain"], &[])?;
            let instance = (string(&row["kind"])?, string(&row["domain"])?);
            self.logical_type(instance, catalog)
                .map_err(|error| format!("{instance:?}: {error}"))?;
        }
        Ok(())
    }

    fn logical_type(&mut self, (kind, domain): Instance<'a>, catalog: &Catalog<'a>) -> Result<()> {
        let ty = catalog
            .types
            .get(kind)
            .ok_or_else(|| format!("undeclared constructor {kind}"))?;
        require(
            !matches!(kind, "variant" | "resource_unit"),
            "variant and resource_unit have their own formation",
        )?;
        match kinds(&ty["parameters"])?.as_slice() {
            [] => require(domain.is_empty(), "a nullary instance has the empty domain")?,
            [("Domain", sort)] => require(
                self.domains.get(domain).is_some_and(|d| d.sort == *sort),
                &format!("a unary instance names a domain of sort {sort}"),
            )?,
            _ => {
                return Err(
                    "only nullary and unary domain constructors have logical type instances".into(),
                );
            }
        }
        // `setup` marks the setup-key constructors.
        if !ty["setup"].is_null() {
            require(
                self.scheme(domain) == Some("multilinearKzg"),
                "setup keys are admitted only over multilinearKzg commitments",
            )?;
        }
        require(
            self.instances.insert((kind, domain)),
            "duplicate logical type instance",
        )
    }

    fn read_codecs(
        &mut self,
        v: &'a Value,
        catalog: &Catalog<'a>,
        tags: &BTreeMap<usize, Tag<'a>>,
        users: &mut Users<'a>,
    ) -> Result<BTreeMap<Instance<'a>, usize>> {
        let mut identities = BTreeSet::new();
        let mut widths = BTreeMap::new();
        for row in list(&v["codecs"])? {
            object(row, &["identity", "kind", "domain", "frame"], &[])?;
            let name = identity(&row["identity"])?;
            require(
                !self.domains.contains_key(name) && identities.insert(name),
                &format!("{name}: identity is not unique across domains and codecs"),
            )?;
            let instance = (string(&row["kind"])?, string(&row["domain"])?);
            let width = self
                .codec(name, instance, &row["frame"], catalog, tags, users)
                .map_err(|error| format!("{name}: {error}"))?;
            if let Some(width) = width {
                widths.insert(instance, width);
            }
        }
        for (&(kind, domain), width) in &widths {
            if kind == "group" {
                require(
                    widths
                        .get(&("groups", domain))
                        .is_none_or(|other| other == width),
                    &format!("group and groups codecs of {domain} must have equal elementBytes"),
                )?;
            }
        }
        Ok(widths)
    }

    /// Check one codec and return its element width, when its frame has one.
    fn codec(
        &mut self,
        name: &'a str,
        (kind, domain): Instance<'a>,
        frame: &'a Value,
        catalog: &Catalog<'a>,
        tags: &BTreeMap<usize, Tag<'a>>,
        users: &mut Users<'a>,
    ) -> Result<Option<usize>> {
        require(
            self.instances.contains(&(kind, domain)),
            &format!("({kind}, {domain}) is not a logical type instance"),
        )?;
        let predicate = format!("Encodes.{kind}");
        let declared = catalog
            .capabilities
            .get(predicate.as_str())
            .ok_or_else(|| format!("{predicate} is not declared"))?;
        let mut expected = vec![("Domain", "Codec")];
        expected.extend(self.domains.get(domain).map(|d| ("Domain", d.sort)));
        require(
            kinds(&declared["parameters"])? == expected,
            &format!("{predicate} must be declared over Codec and the payload sort"),
        )?;
        require(
            self.codecs.insert((kind, domain), name).is_none(),
            "at most one codec per logical type instance",
        )?;
        let message = boolean(&catalog.types[kind]["message"])?;
        if frame.is_null() {
            require(!message, "a message type's codec has a frame")?;
            return Ok(None);
        }
        let number_of_tag = number(&frame["tag"])?;
        let tag = tags
            .get(&number_of_tag)
            .ok_or_else(|| format!("unknown frame tag {number_of_tag}"))?;
        let fields: &[&str] = match tag.layout {
            "Scalar" | "Vector" | "SparseMatrix" => &["tag", "elementBytes"],
            "PcsCommitment" => &["tag", "bytes"],
            "PcsProof" => &["tag", "bytes", "bytesPerArity"],
            "MerkleRoot" | "MerklePath" | "DigestRoot" | "DigestProof" | "Table" => &["tag"],
            other => return Err(format!("{other} is not a codec frame layout")),
        };
        object(frame, fields, &[])?;
        for key in &fields[1..] {
            number(&frame[*key])?;
        }
        // The standalone public table input frame is input-only.
        require(
            message || tag.layout == "Table",
            "only message types and the input-only table frame have frames",
        )?;
        require(
            layout(kind, self.scheme(domain)) == Some(tag.layout),
            &format!("{kind} codecs do not use the {} layout", tag.layout),
        )?;
        users
            .entry(number_of_tag)
            .or_default()
            .push(Some((kind, domain)));
        self.framed.insert((kind, domain), tag.layout);
        let Some(width) = frame.get("elementBytes") else {
            return Ok(None);
        };
        let width = number(width)?;
        if matches!(kind, "field" | "vector" | "matrix") {
            require(
                width == self.element_width(domain)?,
                "elementBytes must follow the field structure",
            )?;
        }
        Ok(Some(width))
    }

    fn aggregate_frames(
        &mut self,
        v: &'a Value,
        tags: &BTreeMap<usize, Tag<'a>>,
        users: &mut Users<'a>,
    ) -> Result<()> {
        for row in list(&v["aggregateFrames"])? {
            object(row, &["constructor", "domain", "tag"], &[])?;
            let constructor = choice(&row["constructor"], &["sequence", "variant", "field_array"])?;
            let domain = string(&row["domain"])?;
            require(
                if constructor == "field_array" {
                    self.field(domain).is_some()
                } else {
                    domain.is_empty()
                },
                "sequence and variant frames have the empty domain and field_array frames a Field domain",
            )?;
            if constructor == "field_array" {
                // The field's own scalar frame encodes the array's elements.
                require(
                    self.framed.get(&("field", domain)) == Some(&"Scalar"),
                    &format!(
                        "field_array frames need a field codec of {domain} with a Scalar frame"
                    ),
                )?;
            }
            let number_of_tag = number(&row["tag"])?;
            let tag = tags
                .get(&number_of_tag)
                .ok_or_else(|| format!("unknown frame tag {number_of_tag}"))?;
            require(
                layout(constructor, None) == Some(tag.layout),
                &format!("{constructor} frames do not use the {} layout", tag.layout),
            )?;
            require(
                self.aggregates.insert((constructor, domain)),
                &format!("duplicate aggregate frame ({constructor}, {domain})"),
            )?;
            users.entry(number_of_tag).or_default().push(None);
        }
        Ok(())
    }

    fn tag_ownership(&self, tags: &BTreeMap<usize, Tag<'a>>, users: &Users<'a>) -> Result<()> {
        for (number_of_tag, tag) in tags {
            let used = users.get(number_of_tag).map_or(&[][..], Vec::as_slice);
            let Some((kind, scheme)) = tag.shared else {
                require(
                    used.len() == 1,
                    &format!("unshared frame tag {number_of_tag} needs exactly one user"),
                )?;
                continue;
            };
            let mut actual = used.iter().copied().collect::<Option<Vec<_>>>();
            if let Some(actual) = &mut actual {
                actual.sort();
            }
            let expected = self
                .codecs
                .keys()
                .filter(|(k, d)| *k == kind && self.scheme(d) == Some(scheme))
                .copied()
                .collect::<Vec<_>>();
            require(
                actual.as_ref() == Some(&expected) && expected.len() >= 2,
                &format!(
                    "frame tag {number_of_tag} must be shared by exactly the {kind} codecs over {scheme} commitments, at least two"
                ),
            )?;
        }
        Ok(())
    }

    fn digest_words(&self, widths: &BTreeMap<Instance<'a>, usize>) -> Result<()> {
        for (name, domain) in &self.domains {
            if let Facts::Commitment(Commitment {
                words: Some((field, bytes)),
                ..
            }) = &domain.facts
            {
                require(
                    widths.get(&("field", *field)) == Some(bytes),
                    &format!(
                        "{name}: digestWordBytes must equal the element width of the {field} field codec frame"
                    ),
                )?;
            }
        }
        Ok(())
    }

    fn random_services(&self, v: &'a Value) -> Result<()> {
        let mut contracts = BTreeSet::new();
        let mut fields = BTreeSet::new();
        for row in list(&v["randomServices"])? {
            object(row, &["contract", "field"], &[])?;
            let contract = identity(&row["contract"])?;
            require(
                contracts.insert(contract),
                &format!("duplicate random service {contract}"),
            )?;
            let field = string(&row["field"])?;
            require(
                self.field(field).is_some(),
                &format!("{contract}: a random service draws from a declared Field domain"),
            )?;
            require(
                fields.insert(field),
                "random services and rng types correspond one to one",
            )?;
        }
        let rng = self
            .instances
            .iter()
            .filter(|(kind, _)| *kind == "rng")
            .map(|(_, field)| *field)
            .collect::<BTreeSet<_>>();
        require(
            fields == rng,
            &format!(
                "random services and rng types correspond one to one; unmatched {:?}",
                fields.symmetric_difference(&rng).collect::<Vec<_>>()
            ),
        )
    }
}

fn read_domain<'a>(
    row: &'a Value,
    sort: &'a str,
    facts: Option<&str>,
    catalog: &Catalog<'a>,
    rules: &[(&'a str, &'a str)],
) -> Result<Domain<'a>> {
    require(
        catalog.sorts.contains(sort) && !matches!(sort, "Codec" | "Slot"),
        "domain sort must be a declared sort other than Codec and Slot",
    )?;
    let mut members = BTreeMap::new();
    for pair in list(&row["members"])? {
        let [member, target] = list(pair)? else {
            return Err("expected a [member, identity] pair".into());
        };
        let member = string(member)?;
        let result = catalog
            .members
            .get(&(("Domain", sort), member))
            .ok_or_else(|| format!("{member} is not a declared member of sort {sort}"))?;
        require(
            result.0 == "Domain",
            &format!("member {member} does not name a domain"),
        )?;
        require(
            members
                .insert(member, (string(target)?, result.1))
                .is_none(),
            &format!("duplicate member {member}"),
        )?;
    }
    let mut capabilities = BTreeSet::new();
    for capability in list(&row["capabilities"])? {
        let capability = string(capability)?;
        let declared = catalog
            .capabilities
            .get(capability)
            .ok_or_else(|| format!("unknown capability {capability}"))?;
        require(
            kinds(&declared["parameters"])? == [("Domain", sort)],
            &format!("{capability} is not a unary predicate over {sort}"),
        )?;
        require(
            capabilities.insert(capability),
            &format!("duplicate capability {capability}"),
        )?;
    }
    for (premise, conclusion) in rules {
        require(
            !capabilities.contains(premise) || capabilities.contains(conclusion),
            &format!("capabilities are not closed under {premise} => {conclusion}"),
        )?;
    }
    // A capability's required members are present, and a member that some
    // capability names occurs only beside a capability that names it.
    for capability in &capabilities {
        for required in list(&catalog.capabilities[capability]["requires"])? {
            let required = string(required)?;
            require(
                members.contains_key(required),
                &format!("{capability} requires a {required} member"),
            )?;
        }
    }
    for member in members.keys() {
        let mut governing = Vec::new();
        for (name, row) in &catalog.capabilities {
            let names = |field: &str| -> Result<bool> {
                Ok(list(&row[field])?
                    .iter()
                    .any(|named| named.as_str() == Some(*member)))
            };
            if names("requires")? || names("permits")? {
                governing.push(*name);
            }
        }
        require(
            governing.is_empty() || governing.iter().any(|name| capabilities.contains(name)),
            &format!(
                "a {member} member requires one of the capabilities {}",
                governing.join(", ")
            ),
        )?;
    }
    let holds = |name: &str| capabilities.contains(name);
    let has = |name: &str| members.contains_key(name);
    let facts = match facts {
        Some("field") => Facts::Field(field(&row["field"], holds)?),
        Some("transcript") => Facts::Transcript(transcript(&row["transcript"], holds, has)?),
        Some(_) => Facts::Commitment(commitment(&row["commitment"], has)?),
        None => Facts::Plain,
    };
    Ok(Domain {
        sort,
        members,
        capabilities,
        facts,
    })
}

fn field<'a>(v: &'a Value, holds: impl Fn(&str) -> bool) -> Result<Field<'a>> {
    object(v, &["characteristic", "structure", "twoAdic"], &[])?;
    let characteristic = Natural::decimal(&v["characteristic"], 1024)?;
    require(
        characteristic.bits() >= 2,
        "characteristic must be at least 2",
    )?;
    require(
        holds("CharacteristicNotTwo") != characteristic.is_two(),
        "CharacteristicNotTwo must hold exactly when the characteristic is not 2",
    )?;
    let shape = &v["structure"];
    let mut binomial = false;
    let structure = if choice(&shape["kind"], &["prime", "extension"])? == "prime" {
        object(shape, &["kind"], &[])?;
        Structure::Prime
    } else {
        object(shape, &["kind", "over", "degree", "reduction"], &[])?;
        let over = choice(&shape["over"], &["BaseField", "PrimeSubfield"])?;
        let degree = number(&shape["degree"])?;
        require(degree >= 2, "extension degree must be at least 2")?;
        let reduction = list(&shape["reduction"])?;
        require(!reduction.is_empty(), "reduction is a nonempty list")?;
        binomial = reduction.len() == 1 && reduction[0][0] == 0;
        let mut bound = degree;
        for term in reduction {
            let [exponent, coefficient] = list(term)? else {
                return Err("expected an [exponent, coefficient] reduction term".into());
            };
            let exponent = number(exponent)?;
            require(
                exponent < bound,
                "reduction exponents must strictly decrease below the degree",
            )?;
            bound = exponent;
            let coefficient = Natural::decimal(coefficient, 1024)?;
            require(
                !coefficient.is_zero() && coefficient < characteristic,
                "reduction coefficients must be nonzero and below the characteristic",
            )?;
        }
        if over == "BaseField" {
            Structure::OverBase(degree)
        } else {
            Structure::OverPrimeSubfield(degree)
        }
    };
    let prime = matches!(structure, Structure::Prime);
    require(
        holds("PrimeField") == prime,
        "exactly the prime rows hold PrimeField",
    )?;
    let over_base = matches!(structure, Structure::OverBase(_));
    require(
        holds("ExtensionField") == over_base,
        "exactly the rows over BaseField hold ExtensionField",
    )?;
    let two_adic = &v["twoAdic"];
    let convention = if two_adic.is_null() {
        None
    } else {
        object(
            two_adic,
            &["convention", "maximalRoot", "twoAdicity", "ordering"],
            &[],
        )?;
        require(prime, "twoAdic is only on prime rows")?;
        require(
            Natural::decimal(&two_adic["maximalRoot"], 1024)? < characteristic,
            "maximalRoot must be below the characteristic",
        )?;
        require(
            (1..=64).contains(&number(&two_adic["twoAdicity"])?),
            "twoAdicity must be between 1 and 64",
        )?;
        choice(&two_adic["ordering"], &["powers"])?;
        Some(identity(&two_adic["convention"])?)
    };
    Ok(Field {
        characteristic,
        structure,
        binomial,
        convention,
    })
}

fn transcript(v: &Value, holds: impl Fn(&str) -> bool, has: impl Fn(&str) -> bool) -> Result<&str> {
    object(v, &["family", "hash", "decoder", "bindsSuite"], &[])?;
    let chain =
        choice(&v["family"], &["merlin3", "spongefish0.8.0", "hash-chain"])? == "hash-chain";
    require(
        if chain {
            v["hash"] == "keccak256"
        } else {
            v["hash"].is_null()
        },
        "hash is keccak256 exactly for hash-chain transcripts, otherwise null",
    )?;
    let decoder = choice(
        &v["decoder"],
        &["fr64be", "rejection31le", "rejection64le", "scalar64le"],
    )?;
    boolean(&v["bindsSuite"])?;
    require(
        holds("Transcript") && holds("FieldTranscript"),
        "a transcript row holds Transcript and FieldTranscript",
    )?;
    require(
        has("ChallengeField"),
        "a transcript row has a ChallengeField member",
    )?;
    Ok(decoder)
}

fn commitment<'a>(v: &'a Value, has: impl Fn(&str) -> bool) -> Result<Commitment<'a>> {
    let scheme = choice(&v["scheme"], SCHEMES)?;
    let words = match scheme {
        "keccak256Rows" => {
            object(v, &["scheme", "digestBytes"], &[])?;
            None
        }
        "poseidon2Rows" => {
            object(
                v,
                &["scheme", "permutation", "digestBytes", "digestWordBytes"],
                &[],
            )?;
            let permutation = string(&v["permutation"])?;
            let field = PERMUTATIONS
                .iter()
                .find(|(name, _)| *name == permutation)
                .map(|(_, field)| *field)
                .ok_or_else(|| format!("unknown permutation {permutation}"))?;
            Some((field, number(&v["digestWordBytes"])?))
        }
        _ => {
            object(v, &["scheme"], &[])?;
            None
        }
    };
    if scheme != "multilinearKzg" {
        require(number(&v["digestBytes"])? == 32, "digestBytes must be 32")?;
    }
    require(
        has("ValueField"),
        "a commitment row has a ValueField member",
    )?;
    require(
        scheme == "multilinearKzg" || !(has("PointField") || has("EvaluationField")),
        "PointField and EvaluationField occur only on multilinearKzg commitments",
    )?;
    Ok(Commitment { scheme, words })
}

fn frame_tags<'a>(v: &'a Value, catalog: &Catalog<'a>) -> Result<BTreeMap<usize, Tag<'a>>> {
    let mut tags = BTreeMap::new();
    for row in list(&v["frameTags"])? {
        object(row, &["tag", "layout", "shared"], &[])?;
        let number_of_tag = number(&row["tag"])?;
        require(
            (1..=255).contains(&number_of_tag),
            "frame tags are between 1 and 255",
        )?;
        let layout = choice(&row["layout"], LAYOUTS)?;
        let shared = &row["shared"];
        let shared = if shared.is_null() {
            None
        } else {
            object(shared, &["kind", "scheme"], &[])?;
            let kind = string(&shared["kind"])?;
            require(
                catalog.types.contains_key(kind),
                "shared frame tags name a declared constructor",
            )?;
            Some((kind, choice(&shared["scheme"], SCHEMES)?))
        };
        require(
            tags.insert(number_of_tag, Tag { layout, shared }).is_none(),
            &format!("duplicate frame tag {number_of_tag}"),
        )?;
    }
    Ok(tags)
}

fn limits(v: &Value) -> Result<()> {
    let mut names = BTreeSet::new();
    for row in list(&v["limits"])? {
        object(
            row,
            &["name", "value", "unit", "owner", "scope", "phase"],
            &[],
        )?;
        let name = identity(&row["name"])?;
        require(names.insert(name), &format!("duplicate limit {name}"))?;
        require(
            row["value"].as_u64().is_some_and(|value| value < 1 << 63),
            "limit value must be a JSON integer from 0 to 2^63 - 1",
        )?;
        choice(
            &row["unit"],
            &["roles", "bytes", "elements", "entries", "steps"],
        )?;
        require(
            !string(&row["owner"])?.is_empty() && !string(&row["scope"])?.is_empty(),
            "limit owner and scope are nonempty",
        )?;
        choice(
            &row["phase"],
            &["formation", "admission", "publication", "execution"],
        )?;
    }
    Ok(())
}

fn finite_definitions(v: &Value) -> Result<()> {
    let mut identities = BTreeSet::new();
    for row in list(&v["finiteDefinitions"])? {
        object(
            row,
            &["identity", "mode", "operation", "collection", "filtered"],
            &[],
        )?;
        let name = identity(&row["identity"])?;
        require(
            identities.insert(name),
            &format!("duplicate finite definition {name}"),
        )?;
        choice(&row["mode"], &["math", "local"])?;
        let fold = choice(&row["operation"], &["fold", "collect"])? == "fold";
        let filtered = boolean(&row["filtered"])?;
        let collection = &row["collection"];
        require(
            fold == collection.is_null(),
            &format!("{name}: collection is null exactly for fold"),
        )?;
        if !fold {
            let collection = choice(
                collection,
                &["vector", "groups", "sequence", "indices", "field_array"],
            )?;
            require(
                !(filtered && collection == "field_array"),
                &format!("{name}: field_array collections are not filtered"),
            )?;
        }
    }
    Ok(())
}

fn domain_constructors(v: &Value) -> Result<()> {
    let mut identities = BTreeSet::new();
    for row in list(&v["domainConstructors"])? {
        object(row, &["identity", "kind", "axis"], &[])?;
        let name = identity(&row["identity"])?;
        require(
            identities.insert(name),
            &format!("duplicate domain constructor {name}"),
        )?;
        choice(
            &row["kind"],
            &[
                "Elements",
                "Indices",
                "Range",
                "Zip",
                "Product",
                "MatrixRow",
                "MatrixColumn",
                "MatrixCoordinates",
                "SourceArray",
            ],
        )?;
        require(number(&row["axis"])? <= 1, "axis is 0 or 1")?;
    }
    Ok(())
}
