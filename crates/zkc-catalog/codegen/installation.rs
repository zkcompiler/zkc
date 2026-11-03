//! The native installation document: physical representations, provider
//! preferences, installation units, field arithmetic forms and calling
//! conventions. It references the declaration document one way and is checked
//! together with it; nothing here is projected into `CATALOG`.
use super::super::{Result, boolean, choice, list, number, object, string};
use super::instances::{Instance, Instances, canonical, identity};
use super::{Catalog, Kind, kinds, require};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

const PROVIDERS: &[&str] = &[
    "arkworks",
    "blst",
    "dalek",
    "halo2curves-axiom",
    "plonky3",
    "spongefish",
];
const UNITS: &[&str] = &[
    "arkworks",
    "blst",
    "dalek",
    "halo2curves",
    "plonky3",
    "independent",
];
/// Units that the specification fixes for providers named unlike their unit.
const FIXED_UNITS: &[(&str, &str)] = &[
    ("spongefish", "arkworks"),
    ("halo2curves-axiom", "halo2curves"),
];
const FRAMES: &[&str] = &["canonical", "local"];
const EXTENT: u64 = 1_048_576;

struct Representations<'a> {
    rows: BTreeMap<(&'a str, &'a str, &'a str), &'a Value>,
    defaults: BTreeMap<Instance<'a>, &'a str>,
}

enum Pattern<'a> {
    Any,
    Domain(&'a str),
    /// An admitted logical type instance.
    Type(Instance<'a>),
    Naturals(u64, u64),
}

pub(super) fn validate<'a>(
    v: &'a Value,
    catalog: &Catalog<'a>,
    instances: &Instances<'a>,
) -> Result<()> {
    object(
        v,
        &[
            "format",
            "representations",
            "appliedRepresentations",
            "providers",
            "providerUnits",
            "fieldForms",
            "physicalArguments",
        ],
        &[],
    )?;
    choice(&v["format"], &["zkc.native-installation/0"])?;
    let units = provider_units(v).map_err(|error| format!("providerUnits: {error}"))?;
    let providers = providers(v, instances).map_err(|error| format!("providers: {error}"))?;
    let representations = representations(v, instances, &providers, &units)
        .map_err(|error| format!("representations: {error}"))?;
    applied(v, catalog, instances, &representations, &providers, &units)
        .map_err(|error| format!("appliedRepresentations: {error}"))?;
    field_forms(v, instances, &representations).map_err(|error| format!("fieldForms: {error}"))?;
    physical_arguments(v, catalog).map_err(|error| format!("physicalArguments: {error}"))
}

/// Exactly one unit row for each provider of the vocabulary.
fn provider_units(v: &Value) -> Result<BTreeMap<&str, &str>> {
    let mut units = BTreeMap::new();
    for row in list(&v["providerUnits"])? {
        object(row, &["provider", "unit"], &[])?;
        let provider = choice(&row["provider"], PROVIDERS)?;
        let unit = choice(&row["unit"], UNITS)?;
        require(
            unit != "independent",
            &format!("{provider}: independent is the unit of provider-free storage"),
        )?;
        if let Some((_, fixed)) = FIXED_UNITS.iter().find(|(name, _)| *name == provider) {
            require(
                unit == *fixed,
                &format!("{provider} is installed by the {fixed} unit"),
            )?;
        }
        require(
            units.insert(provider, unit).is_none(),
            &format!("{provider} has more than one unit row"),
        )?;
    }
    for provider in PROVIDERS {
        require(
            units.contains_key(provider),
            &format!("{provider} has no installation unit row"),
        )?;
    }
    Ok(units)
}

/// Each declared domain's providers: its default, then its alternatives.
fn providers<'a>(
    v: &'a Value,
    instances: &Instances<'a>,
) -> Result<BTreeMap<&'a str, Vec<&'a str>>> {
    let mut preferences = BTreeMap::new();
    for row in list(&v["providers"])? {
        object(row, &["domain", "default", "alternatives"], &[])?;
        let domain = string(&row["domain"])?;
        require(
            instances.domains.contains_key(domain),
            &format!("{domain} is not a declared domain"),
        )?;
        let default = choice(&row["default"], PROVIDERS)?;
        let mut named = vec![default];
        for alternative in list(&row["alternatives"])? {
            let alternative = choice(alternative, PROVIDERS)?;
            require(
                !named.contains(&alternative),
                &format!("{domain}: provider {alternative} appears twice"),
            )?;
            named.push(alternative);
        }
        require(
            preferences.insert(domain, named).is_none(),
            &format!("{domain} has more than one provider row"),
        )?;
    }
    for domain in instances.domains.keys() {
        require(
            preferences.contains_key(domain),
            &format!("{domain} has no provider row"),
        )?;
    }
    Ok(preferences)
}

fn representations<'a>(
    v: &'a Value,
    instances: &Instances<'a>,
    providers: &BTreeMap<&'a str, Vec<&'a str>>,
    units: &BTreeMap<&'a str, &'a str>,
) -> Result<Representations<'a>> {
    let rows = list(&v["representations"])?;
    let mut result = Representations {
        rows: BTreeMap::new(),
        defaults: BTreeMap::new(),
    };
    let mut layouts = BTreeSet::new();
    // References, uniqueness and the single default of each instance come
    // before the facts that a default row must satisfy.
    for row in rows {
        object(
            row,
            &[
                "identity", "kind", "domain", "default", "layout", "frame", "unit",
            ],
            &[],
        )?;
        let name = identity(&row["identity"])?;
        let (kind, domain) = (string(&row["kind"])?, string(&row["domain"])?);
        let at = format!("{name} for ({kind}, {domain})");
        require(
            instances.instances.contains(&(kind, domain)),
            &format!("{at}: undeclared logical type instance"),
        )?;
        require(
            result.rows.insert((kind, domain, name), row).is_none(),
            &format!("{at}: duplicate representation"),
        )?;
        let layout = string(&row["layout"])?;
        if !layout.is_empty() {
            identity(&row["layout"])?;
            require(
                layouts.insert((kind, domain, layout)),
                &format!("{at}: layout {layout} is selected twice for one instance"),
            )?;
        }
        if choice(&row["frame"], FRAMES)? == "canonical" {
            require(
                instances.framed.contains_key(&(kind, domain)),
                &format!("{at}: a canonical representation requires a framed codec"),
            )?;
        }
        choice(&row["unit"], UNITS)?;
        if boolean(&row["default"])? {
            require(
                result.defaults.insert((kind, domain), name).is_none(),
                &format!("{at}: second default representation"),
            )?;
        }
    }
    for (kind, domain) in &instances.instances {
        require(
            result.defaults.contains_key(&(*kind, *domain)),
            &format!("({kind}, {domain}) has no default representation"),
        )?;
    }
    for row in rows.iter().filter(|row| row["default"] == true) {
        let (kind, domain) = (string(&row["kind"])?, string(&row["domain"])?);
        let at = format!("{} for ({kind}, {domain})", string(&row["identity"])?);
        // The table input codec's frame counts like any other codec frame.
        if instances.framed.contains_key(&(kind, domain)) {
            require(
                row["frame"] == "canonical",
                &format!("{at}: the default of an instance with a framed codec is canonical"),
            )?;
        }
        if domain.is_empty() {
            require(
                row["unit"] == "independent",
                &format!("{at}: the default of a nullary instance has unit independent"),
            )?;
        } else {
            let unit = providers
                .get(domain)
                .and_then(|named| named.first())
                .and_then(|provider| units.get(provider));
            require(
                unit.is_some_and(|unit| row["unit"] == *unit),
                &format!(
                    "{at}: the default of a unary instance has the unit of its domain's default provider"
                ),
            )?;
        }
    }
    Ok(result)
}

fn applied<'a>(
    v: &'a Value,
    catalog: &Catalog<'a>,
    instances: &Instances<'a>,
    representations: &Representations<'a>,
    providers: &BTreeMap<&'a str, Vec<&'a str>>,
    units: &BTreeMap<&'a str, &'a str>,
) -> Result<()> {
    let mut previous: Vec<(&str, Vec<Pattern<'a>>, &str, bool)> = Vec::new();
    let mut conventions = BTreeSet::new();
    for row in list(&v["appliedRepresentations"])? {
        object(
            row,
            &[
                "constructor",
                "arguments",
                "identity",
                "default",
                "child",
                "frame",
                "provider",
                "unit",
                "vectorPort",
            ],
            &[],
        )?;
        let name = identity(&row["identity"])?;
        let constructor = string(&row["constructor"])?;
        let at = format!("{name} for {constructor}");
        let declared = catalog.types.get(constructor).copied();
        let parameters = match declared {
            Some(ty) => kinds(&ty["parameters"])?,
            None if constructor == "variant" => Vec::new(),
            None => return Err(format!("{at}: undeclared constructor")),
        };
        require(
            declared.is_none() || !parameters.is_empty(),
            &format!("{at}: applied representations need a constructor with parameters"),
        )?;
        let arguments = list(&row["arguments"])?;
        require(
            arguments.len() == parameters.len(),
            &format!("{at}: one pattern per parameter"),
        )?;
        let patterns = arguments
            .iter()
            .zip(parameters)
            .map(|(argument, parameter)| pattern(argument, parameter, instances))
            .collect::<Result<Vec<_>>>()
            .map_err(|error| format!("{at}: {error}"))?;
        let default = boolean(&row["default"])?;
        let frame = choice(&row["frame"], FRAMES)?;
        let unit = choice(&row["unit"], UNITS)?;
        let child = &row["child"];
        if !child.is_null() {
            object(child, &["kind", "domain", "representation"], &[])?;
            let (kind, domain) = (string(&child["kind"])?, string(&child["domain"])?);
            require(
                representations.rows.contains_key(&(
                    kind,
                    domain,
                    string(&child["representation"])?,
                )),
                &format!("{at}: child names no representation row"),
            )?;
            require(
                logical_child(declared, &patterns, instances) == Some((kind, domain)),
                &format!("{at}: child is not the logical child of the applied type"),
            )?;
        }
        // The dense calling convention: the provider whose dense operations
        // use this container, and the vector representation they exchange.
        let (provider, port) = (&row["provider"], &row["vectorPort"]);
        let mut convention = None;
        require(
            provider.is_null() == child.is_null() && port.is_null() == child.is_null(),
            &format!("{at}: a provider and a vector port are declared exactly for a dense child"),
        )?;
        if !child.is_null() {
            object(port, &["kind", "domain", "representation"], &[])?;
            let key = (
                string(&port["kind"])?,
                string(&port["domain"])?,
                string(&port["representation"])?,
            );
            require(
                key.0 == "vector" && child["domain"] == key.1,
                &format!("{at}: vector port is not a vector over the child's domain"),
            )?;
            let port_row = representations
                .rows
                .get(&key)
                .ok_or_else(|| format!("{at}: vector port names no representation row"))?;
            require(
                port_row["layout"] == "",
                &format!("{at}: vector port names a layout selection"),
            )?;
            require(
                port_row["unit"] == unit,
                &format!("{at}: vector port storage belongs to another unit"),
            )?;
            let provider = choice(provider, PROVIDERS)?;
            require(
                units.get(provider) == Some(&unit),
                &format!("{at}: dense provider is installed by another unit"),
            )?;
            require(
                providers
                    .get(key.1)
                    .is_some_and(|named| named.contains(&provider)),
                &format!("{at}: dense provider is not a provider of the child's domain"),
            )?;
            convention = Some((constructor, provider));
        }
        if frame == "canonical" {
            // A field_array frame belongs to its exact field.
            let domain = match (constructor, patterns.first()) {
                ("field_array", Some(Pattern::Domain(field))) => Some(*field),
                ("field_array", _) => None,
                _ => Some(""),
            };
            require(
                domain.is_some_and(|domain| instances.aggregates.contains(&(constructor, domain))),
                &format!(
                    "{at}: a canonical applied representation requires an aggregate frame for its constructor"
                ),
            )?;
        }
        for (other, others, other_name, other_default) in &previous {
            if *other == constructor && overlap(&patterns, others) {
                require(
                    name != *other_name && !(default && *other_default),
                    &format!("{at}: overlapping patterns share an identity or a default"),
                )?;
            }
        }
        // One calling convention per provider and dense constructor.
        if let Some(convention) = convention {
            require(
                conventions.insert(convention),
                &format!("{at}: second dense container of one provider"),
            )?;
        }
        previous.push((constructor, patterns, name, default));
    }
    Ok(())
}

fn pattern<'a>(
    v: &'a Value,
    parameter: Kind<'_>,
    instances: &Instances<'a>,
) -> Result<Pattern<'a>> {
    match (list(v)?, parameter) {
        ([tag], _) if *tag == "any" => Ok(Pattern::Any),
        ([tag, sort, domain], ("Domain", expected)) if *tag == "domain" => {
            let domain = string(domain)?;
            require(
                string(sort)? == expected
                    && instances
                        .domains
                        .get(domain)
                        .is_some_and(|d| d.sort == expected),
                &format!("domain pattern must name a declared {expected} domain"),
            )?;
            Ok(Pattern::Domain(domain))
        }
        ([tag, ty], ("Type", _)) if *tag == "type" => Ok(Pattern::Type(instance(ty, instances)?)),
        ([tag, minimum, maximum], ("Nat", _)) if *tag == "natRange" => {
            let (minimum, maximum) = (extent(minimum)?, extent(maximum)?);
            require(
                minimum <= maximum,
                "natural range minimum exceeds its maximum",
            )?;
            Ok(Pattern::Naturals(minimum, maximum))
        }
        _ => Err("pattern does not match its parameter kind".into()),
    }
}

/// An exact Type pattern: `["apply", constructor, arguments]` naming an
/// admitted logical type instance, never a variant, oracle or service tree.
fn instance<'a>(v: &'a Value, instances: &Instances<'a>) -> Result<Instance<'a>> {
    let [tag, constructor, arguments] = list(v)? else {
        return Err("Type patterns are constructor applications".into());
    };
    require(
        *tag == "apply",
        "Type patterns are constructor applications, never variant, oracle or service trees",
    )?;
    let kind = string(constructor)?;
    let domain = match list(arguments)? {
        [] => "",
        [argument] => {
            let [tag, sort, domain] = list(argument)? else {
                return Err(format!("{kind} pattern argument is not a domain"));
            };
            let domain = string(domain)?;
            require(
                *tag == "domain"
                    && instances
                        .domains
                        .get(domain)
                        .is_some_and(|d| *sort == d.sort),
                &format!("{kind} pattern argument must name a declared domain of its sort"),
            )?;
            domain
        }
        _ => return Err(format!("{kind} pattern is not a logical type instance")),
    };
    require(
        instances.instances.contains(&(kind, domain)),
        &format!("({kind}, {domain}) is not an admitted logical type instance"),
    )?;
    Ok((kind, domain))
}

fn extent(v: &Value) -> Result<u64> {
    let text = string(v)?;
    require(canonical(text), &format!("noncanonical natural {text:?}"))?;
    let value = text
        .parse::<u64>()
        .map_err(|_| format!("natural {text} does not fit u64"))?;
    require(value <= EXTENT, "natural range bound above 1,048,576")?;
    Ok(value)
}

/// The single dense child that the `collection` column fixes, when the
/// element is determined by the patterns.
fn logical_child<'a>(
    declared: Option<&Value>,
    patterns: &[Pattern<'a>],
    instances: &Instances<'_>,
) -> Option<Instance<'a>> {
    match declared?["collection"]["element"].as_str()? {
        "parameter" => match patterns.first()? {
            Pattern::Domain(domain) => match instances.domains.get(domain)?.sort {
                "Field" => Some(("field", *domain)),
                "Group" => Some(("group", *domain)),
                _ => None,
            },
            Pattern::Type(instance) => Some(*instance),
            _ => None,
        },
        "index" => Some(("index", "")),
        _ => None,
    }
}

fn overlap(left: &[Pattern<'_>], right: &[Pattern<'_>]) -> bool {
    left.iter().zip(right).all(|pair| match pair {
        (Pattern::Any, _) | (_, Pattern::Any) => true,
        (Pattern::Domain(a), Pattern::Domain(b)) => a == b,
        (Pattern::Type(a), Pattern::Type(b)) => a == b,
        (Pattern::Naturals(a, b), Pattern::Naturals(c, d)) => a <= d && c <= b,
        _ => false,
    })
}

/// At most one field form row per Field domain.
fn field_forms<'a>(
    v: &'a Value,
    instances: &Instances<'a>,
    representations: &Representations<'a>,
) -> Result<()> {
    let mut fields = BTreeSet::new();
    for row in list(&v["fieldForms"])? {
        object(
            row,
            &["field", "arithmetic", "montgomery", "byteEncoding"],
            &[],
        )?;
        let field = string(&row["field"])?;
        let characteristic = instances
            .characteristic(field)
            .ok_or_else(|| format!("{field} is not a declared Field domain"))?;
        require(
            fields.insert(field),
            &format!("{field} has more than one field form"),
        )?;
        let arithmetic = &row["arithmetic"];
        if !arithmetic.is_null() {
            object(arithmetic, &["form", "representation"], &[])?;
            choice(&arithmetic["form"], &["residue"])?;
            require(
                representations
                    .defaults
                    .get(&("field", field))
                    .is_some_and(|default| arithmetic["representation"] == *default),
                &format!(
                    "{field}: arithmetic names the default representation of its field instance"
                ),
            )?;
            // Residue arithmetic is installed on a prime field or on a binomial
            // extension of a prime base; its coordinates take the prime
            // base's framed field codec.
            let base = instances.residue_base(field).ok_or_else(|| {
                format!(
                    "{field}: residue arithmetic requires a prime field or a binomial extension of a prime base"
                )
            })?;
            require(
                instances.framed.contains_key(&("field", base)),
                &format!(
                    "{field}: residue arithmetic requires a framed field codec of its prime base"
                ),
            )?;
        }
        let montgomery = &row["montgomery"];
        if !montgomery.is_null() {
            object(montgomery, &["wordBytes", "radixBits"], &[])?;
            let radix = number(&montgomery["radixBits"])?;
            require(
                number(&montgomery["wordBytes"])? * 8 == radix,
                &format!("{field}: wordBytes * 8 must equal radixBits"),
            )?;
            require(
                !arithmetic.is_null(),
                &format!("{field}: montgomery requires an arithmetic row"),
            )?;
            require(
                characteristic.bits() <= radix,
                &format!("{field}: montgomery requires a characteristic below 2^radixBits"),
            )?;
        }
        let encoding = &row["byteEncoding"];
        if !encoding.is_null() {
            object(encoding, &["codec", "order"], &[])?;
            require(
                instances
                    .codecs
                    .get(&("field", field))
                    .is_some_and(|codec| encoding["codec"] == *codec)
                    && instances.framed.contains_key(&("field", field)),
                &format!("{field}: byteEncoding names the framed field codec of its field"),
            )?;
            choice(&encoding["order"], &["littleEndian"])?;
        }
    }
    Ok(())
}

fn physical_arguments(v: &Value, catalog: &Catalog<'_>) -> Result<()> {
    let mut operations = BTreeSet::new();
    for row in list(&v["physicalArguments"])? {
        object(row, &["operation"], &[])?;
        let operation = string(&row["operation"])?;
        require(
            catalog.operations.contains_key(operation),
            &format!("{operation} is not a declared operation"),
        )?;
        require(
            operations.insert(operation),
            &format!("{operation} is listed twice"),
        )?;
    }
    Ok(())
}
