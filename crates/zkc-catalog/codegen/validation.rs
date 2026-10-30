//! Declaration formation, independent of any executable or formal profile.
use super::{Result, boolean, list, number, string};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

type Kind<'a> = (&'a str, &'a str);
type Rows<'a> = BTreeMap<&'a str, &'a Value>;

fn require(value: bool, message: &str) -> Result<()> {
    if value { Ok(()) } else { Err(message.into()) }
}
fn identifier(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
        && value
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_')
}
fn path(value: &str, separator: &str) -> bool {
    value.split(separator).all(identifier)
}
fn kind(v: &Value) -> Result<Kind<'_>> {
    Ok((string(&v["kind"])?, string(&v["sort"])?))
}
fn kinds(v: &Value) -> Result<Vec<Kind<'_>>> {
    list(v)?.iter().map(kind).collect()
}
fn names(v: &Value) -> Result<Rows<'_>> {
    let mut result = Rows::new();
    for row in list(v)? {
        let name = string(&row["name"])?;
        require(
            !name.is_empty() && result.insert(name, row).is_none(),
            "duplicate or empty declaration identity",
        )?;
    }
    Ok(result)
}
fn lookup<'a>(rows: &Rows<'a>, name: &Value) -> Result<&'a Value> {
    rows.get(string(name)?)
        .copied()
        .ok_or_else(|| format!("unresolved declaration {name}"))
}
fn index<'a, T>(items: &'a [T], value: &Value) -> Result<&'a T> {
    items
        .get(number(value)?)
        .ok_or("unscoped declaration reference".into())
}
fn limited(v: &Value) -> Result<&[Value]> {
    let values = list(v)?;
    require(values.len() <= 1024, "operation declaration limit")?;
    Ok(values)
}
struct Catalog<'a> {
    types: Rows<'a>,
    capabilities: Rows<'a>,
    meanings: Rows<'a>,
    operations: Rows<'a>,
    sorts: BTreeSet<&'a str>,
    members: BTreeMap<(Kind<'a>, &'a str), Kind<'a>>,
}
impl<'a> Catalog<'a> {
    fn check_kind(&self, k: Kind<'_>) -> Result<()> {
        require(
            if k.0 == "Domain" {
                self.sorts.contains(k.1)
            } else {
                k.1.is_empty()
            },
            "invalid parameter sort",
        )
    }
    fn arguments(&self, rows: &Rows<'a>, row: &Value, key: &str, scope: &[Kind<'a>]) -> Result<()> {
        let expected = kinds(&lookup(rows, &row[key])?["parameters"])?;
        let actual = list(&row["arguments"])?;
        require(actual.len() == expected.len(), "parameter arity mismatch")?;
        for (value, expected) in actual.iter().zip(expected) {
            require(
                *index(scope, value)? == expected,
                "parameter kind or sort mismatch",
            )?;
        }
        Ok(())
    }
    fn operation(&self, op: &'a Value) -> Result<()> {
        require(
            path(string(&op["name"])?, "."),
            "invalid operation identity",
        )?;
        let scope = limited(&op["scope"])?;
        let mut seen = BTreeSet::new();
        let mut roots = BTreeSet::new();
        let mut parameters = Vec::new();
        for term in scope {
            let k = match string(&term["kind"])? {
                "root" => {
                    let name = string(&term["name"])?;
                    require(
                        identifier(name) && roots.insert(name),
                        "invalid or duplicate formal root",
                    )?;
                    let k = kind(&term["parameter"])?;
                    self.check_kind(k)?;
                    k
                }
                "project" => {
                    let owner = *index(&parameters, &term["parent"])?;
                    *self
                        .members
                        .get(&(owner, string(&term["member"])?))
                        .ok_or("associated member parameter mismatch")?
                }
                "apply" => {
                    self.arguments(&self.types, term, "constructor", &parameters)?;
                    ("Type", "")
                }
                "natural" => ("Nat", ""),
                _ => return Err("unknown scope term".into()),
            };
            require(seen.insert(term.to_string()), "duplicate scoped term")?;
            parameters.push(k);
        }
        let signature = &op["signature"];
        let schema = &op["parameters"];
        let numerical = signature["kind"] == "numerical";
        if numerical {
            require(
                scope.len() == 1
                    && scope[0]["kind"] == "root"
                    && parameters[0] == ("Domain", "Field")
                    && number(&signature["fieldTerm"])? == 0
                    && op["stage"] == "CompilerGenerated"
                    && schema["validator"] == "NumericalExpression"
                    && list(&op["facets"])?.is_empty(),
                "invalid numerical signature family",
            )?;
            let needs = limited(&op["requirements"])?;
            require(
                needs.len() == 1
                    && needs[0]["capability"] == "Field"
                    && list(&needs[0]["arguments"])? == [Value::from(0)],
                "numerical family requires exact Field capability",
            )?;
        } else {
            require(
                schema["validator"] != "NumericalExpression",
                "numerical expression requires signature family",
            )?;
            for ports in ["inputs", "outputs"] {
                for p in limited(&signature[ports])? {
                    if let Some(i) = p.get("term") {
                        require(
                            *index(&parameters, i)? == ("Type", ""),
                            "complete port requires scoped Type",
                        )?;
                    } else {
                        self.arguments(&self.types, p, "constructor", &parameters)?;
                    }
                }
            }
        }
        for need in limited(&op["requirements"])? {
            self.arguments(&self.capabilities, need, "capability", &parameters)?;
        }
        let validator = string(&schema["validator"])?;
        let expected = match validator {
            "None" => (0, Some(0)),
            "FieldLiterals" | "GatherIndices" => (0, None),
            "ScatterIndices" => (1, None),
            "MatrixShape" => (2, Some(2)),
            "MatrixVector" => (3, Some(3)),
            _ => (1, Some(1)),
        };
        let maximum = if schema["maximum"].is_null() {
            None
        } else {
            Some(number(&schema["maximum"])?)
        };
        require(
            (number(&schema["minimum"])?, maximum) == expected,
            "parameter bounds mismatch",
        )?;
        let literals = matches!(validator, "FieldLiteral" | "FieldLiterals");
        require(
            literals == schema.get("fieldTerm").is_some(),
            "field literals require exactly one field term",
        )?;
        if let Some(field) = schema.get("fieldTerm") {
            require(
                *index(&parameters, field)? == ("Domain", "Field"),
                "parameter field sort",
            )?;
        }
        require(
            if validator == "AssetIdentity" {
                matches!(
                    schema["assetFormat"].as_str(),
                    Some("zkc.ring/0" | "zkc.relation-bundle/0")
                )
            } else {
                schema.get("assetFormat").is_none()
            },
            "asset parameter format",
        )?;
        self.facets(op)?;
        Ok(())
    }
    fn facets(&self, op: &'a Value) -> Result<()> {
        let mut facets = BTreeMap::new();
        let inputs = op["signature"]["inputs"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let outputs = op["signature"]["outputs"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let scope = list(&op["scope"])?;
        let normalize = |p: &'a Value| -> Result<&'a Value> {
            if let Some(i) = p.get("term") {
                let term = index(scope, i)?;
                if term["kind"] == "apply" {
                    return Ok(term);
                }
            }
            Ok(p)
        };
        let port = |row: &Value, key: &str, output: bool, head: &str| -> Result<&'a Value> {
            let p = normalize(index(if output { outputs } else { inputs }, &row[key])?)?;
            require(
                head.is_empty() || p["constructor"] == head,
                "facet port constructor mismatch",
            )?;
            Ok(p)
        };
        let same = |a: &Value, b: &Value| {
            if a.get("constructor").is_some() && b.get("constructor").is_some() {
                a["constructor"] == b["constructor"] && a["arguments"] == b["arguments"]
            } else {
                a == b
            }
        };
        for f in limited(&op["facets"])? {
            let k = string(&f["kind"])?;
            require(facets.insert(k, f).is_none(), "duplicate semantic facet")?;
            match k {
                "History" => require(
                    same(
                        port(f, "stateInput", false, "")?,
                        port(f, "stateOutput", true, "")?,
                    ),
                    "history successor mismatch",
                )?,
                "Observation" => {
                    require(
                        same(
                            port(f, "stateInput", false, "transcript")?,
                            port(f, "stateOutput", true, "transcript")?,
                        ),
                        "observation successor mismatch",
                    )?;
                    port(f, "payloadInput", false, "")?;
                    require(
                        f["stateInput"] != f["payloadInput"],
                        "observation roles overlap",
                    )?;
                }
                "Sampling" => {
                    let state = if f["provider"] == "Entropy" {
                        "rng"
                    } else {
                        "transcript"
                    };
                    require(
                        same(
                            port(f, "stateInput", false, state)?,
                            port(f, "stateOutput", true, state)?,
                        ),
                        "sampling successor mismatch",
                    )?;
                    port(
                        f,
                        "valueOutput",
                        true,
                        match string(&f["domain"])? {
                            "Field" => "field",
                            "FieldVector" => "vector",
                            _ => "index",
                        },
                    )?;
                    require(
                        f["valueOutput"] != f["stateOutput"],
                        "sampling roles overlap",
                    )?;
                    require(
                        (f["domain"] == "BoundedIndex") == !f["boundInput"].is_null(),
                        "sampling bound domain mismatch",
                    )?;
                    if !f["boundInput"].is_null() {
                        port(f, "boundInput", false, "index")?;
                    }
                }
                "Diagonal" | "Contraction" => {
                    let key = if k == "Diagonal" {
                        "factorsInput"
                    } else {
                        "coefficientsInput"
                    };
                    let factors = port(f, key, false, "vector")?;
                    let values = port(f, "valuesInput", false, "")?;
                    require(
                        f[key] != f["valuesInput"] && inputs.len() == 2 && outputs.len() == 1,
                        "linear facet arity or roles",
                    )?;
                    let output = normalize(if k == "Diagonal" {
                        port(f, "resultOutput", true, "")?
                    } else {
                        &outputs[0]
                    })?;
                    let field = values["constructor"] == "vector";
                    let group = values["constructor"] == "groups";
                    require(field || group, "linear values constructor")?;
                    let domain = unary_argument(values)?;
                    if field {
                        require(
                            unary_argument(factors)? == domain,
                            "linear field domain mismatch",
                        )?;
                    } else {
                        associated_scalar(scope, unary_argument(factors)?, domain)?;
                    }
                    let head = match (field, k) {
                        (true, "Diagonal") => "vector",
                        (true, _) => "field",
                        (false, "Diagonal") => "groups",
                        (false, _) => "group",
                    };
                    require(
                        output["constructor"] == head && unary_argument(output)? == domain,
                        "linear result domain mismatch",
                    )?;
                    has_requirement(op, if field { "Field" } else { "ScalarAction" }, domain)?;
                }
                "Coset" => {
                    port(f, "shiftInput", false, "field")?;
                    port(
                        f,
                        "sizeInput",
                        false,
                        if boolean(&f["sizeIsLength"])? {
                            "vector"
                        } else {
                            "index"
                        },
                    )?;
                    if !f["vectorOutput"].is_null() {
                        port(f, "vectorOutput", true, "vector")?;
                    }
                }
                "DomainValue" => {
                    port(f, "output", true, "")?;
                    if f["rule"] == "Constant" {
                        require(
                            number(&f["parameter"])? < number(&op["parameters"]["minimum"])?,
                            "constant facet outside parameters",
                        )?;
                    } else {
                        port(f, "input", false, "")?;
                    }
                    if matches!(f["rule"].as_str(), Some("Multiply" | "Divide")) {
                        port(f, "otherInput", false, "")?;
                    }
                }
                "AcceptanceGuard" => require(
                    inputs.len() == 1
                        && outputs.is_empty()
                        && normalize(&inputs[0])?["constructor"] == "bool",
                    "guard signature mismatch",
                )?,
                "Conjunction" => require(
                    inputs.len() == 2
                        && outputs.len() == 1
                        && normalize(&inputs[0])?["constructor"] == "bool"
                        && same(normalize(&inputs[0])?, normalize(&inputs[1])?)
                        && same(normalize(&inputs[0])?, normalize(&outputs[0])?),
                    "conjunction signature mismatch",
                )?,
                "Mathematical" => {
                    let meaning = lookup(&self.meanings, &f["identity"])?;
                    mathematical(
                        op,
                        &meaning["laws"],
                        &inputs.iter().map(&normalize).collect::<Result<Vec<_>>>()?,
                        &outputs.iter().map(&normalize).collect::<Result<Vec<_>>>()?,
                    )?;
                }
                _ => {}
            }
        }
        for flag in ["ManagedHistory", "SourceHistory"] {
            if facets.contains_key(flag) {
                let history = facets
                    .get("History")
                    .ok_or("history authoring requires transition")?;
                require(op["stage"] == "Source", "history authoring stage")?;
                let state = port(
                    history,
                    "stateInput",
                    false,
                    if flag == "ManagedHistory" {
                        "transcript"
                    } else {
                        ""
                    },
                )?;
                if flag == "SourceHistory" {
                    let ty = lookup(&self.types, &state["constructor"])?;
                    require(
                        !facets.contains_key("Sampling")
                            && !facets.contains_key("Observation")
                            && boolean(&ty["copy"])?
                            && boolean(&ty["drop"])?
                            && list(&state["arguments"])?.is_empty(),
                        "source history state must be reusable data",
                    )?;
                }
            }
        }
        for f in facets.get("Observation").into_iter().chain(
            facets
                .get("Sampling")
                .filter(|s| s["provider"] == "Transcript"),
        ) {
            let h = facets
                .get("History")
                .ok_or("transcript facet requires history")?;
            require(
                h["stateInput"] == f["stateInput"] && h["stateOutput"] == f["stateOutput"],
                "transcript history roles mismatch",
            )?;
        }
        if let Some(target) = op.get("derivedCounterpart") {
            let source = facets
                .get("Sampling")
                .ok_or("derived counterpart requires sampling")?;
            let counterpart = lookup(&self.operations, target)?;
            let target = list(&counterpart["facets"])?
                .iter()
                .find(|f| f["kind"] == "Sampling")
                .ok_or("counterpart sampling facet missing")?;
            require(
                source["provider"] == "Entropy"
                    && target["provider"] == "Transcript"
                    && counterpart["stage"] == "Construction"
                    && source["domain"] == target["domain"],
                "derived counterpart sampling mismatch",
            )?;
            for role in ["stateInput", "stateOutput", "valueOutput", "boundInput"] {
                require(source[role] == target[role], "counterpart port mismatch")?;
            }
            for (side, state) in [("inputs", "stateInput"), ("outputs", "stateOutput")] {
                let left = list(&op["signature"][side])?;
                let right = list(&counterpart["signature"][side])?;
                require(left.len() == right.len(), "counterpart arity mismatch")?;
                let target_scope = list(&counterpart["scope"])?;
                for (i, (left, right)) in left.iter().zip(right).enumerate() {
                    if i == number(&source[state])? {
                        continue;
                    }
                    let left = normalize(left)?;
                    let right = if let Some(term) = right.get("term") {
                        index(target_scope, term)?
                    } else {
                        right
                    };
                    require(
                        left.get("constructor").is_some()
                            && left["constructor"] == right["constructor"],
                        "counterpart payload mismatch",
                    )?;
                }
            }
        }
        Ok(())
    }
}
fn unary_argument(port: &Value) -> Result<usize> {
    let args = list(&port["arguments"])?;
    require(args.len() == 1, "expected nominal unary port")?;
    number(&args[0])
}
fn associated_scalar(scope: &[Value], scalar: usize, group: usize) -> Result<()> {
    let term = scope.get(scalar).ok_or("unscoped scalar domain")?;
    require(
        term["kind"] == "project"
            && term["member"] == "Scalar"
            && number(&term["parent"])? == group,
        "associated scalar mismatch",
    )
}
fn has_requirement(op: &Value, name: &str, domain: usize) -> Result<()> {
    require(
        list(&op["requirements"])?
            .iter()
            .any(|r| r["capability"] == name && r["arguments"] == serde_json::json!([domain])),
        "missing exact mathematical capability",
    )
}
fn mathematical(op: &Value, laws: &Value, inputs: &[&Value], outputs: &[&Value]) -> Result<()> {
    require(
        !laws.is_null() && outputs.len() == 1,
        "mathematical facet needs signature law and one result",
    )?;
    let shape = string(&laws["signature"])?;
    let group = matches!(shape, "GroupBinary" | "GroupAction");
    let head = if group { "group" } else { "field" };
    require(
        outputs[0]["constructor"] == head,
        "mathematical result constructor",
    )?;
    let domain = unary_argument(outputs[0])?;
    has_requirement(op, if group { "ScalarAction" } else { "Field" }, domain)?;
    let nominal = |p: &Value, h: &str| -> Result<bool> {
        Ok(p["constructor"] == h && unary_argument(p)? == domain)
    };
    let valid = match shape {
        "FieldConstant" => {
            inputs.is_empty()
                && op["parameters"]["validator"] == "FieldLiteral"
                && number(&op["parameters"]["fieldTerm"])? == domain
        }
        "FieldBinary" | "GroupBinary" => {
            inputs.len() == 2 && nominal(inputs[0], head)? && nominal(inputs[1], head)?
        }
        "GroupAction" => {
            if inputs.len() != 2
                || !nominal(inputs[0], "group")?
                || inputs[1]["constructor"] != "field"
            {
                false
            } else {
                associated_scalar(list(&op["scope"])?, unary_argument(inputs[1])?, domain)?;
                true
            }
        }
        "ElementAccess" | "MatrixAccess" => {
            let matrix = shape == "MatrixAccess";
            inputs.len() == if matrix { 3 } else { 2 }
                && nominal(inputs[0], if matrix { "matrix" } else { "vector" })?
                && inputs[1..].iter().all(|p| {
                    p["constructor"] == "index"
                        && p["arguments"].as_array().is_some_and(Vec::is_empty)
                })
        }
        _ => false,
    };
    require(
        valid && (shape == "FieldConstant" || op["parameters"]["validator"] == "None"),
        "mathematical signature or parameters mismatch",
    )
}
fn laws(v: &Value) -> Result<()> {
    if v.is_null() {
        return Ok(());
    }
    let shape = string(&v["signature"])?;
    let algebra = string(&v["algebra"])?;
    let binary = matches!(shape, "FieldBinary" | "GroupBinary");
    let action = shape == "GroupAction";
    let access = algebra == "Access";
    require(
        match algebra {
            "FieldRing" => matches!(shape, "FieldConstant" | "FieldBinary"),
            "GroupModule" => matches!(shape, "GroupBinary" | "GroupAction"),
            _ => matches!(shape, "ElementAccess" | "MatrixAccess"),
        },
        "incompatible mathematical signature law",
    )?;
    for role in ["leftIdentity", "rightIdentity", "annihilator"] {
        let identity = string(&v[role])?;
        require(
            identity == "None"
                || (shape == "FieldBinary" && matches!(identity, "Zero" | "One"))
                || (shape == "GroupBinary" && role != "annihilator" && identity == "GroupIdentity")
                || (action && role == "rightIdentity" && identity == "One"),
            "identity law nominal role mismatch",
        )?;
    }
    require(
        binary || (!boolean(&v["associative"])? && !boolean(&v["commutative"])?),
        "reassociation needs homogeneous binary ports",
    )?;
    require(
        boolean(&v["scalarAction"])? == action,
        "scalar action signature mismatch",
    )?;
    require(
        v["access"]
            == match shape {
                "ElementAccess" => "Element",
                "MatrixAccess" => "MatrixCell",
                _ => "None",
            }
            && (!access || !boolean(&v["total"])?),
        "access signature or totality mismatch",
    )
}

pub(super) fn validate(v: &Value) -> Result<()> {
    let sorts = list(&v["sorts"])?
        .iter()
        .map(string)
        .collect::<Result<BTreeSet<_>>>()?;
    require(
        sorts.len() == list(&v["sorts"])?.len()
            && sorts
                .iter()
                .all(|s| !s.is_empty() && !matches!(*s, "Type" | "Nat")),
        "duplicate or reserved sort",
    )?;
    let mut catalog = Catalog {
        types: names(&v["types"])?,
        capabilities: names(&v["capabilities"])?,
        meanings: names(&v["mathematicalIdentities"])?,
        operations: names(&v["operations"])?,
        sorts,
        members: BTreeMap::new(),
    };
    for ty in catalog.types.values() {
        let parameters = kinds(&ty["parameters"])?;
        require(
            identifier(string(&ty["name"])?) && parameters.len() <= 16,
            "type identity or parameter limit",
        )?;
        for k in &parameters {
            catalog.check_kind(*k)?;
        }
        let copy = boolean(&ty["copy"])?;
        require(
            if ty["custody"] == "Affine" {
                !copy
            } else {
                copy && boolean(&ty["drop"])?
            },
            "incoherent type permissions",
        )?;
        require(
            !boolean(&ty["participants"])? || copy,
            "participant data must be copyable",
        )?;
        require(
            !boolean(&ty["message"])? || boolean(&ty["constructible"])?,
            "message needs decoder authority",
        )?;
        require(
            !boolean(&ty["mathematical"])? || (copy && boolean(&ty["nativeLocal"])?),
            "mathematical data must be reusable and local",
        )?;
        require(
            parameters.is_empty()
                || (parameters.len() == 1 && parameters[0].0 == "Domain")
                || ty["custody"] != "PublicValue",
            "applied types need complete codec model",
        )?;
    }
    for cap in catalog.capabilities.values() {
        for k in kinds(&cap["parameters"])? {
            catalog.check_kind(k)?;
        }
    }
    for m in list(&v["members"])? {
        let owner = kind(&m["owner"])?;
        let result = kind(&m["result"])?;
        catalog.check_kind(owner)?;
        catalog.check_kind(result)?;
        let name = string(&m["name"])?;
        require(
            identifier(name) && catalog.members.insert((owner, name), result).is_none(),
            "invalid or duplicate associated member",
        )?;
    }
    let mut rules = BTreeSet::new();
    for r in list(&v["rules"])? {
        let from = kinds(&lookup(&catalog.capabilities, &r[0])?["parameters"])?;
        let to = kinds(&lookup(&catalog.capabilities, &r[1])?["parameters"])?;
        require(
            from.len() == 1 && from == to && rules.insert(r.to_string()),
            "capability implication mismatch or duplicate",
        )?;
    }
    let mut families = BTreeSet::new();
    let mut family_names = BTreeSet::new();
    for f in list(&v["families"])? {
        let name = string(&f["family"])?;
        require(
            !name.is_empty()
                && !catalog.types.contains_key(name)
                && families.insert((name, string(&f["elementConstructor"])?)),
            "duplicate source family case",
        )?;
        family_names.insert(name);
        let a = kinds(&lookup(&catalog.types, &f["elementConstructor"])?["parameters"])?;
        let b = kinds(&lookup(&catalog.types, &f["resultConstructor"])?["parameters"])?;
        require(a.len() == 1 && a == b, "source family parameter mismatch")?;
    }
    let mut associated = BTreeSet::new();
    for a in list(&v["associatedTypes"])? {
        let sort = string(&a["sort"])?;
        let member = string(&a["member"])?;
        let ps = kinds(&lookup(&catalog.types, &a["constructor"])?["parameters"])?;
        require(
            catalog.sorts.contains(sort)
                && identifier(member)
                && ps == [("Domain", sort)]
                && associated.insert((sort, member)),
            "associated source type mismatch or duplicate",
        )?;
    }
    let mut exports = BTreeSet::new();
    for e in list(&v["exports"])? {
        let module = string(&e["module"])?;
        let name = string(&e["name"])?;
        require(
            module.starts_with("zkc::")
                && path(module, "::")
                && identifier(name)
                && exports.insert((module, name)),
            "invalid or duplicate source export",
        )?;
        if let Some(c) = e.get("constructor") {
            require(
                catalog.types.contains_key(string(c)?) || family_names.contains(string(c)?),
                "unresolved source type export",
            )?;
        } else {
            let parameters = kinds(&lookup(&catalog.capabilities, &e["predicate"])?["parameters"])?;
            require(
                parameters.len() == 1 && parameters[0].0 == "Domain",
                "source capability must be unary domain predicate",
            )?;
        }
    }
    for m in catalog.meanings.values() {
        let name = string(&m["name"])?;
        require(
            name.bytes().next().is_some_and(|c| c.is_ascii_alphabetic())
                && name.bytes().all(|c| c.is_ascii_alphanumeric()),
            "invalid mathematical identity",
        )?;
        laws(&m["laws"])?;
    }
    for i in names(&v["mathematicalIntrinsics"])?.values() {
        lookup(&catalog.meanings, &i["identity"])?;
    }
    for op in catalog.operations.values() {
        catalog
            .operation(op)
            .map_err(|error| format!("{}: {error}", op["name"]))?;
    }
    Ok(())
}
