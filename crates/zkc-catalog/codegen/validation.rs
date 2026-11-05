//! Declaration formation, independent of any executable or formal profile.
#[path = "installation.rs"]
mod installation;
#[path = "instances.rs"]
mod instances;

use super::{Result, boolean, choice, list, number, object, string};
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
    fn consumer_profile(&self, profile: &'a Value) -> Result<()> {
        let mut constructors = BTreeSet::new();
        for name in list(&profile["typeConstructors"])? {
            lookup(&self.types, name)?;
            require(
                constructors.insert(string(name)?),
                "duplicate profile constructor",
            )?;
        }
        let mut validators = BTreeSet::new();
        for name in list(&profile["parameterValidators"])? {
            require(
                validators.insert(string(name)?),
                "duplicate profile validator",
            )?;
        }
        let mut selected = BTreeSet::new();
        for entry in list(&profile["operations"])? {
            let op = lookup(&self.operations, &entry["operation"])?;
            require(
                selected.insert(string(&entry["operation"])?),
                "duplicate profile membership",
            )?;
            require(
                op["signature"]["kind"] == "fixed",
                "unsupported profile signature family",
            )?;
            for field in ["scope", "stage", "signature", "requirements", "parameters"] {
                require(
                    entry[field] == op[field],
                    &format!("consumer operation {field} mismatch"),
                )?;
            }
            require(
                validators.contains(string(&op["parameters"]["validator"])?),
                "unsupported profile validator",
            )?;
            let mut parameters = Vec::new();
            for term in list(&op["scope"])? {
                let result = match string(&term["kind"])? {
                    "root" => kind(&term["parameter"])?,
                    "project" => {
                        let owner = *index(&parameters, &term["parent"])?;
                        *self
                            .members
                            .get(&(owner, string(&term["member"])?))
                            .ok_or("unknown profile associated member")?
                    }
                    "apply" => ("Type", ""),
                    "natural" => ("Nat", ""),
                    _ => return Err("unknown profile term".into()),
                };
                require(
                    result.0 != "Type" || term["kind"] == "apply",
                    "unsupported profile Type term",
                )?;
                if term["kind"] == "apply" {
                    require(
                        constructors.contains(string(&term["constructor"])?),
                        "unsupported profile type constructor",
                    )?;
                }
                parameters.push(result);
            }
            for field in ["inputs", "outputs"] {
                for port in list(&op["signature"][field])? {
                    if let Some(name) = port.get("constructor") {
                        require(
                            constructors.contains(string(name)?),
                            "unsupported profile type constructor",
                        )?;
                    }
                }
            }
        }
        Ok(())
    }
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
            "NativeIndexBlock" => {
                if string(&op["name"])? == "transcript.native.indexed.indices" {
                    (3, Some(3))
                } else {
                    (4, Some(4))
                }
            }
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
                "Succession" => {
                    // Identity transfer of one resource: the same Slot root on
                    // both sides, and no other resource port to duplicate or
                    // drop custody.
                    let slot = unary_argument(port(f, "stateInput", false, "resource_unit")?)?;
                    require(
                        unary_argument(port(f, "stateOutput", true, "resource_unit")?)? == slot,
                        "succession resource type mismatch",
                    )?;
                    let root = scope.get(slot).ok_or("unscoped declaration reference")?;
                    require(
                        root["kind"] == "root"
                            && root["parameter"]["kind"] == "Domain"
                            && root["parameter"]["sort"] == "Slot",
                        "succession requires a Slot root",
                    )?;
                    for (ports, role) in [(inputs, "stateInput"), (outputs, "stateOutput")] {
                        let state = number(&f[role])?;
                        for (i, p) in ports.iter().enumerate() {
                            require(
                                i == state || normalize(p)?["constructor"] != "resource_unit",
                                "succession admits no other resource port",
                            )?;
                        }
                    }
                }
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
                            "IndexBlock" => "indices",
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
                "PublicReplay" | "DeterministicData" | "SourceHistory" | "ManagedHistory" => {}
                _ => return Err(format!("unknown facet {k}")),
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

/// Check the declaration document and the native installation document
/// together; the second references the first one way.
/// A source type as a comparable key: a static parameter (with its associated
/// member) or a parameterless constructor, after checking its references.
type SourceTerm<'a> = (Option<usize>, &'a str, &'a str);
type SourceShape<'a> = (
    &'a str,
    Vec<Kind<'a>>,
    Vec<SourceTerm<'a>>,
    Option<SourceTerm<'a>>,
);
fn source_term<'a>(
    catalog: &Catalog<'a>,
    statics: &[Kind<'a>],
    t: &'a Value,
) -> Result<SourceTerm<'a>> {
    if let Some(head) = t.get("constructor") {
        let head = string(head)?;
        require(
            catalog
                .types
                .get(head)
                .is_some_and(|ty| list(&ty["parameters"]).is_ok_and(|p| p.is_empty())),
            "unknown source constructor",
        )?;
        return Ok((None, "", head));
    }
    let index = number(&t["static"])?;
    let parameter = *statics
        .get(index)
        .ok_or("source static index out of range")?;
    let member = match t.get("member") {
        Some(m) => string(m)?,
        None => "",
    };
    require(
        member.is_empty() || catalog.members.contains_key(&(parameter, member)),
        "unknown source static member",
    )?;
    Ok((Some(index), member, ""))
}
fn source_shape<'a>(
    catalog: &Catalog<'a>,
    kind_name: &'a str,
    statics: Vec<Kind<'a>>,
    inputs: &[&'a Value],
    output: &'a Value,
) -> Result<SourceShape<'a>> {
    require(
        matches!(kind_name, "Math" | "Local" | "Interface" | "Requirement"),
        "unknown source declaration kind",
    )?;
    for k in &statics {
        catalog.check_kind(*k)?;
    }
    let inputs = inputs
        .iter()
        .map(|t| source_term(catalog, &statics, t))
        .collect::<Result<Vec<_>>>()?;
    let output = if output.is_null() {
        None
    } else {
        Some(source_term(catalog, &statics, output)?)
    };
    require(
        matches!(kind_name, "Interface" | "Requirement") == output.is_none()
            && (!matches!(kind_name, "Interface" | "Requirement") || inputs.is_empty()),
        "source declaration kind and signature disagree",
    )?;
    Ok((kind_name, statics, inputs, output))
}
/// Installed source declarations, rules and notations. Rule shapes and every
/// declaration reference are data. Service ownership below separately checks
/// the semantic constructor rule supported by the service adapter.
fn frontend<'a>(
    v: &'a Value,
    catalog: &Catalog<'a>,
    exports: &mut BTreeSet<(&'a str, &'a str)>,
) -> Result<BTreeSet<&'a str>> {
    let mut rules = BTreeMap::new();
    for r in list(&v["frontendRules"])? {
        object(r, &["name", "kind", "statics", "inputs", "output"], &[])?;
        let name = string(&r["name"])?;
        let inputs = list(&r["inputs"])?.iter().collect::<Vec<_>>();
        let shape = source_shape(
            catalog,
            string(&r["kind"])?,
            kinds(&r["statics"])?,
            &inputs,
            &r["output"],
        )?;
        require(
            identifier(name) && rules.insert(name, shape).is_none(),
            "invalid or duplicate frontend rule",
        )?;
    }
    let intrinsics = names(&v["mathematicalIntrinsics"])?;
    let mut identities = BTreeSet::new();
    let mut prelude_names = BTreeSet::new();
    let mut declared = BTreeSet::new();
    for r in list(&v["frontendDeclarations"])? {
        let identity = string(&r["identity"])?;
        require(
            !identity.is_empty() && identities.insert(identity),
            "duplicate frontend identity",
        )?;
        let module = string(&r["owner"])?;
        let name = string(&r["name"])?;
        require(
            module.starts_with("zkc::") && path(module, "::") && identifier(name),
            "invalid frontend owner",
        )?;
        require(
            exports.insert((module, name)),
            "duplicate frontend ownership",
        )?;
        declared.insert((module, name));
        let mut parameters = BTreeSet::new();
        let mut statics = Vec::new();
        for s in list(&r["statics"])? {
            let static_name = string(&s["name"])?;
            require(
                identifier(static_name) && parameters.insert(static_name),
                "invalid or duplicate source parameter name",
            )?;
            statics.push(kind(&s["parameter"])?);
        }
        let mut inputs = Vec::new();
        for s in list(&r["inputs"])? {
            let input_name = string(&s["name"])?;
            require(
                identifier(input_name) && parameters.insert(input_name),
                "invalid or duplicate source parameter name",
            )?;
            inputs.push(&s["type"]);
        }
        let kind_name = string(&r["kind"])?;
        let shape = source_shape(catalog, kind_name, statics, &inputs, &r["output"])?;
        let target = string(&r["association"]["target"])?;
        match string(&r["association"]["kind"])? {
            "rule" => require(
                rules.get(target) == Some(&shape),
                "frontend rule signature mismatch",
            )?,
            "primitive" => require(
                match kind_name {
                    "Math" => intrinsics.contains_key(target),
                    "Local" => catalog.operations.contains_key(target),
                    _ => false,
                },
                "frontend primitive kind mismatch",
            )?,
            _ => return Err("unknown frontend association".into()),
        }
        require(
            !boolean(&r["prelude"])? || prelude_names.insert(name),
            "duplicate prelude frontend name",
        )?;
    }
    let mut notations = BTreeSet::new();
    for r in list(&v["frontendNotations"])? {
        let module = string(&r["owner"])?;
        let symbol = string(&r["symbol"])?;
        let target = string(&r["target"])?;
        require(
            declared.iter().any(|(owner, _)| *owner == module),
            "frontend notation owner is not installed",
        )?;
        require(
            declared.contains(&(module, target)),
            "frontend notation target is not declared",
        )?;
        require(
            !symbol.is_empty() && !symbol.chars().any(char::is_whitespace),
            "invalid frontend notation symbol",
        )?;
        let fixity = &r["fixity"];
        require(
            fixity.is_null() || (1..=99).contains(&number(&fixity["precedence"])?),
            "invalid frontend notation fixity",
        )?;
        require(
            notations.insert((module, symbol, target)),
            "duplicate frontend notation",
        )?;
    }
    Ok(identities)
}
pub(super) fn validate(v: &Value, installation: &Value) -> Result<()> {
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
        // A `parameter` element is the value type of the first parameter:
        // `field` over a Field domain, `group` over a Group domain, or the
        // Type argument itself.
        require(
            ty["collection"]["element"] != "parameter"
                || matches!(
                    parameters.first(),
                    Some(("Domain", "Field" | "Group") | ("Type", _))
                ),
            "a parameter collection element needs a Field, Group or Type first parameter",
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
    // The members a capability names: required ones, then permitted ones.
    for cap in catalog.capabilities.values() {
        let name = string(&cap["name"])?;
        let mut named = BTreeSet::new();
        for member in list(&cap["requires"])?.iter().chain(list(&cap["permits"])?) {
            require(
                named.insert(string(member)?),
                &format!("{name} names a member twice"),
            )?;
        }
        if named.is_empty() {
            continue;
        }
        let parameters = kinds(&cap["parameters"])?;
        let [("Domain", sort)] = parameters[..] else {
            return Err(format!(
                "{name} names members but is not a unary domain predicate"
            ));
        };
        for member in named {
            require(
                catalog.members.contains_key(&(("Domain", sort), member)),
                &format!("{name} names {member}, which is not a member of its sort"),
            )?;
        }
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
    let mut identities = frontend(v, &catalog, &mut exports)?;
    // A home names a catalog type constructor or a declared frontend
    // constructor, a structural head the source language owns. Exactly one
    // row spells each form, the structural meaning the frontend gives a head.
    const FORMS: &[&str] = &["OracleHandle", "OracleHandleSequence", "FiniteDescriptor"];
    let mut constructors = BTreeSet::new();
    let mut forms = BTreeSet::new();
    for r in list(&v["frontendConstructors"])? {
        object(r, &["name", "form"], &[])?;
        let name = string(&r["name"])?;
        require(
            identifier(name) && !catalog.types.contains_key(name) && constructors.insert(name),
            "invalid or duplicate frontend constructor",
        )?;
        require(
            forms.insert(choice(&r["form"], FORMS)?),
            "duplicate frontend constructor form",
        )?;
    }
    require(
        forms.len() == FORMS.len(),
        "missing frontend constructor form",
    )?;
    let mut homes = BTreeSet::new();
    for r in list(&v["frontendHomes"])? {
        let head = string(&r["constructor"])?;
        let module = string(&r["module"])?;
        require(
            (catalog.types.contains_key(head) || constructors.contains(head))
                && module.starts_with("zkc::")
                && path(module, "::"),
            "invalid frontend home",
        )?;
        require(homes.insert(head), "duplicate frontend home")?;
        let mut members = BTreeSet::new();
        for member in list(&r["members"])? {
            let name = string(member)?;
            require(
                name.starts_with("zkc::") && path(name, "::") && members.insert(name),
                "invalid frontend home members",
            )?;
        }
    }
    let mut signatures = BTreeMap::new();
    for r in list(&v["serviceSignatures"])? {
        object(r, &["name", "capability"], &[])?;
        let name = string(&r["name"])?;
        let capability = string(&r["capability"])?;
        require(
            identifier(name) && signatures.insert(name, capability).is_none(),
            "invalid or duplicate service signature",
        )?;
        if !capability.is_empty() {
            require(
                kinds(&lookup(&catalog.capabilities, &r["capability"])?["parameters"])?
                    == [("Domain", "Field")],
                "unknown service capability",
            )?;
        }
    }
    let mut service_constructors = BTreeSet::new();
    for r in list(&v["frontendDeclarations"])? {
        if string(&r["association"]["kind"])? == "rule"
            && string(&r["association"]["target"])? == "RandomConstructor"
        {
            service_constructors.insert(string(&r["identity"])?);
        }
    }
    let mut methods = BTreeSet::new();
    for r in list(&v["serviceMethods"])? {
        let identity = string(&r["identity"])?;
        require(
            !identity.is_empty() && identities.insert(identity),
            "duplicate service method identity",
        )?;
        let constructor = string(&r["constructor"])?;
        require(
            service_constructors.contains(constructor),
            "invalid service method constructor",
        )?;
        let name = string(&r["name"])?;
        require(
            identifier(name) && methods.insert((constructor, name)),
            "invalid or duplicate service method",
        )?;
        require(
            signatures.get(string(&r["signature"])?) == Some(&string(&r["capability"])?),
            "service method capability mismatch",
        )?;
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
    for profile in names(&v["consumerProfiles"])?.values() {
        catalog.consumer_profile(profile)?;
    }
    let instances = instances::Instances::new(v, &catalog)?;
    installation::validate(installation, &catalog, &instances)
        .map_err(|error| format!("native installation: {error}"))
}
