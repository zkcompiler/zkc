//! Build-time projection. No JSON parser or allocation enters the generated
//! runtime table. Formation is checked before any Rust output is published.

#[path = "validation.rs"]
mod validation;

use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Value};
use std::fmt;

type Result<T> = std::result::Result<T, String>;

// Value's ordinary deserializer accepts duplicate keys. Read the authored
// source through a recursive visitor so no overwritten declaration is hidden.
struct Unique(Value);
impl<'de> Deserialize<'de> for Unique {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> std::result::Result<Self, D::Error> {
        struct Read;
        impl<'de> Visitor<'de> for Read {
            type Value = Unique;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("JSON declaration data without duplicate keys")
            }
            fn visit_bool<E: de::Error>(self, v: bool) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::Bool(v)))
            }
            fn visit_i64<E: de::Error>(self, v: i64) -> std::result::Result<Unique, E> {
                Ok(Unique(v.into()))
            }
            fn visit_u64<E: de::Error>(self, v: u64) -> std::result::Result<Unique, E> {
                Ok(Unique(v.into()))
            }
            fn visit_f64<E: de::Error>(self, _: f64) -> std::result::Result<Unique, E> {
                Err(E::custom("declarations require integer counts"))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> std::result::Result<Unique, E> {
                Ok(Unique(v.into()))
            }
            fn visit_unit<E: de::Error>(self) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::Null))
            }
            fn visit_seq<A: SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> std::result::Result<Unique, A::Error> {
                let mut values = Vec::new();
                while let Some(Unique(value)) = seq.next_element()? {
                    if values.len() == 100_000 {
                        return Err(de::Error::custom("declaration list limit"));
                    }
                    values.push(value);
                }
                Ok(Unique(Value::Array(values)))
            }
            fn visit_map<A: MapAccess<'de>>(
                self,
                mut map: A,
            ) -> std::result::Result<Unique, A::Error> {
                let mut values = Map::new();
                while let Some((key, Unique(value))) = map.next_entry::<String, Unique>()? {
                    if values.insert(key.clone(), value).is_some() {
                        return Err(de::Error::custom(format!("duplicate key {key}")));
                    }
                }
                Ok(Unique(Value::Object(values)))
            }
        }
        deserializer.deserialize_any(Read)
    }
}

pub(super) fn object<'a>(
    v: &'a Value,
    required: &[&str],
    optional: &[&str],
) -> Result<&'a Map<String, Value>> {
    let values = v.as_object().ok_or("expected declaration object")?;
    if let Some(key) = required.iter().find(|key| !values.contains_key(**key)) {
        return Err(format!("missing field {key}"));
    }
    if let Some(key) = values
        .keys()
        .find(|key| !required.contains(&key.as_str()) && !optional.contains(&key.as_str()))
    {
        return Err(format!("unknown field {key}"));
    }
    Ok(values)
}
pub(super) fn list(v: &Value) -> Result<&[Value]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or("expected declaration list".into())
}
pub(super) fn string(v: &Value) -> Result<&str> {
    v.as_str().ok_or("expected declaration string".into())
}
pub(super) fn number(v: &Value) -> Result<usize> {
    v.as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .filter(|&n| n <= 1_048_576)
        .ok_or("declaration count out of range".into())
}
pub(super) fn boolean(v: &Value) -> Result<bool> {
    v.as_bool().ok_or("expected Boolean".into())
}
pub(super) fn choice<'a>(v: &'a Value, choices: &[&str]) -> Result<&'a str> {
    let value = string(v)?;
    if choices.contains(&value) {
        Ok(value)
    } else {
        Err(format!("unknown declaration alternative {value}"))
    }
}
fn quoted(v: &Value) -> Result<String> {
    Ok(format!("{:?}", string(v)?))
}
fn count(v: &Value) -> Result<String> {
    Ok(number(v)?.to_string())
}
fn flag(v: &Value) -> Result<String> {
    Ok(boolean(v)?.to_string())
}
fn variant(v: &Value, ty: &str, choices: &[&str]) -> Result<String> {
    Ok(format!("{ty}::{}", choice(v, choices)?))
}
fn array(v: &Value, item: impl Fn(&Value) -> Result<String>) -> Result<String> {
    Ok(format!(
        "&[{}]",
        list(v)?
            .iter()
            .map(item)
            .collect::<Result<Vec<_>>>()?
            .join(",")
    ))
}
fn optional(v: Option<&Value>, item: impl Fn(&Value) -> Result<String>) -> Result<String> {
    match v {
        Some(v) if !v.is_null() => Ok(format!("Some({})", item(v)?)),
        _ => Ok("None".into()),
    }
}
fn record(ty: &str, fields: &[(&str, String)]) -> String {
    format!(
        "{ty} {{ {} }}",
        fields
            .iter()
            .map(|(name, value)| format!("{name}: {value}"))
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn kind(v: &Value) -> Result<String> {
    object(v, &["kind", "sort"], &[])?;
    match choice(&v["kind"], &["Domain", "Type", "Nat"])? {
        "Domain" => Ok(format!("Kind::Domain({})", quoted(&v["sort"])?)),
        name if string(&v["sort"])?.is_empty() => Ok(format!("Kind::{name}")),
        _ => Err("non-domain kind has a sort".into()),
    }
}
fn term(v: &Value) -> Result<String> {
    Ok(match string(&v["kind"])? {
        "root" => {
            object(v, &["kind", "name", "parameter"], &[])?;
            record(
                "Term::Root",
                &[
                    ("name", quoted(&v["name"])?),
                    ("parameter", kind(&v["parameter"])?),
                ],
            )
        }
        "project" => {
            object(v, &["kind", "member", "parent"], &[])?;
            record(
                "Term::Project",
                &[
                    ("member", quoted(&v["member"])?),
                    ("parent", count(&v["parent"])?),
                ],
            )
        }
        "apply" => {
            object(v, &["kind", "constructor", "arguments"], &[])?;
            application(v, "Term::Apply")?
        }
        "natural" => {
            object(v, &["kind", "value"], &[])?;
            let text = string(&v["value"])?;
            let value: u64 = text.parse().map_err(|_| "invalid natural term")?;
            if value > 1_048_576 || value.to_string() != text {
                return Err("noncanonical natural term".into());
            }
            format!("Term::Natural({value})")
        }
        _ => return Err("unknown scope term".into()),
    })
}
fn application(v: &Value, ty: &str) -> Result<String> {
    Ok(record(
        ty,
        &[
            ("constructor", quoted(&v["constructor"])?),
            ("arguments", array(&v["arguments"], count)?),
        ],
    ))
}
fn port(v: &Value) -> Result<String> {
    if v.get("term").is_some() {
        object(v, &["term"], &[])?;
        Ok(format!("Port::Term({})", count(&v["term"])?))
    } else {
        object(v, &["constructor", "arguments"], &[])?;
        application(v, "Port::Apply")
    }
}
fn signature(v: &Value) -> Result<String> {
    match string(&v["kind"])? {
        "fixed" => {
            object(v, &["kind", "inputs", "outputs"], &[])?;
            Ok(record(
                "Signature::Fixed",
                &[
                    ("inputs", array(&v["inputs"], port)?),
                    ("outputs", array(&v["outputs"], port)?),
                ],
            ))
        }
        "numerical" => {
            object(v, &["kind", "fieldTerm", "result"], &[])?;
            let result = match choice(&v["result"], &["map", "sum", "product"])? {
                "map" => "Map",
                "sum" => "Sum",
                _ => "Product",
            };
            Ok(record(
                "Signature::Numerical",
                &[
                    ("field", count(&v["fieldTerm"])?),
                    ("result", format!("NumericalResult::{result}")),
                ],
            ))
        }
        _ => Err("unknown signature family".into()),
    }
}
fn parameters(v: &Value) -> Result<String> {
    object(
        v,
        &["validator", "minimum", "maximum"],
        &["fieldTerm", "assetFormat"],
    )?;
    Ok(record(
        "Parameters",
        &[
            (
                "validator",
                variant(
                    &v["validator"],
                    "ParameterValidator",
                    &[
                        "None",
                        "Natural",
                        "Extent",
                        "FieldLiteral",
                        "FieldLiterals",
                        "MatrixShape",
                        "MatrixIdentity",
                        "AssetIdentity",
                        "MatrixVector",
                        "GatherIndices",
                        "ScatterIndices",
                        "NumericalExpression",
                        "NativeOrigin",
                        "NativeIndexBlock",
                    ],
                )?,
            ),
            ("minimum", count(&v["minimum"])?),
            ("maximum", optional(v.get("maximum"), count)?),
            ("field", optional(v.get("fieldTerm"), count)?),
            ("asset_format", optional(v.get("assetFormat"), quoted)?),
        ],
    ))
}
fn facet(v: &Value) -> Result<String> {
    let name = string(&v["kind"])?;
    let (keys, fields): (&[&str], Vec<(&str, String)>) = match name {
        "PublicReplay" | "DeterministicData" | "AcceptanceGuard" | "Conjunction"
        | "SourceHistory" | "ManagedHistory" => {
            object(v, &["kind"], &[])?;
            return Ok(format!("Facet::{name}"));
        }
        "Mathematical" => {
            object(v, &["kind", "identity"], &[])?;
            return Ok(format!("Facet::Mathematical({})", quoted(&v["identity"])?));
        }
        "History" => (
            &["stateInput", "stateOutput"],
            vec![
                ("state_input", count(&v["stateInput"])?),
                ("state_output", count(&v["stateOutput"])?),
            ],
        ),
        "Observation" => (
            &["stateInput", "payloadInput", "stateOutput"],
            vec![
                ("state_input", count(&v["stateInput"])?),
                ("payload_input", count(&v["payloadInput"])?),
                ("state_output", count(&v["stateOutput"])?),
            ],
        ),
        "Sampling" => (
            &[
                "provider",
                "domain",
                "stateInput",
                "valueOutput",
                "stateOutput",
                "boundInput",
            ],
            vec![
                (
                    "provider",
                    variant(
                        &v["provider"],
                        "SamplingProvider",
                        &["Entropy", "Transcript"],
                    )?,
                ),
                (
                    "domain",
                    variant(
                        &v["domain"],
                        "SamplingDomain",
                        &["Field", "FieldVector", "BoundedIndex", "IndexBlock"],
                    )?,
                ),
                ("state_input", count(&v["stateInput"])?),
                ("value_output", count(&v["valueOutput"])?),
                ("state_output", count(&v["stateOutput"])?),
                ("bound_input", optional(v.get("boundInput"), count)?),
            ],
        ),
        "Diagonal" => (
            &["factorsInput", "valuesInput", "resultOutput"],
            vec![
                ("factors_input", count(&v["factorsInput"])?),
                ("values_input", count(&v["valuesInput"])?),
                ("result_output", count(&v["resultOutput"])?),
            ],
        ),
        "Contraction" => (
            &["coefficientsInput", "valuesInput"],
            vec![
                ("coefficients_input", count(&v["coefficientsInput"])?),
                ("values_input", count(&v["valuesInput"])?),
            ],
        ),
        "Coset" => (
            &[
                "shiftInput",
                "sizeInput",
                "sizeIsLength",
                "foldedOutput",
                "vectorOutput",
            ],
            vec![
                ("shift_input", count(&v["shiftInput"])?),
                ("size_input", count(&v["sizeInput"])?),
                ("size_is_length", flag(&v["sizeIsLength"])?),
                ("folded_output", flag(&v["foldedOutput"])?),
                ("vector_output", optional(v.get("vectorOutput"), count)?),
            ],
        ),
        "DomainValue" => {
            let name = choice(&v["rule"], &["Constant", "Length", "Multiply", "Divide"])?;
            let (extra, fields): (&[&str], Vec<(&str, String)>) = match name {
                "Constant" => (&["parameter"], vec![("parameter", count(&v["parameter"])?)]),
                "Length" => (&["input"], vec![("input", count(&v["input"])?)]),
                _ => (
                    &["input", "otherInput"],
                    vec![
                        ("input", count(&v["input"])?),
                        ("other", count(&v["otherInput"])?),
                    ],
                ),
            };
            let mut required = vec!["kind", "rule", "output"];
            required.extend(extra);
            object(v, &required, &[])?;
            return Ok(record(
                "Facet::DomainValue",
                &[
                    ("rule", record(&format!("DomainValueRule::{name}"), &fields)),
                    ("output", count(&v["output"])?),
                ],
            ));
        }
        _ => return Err(format!("unknown facet {name}")),
    };
    let mut required = vec!["kind"];
    required.extend(keys);
    object(v, &required, &[])?;
    Ok(record(&format!("Facet::{name}"), &fields))
}
fn operation(v: &Value) -> Result<String> {
    object(
        v,
        &[
            "name",
            "scope",
            "stage",
            "parameters",
            "signature",
            "requirements",
            "facets",
        ],
        &["derivedCounterpart"],
    )?;
    Ok(record(
        "Operation",
        &[
            ("name", quoted(&v["name"])?),
            ("scope", array(&v["scope"], term)?),
            (
                "stage",
                variant(
                    &v["stage"],
                    "Stage",
                    &["Source", "Construction", "CompilerGenerated", "Physical"],
                )?,
            ),
            ("parameters", parameters(&v["parameters"])?),
            ("signature", signature(&v["signature"])?),
            (
                "requirements",
                array(&v["requirements"], |r| {
                    object(r, &["capability", "arguments"], &[])?;
                    Ok(record(
                        "Requirement",
                        &[
                            ("capability", quoted(&r["capability"])?),
                            ("arguments", array(&r["arguments"], count)?),
                        ],
                    ))
                })?,
            ),
            ("facets", array(&v["facets"], facet)?),
            (
                "derived_counterpart",
                optional(v.get("derivedCounterpart"), quoted)?,
            ),
        ],
    ))
}
fn constructor(v: &Value) -> Result<String> {
    object(
        v,
        &[
            "name",
            "parameters",
            "copy",
            "drop",
            "custody",
            "nativeLocal",
            "mathematical",
            "participants",
            "constructible",
            "message",
        ],
        &[],
    )?;
    Ok(record(
        "TypeConstructor",
        &[
            ("name", quoted(&v["name"])?),
            ("parameters", array(&v["parameters"], kind)?),
            ("copy", flag(&v["copy"])?),
            ("drop", flag(&v["drop"])?),
            (
                "custody",
                variant(
                    &v["custody"],
                    "Custody",
                    &["PublicValue", "PrivateImmutable", "Affine"],
                )?,
            ),
            ("native_local", flag(&v["nativeLocal"])?),
            ("mathematical", flag(&v["mathematical"])?),
            ("participants", flag(&v["participants"])?),
            ("constructible", flag(&v["constructible"])?),
            ("message", flag(&v["message"])?),
        ],
    ))
}

fn consumer_operation(v: &Value) -> Result<String> {
    let fields = object(
        v,
        &[
            "operation",
            "scope",
            "stage",
            "parameters",
            "signature",
            "requirements",
        ],
        &[],
    )?;
    // Reuse exact syntax checking for the consumed operation shape, without
    // installing another operation or inventing facets for the expectation.
    let mut expected = fields.clone();
    let identity = expected.remove("operation").unwrap();
    expected.insert("name".into(), identity);
    expected.insert("facets".into(), Value::Array(Vec::new()));
    operation(&Value::Object(expected))?;
    let roots = list(&v["scope"])?
        .iter()
        .filter(|term| term["kind"] == "root")
        .map(|term| kind(&term["parameter"]))
        .collect::<Result<Vec<_>>>()?;
    Ok(record(
        "ConsumerProfileOperation",
        &[
            ("operation", quoted(&v["operation"])?),
            ("static_parameters", format!("&[{}]", roots.join(","))),
        ],
    ))
}

fn consumer_profile(v: &Value) -> Result<String> {
    object(
        v,
        &[
            "name",
            "implementation",
            "typeConstructors",
            "parameterValidators",
            "operations",
        ],
        &[],
    )?;
    choice(&v["implementation"], &["unselected"])?;
    Ok(record(
        "ConsumerProfile",
        &[
            ("name", quoted(&v["name"])?),
            (
                "implementation",
                "ConsumerImplementation::Unselected".into(),
            ),
            ("type_constructors", array(&v["typeConstructors"], quoted)?),
            (
                "parameter_validators",
                array(&v["parameterValidators"], |v| {
                    variant(
                        v,
                        "ParameterValidator",
                        &[
                            "None",
                            "Natural",
                            "Extent",
                            "FieldLiteral",
                            "FieldLiterals",
                            "MatrixShape",
                            "MatrixIdentity",
                            "AssetIdentity",
                            "MatrixVector",
                            "GatherIndices",
                            "ScatterIndices",
                            "NativeOrigin",
                            "NativeIndexBlock",
                        ],
                    )
                })?,
            ),
            ("operations", array(&v["operations"], consumer_operation)?),
        ],
    ))
}
fn laws(v: &Value) -> Result<String> {
    object(
        v,
        &[
            "algebra",
            "signature",
            "associative",
            "commutative",
            "total",
            "leftIdentity",
            "rightIdentity",
            "annihilator",
            "scalarAction",
            "access",
        ],
        &[],
    )?;
    let identities = &["None", "Zero", "One", "GroupIdentity"];
    Ok(record(
        "Laws",
        &[
            (
                "algebra",
                variant(
                    &v["algebra"],
                    "Algebra",
                    &["FieldRing", "GroupModule", "Access"],
                )?,
            ),
            (
                "signature",
                variant(
                    &v["signature"],
                    "MathematicalSignature",
                    &[
                        "FieldConstant",
                        "FieldBinary",
                        "GroupBinary",
                        "GroupAction",
                        "ElementAccess",
                        "MatrixAccess",
                    ],
                )?,
            ),
            ("associative", flag(&v["associative"])?),
            ("commutative", flag(&v["commutative"])?),
            ("total", flag(&v["total"])?),
            (
                "left_identity",
                variant(&v["leftIdentity"], "Identity", identities)?,
            ),
            (
                "right_identity",
                variant(&v["rightIdentity"], "Identity", identities)?,
            ),
            (
                "annihilator",
                variant(&v["annihilator"], "Identity", identities)?,
            ),
            ("scalar_action", flag(&v["scalarAction"])?),
            (
                "access",
                variant(&v["access"], "Access", &["None", "Element", "MatrixCell"])?,
            ),
        ],
    ))
}

pub fn generate(bytes: &[u8]) -> Result<String> {
    if bytes.len() > 64 * 1024 * 1024 {
        return Err("declaration byte limit".into());
    }
    let Unique(v) = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
    object(
        &v,
        &[
            "format",
            "sorts",
            "types",
            "operations",
            "members",
            "rules",
            "capabilities",
            "exports",
            "families",
            "associatedTypes",
            "mathematicalIdentities",
            "mathematicalIntrinsics",
            "consumerProfiles",
        ],
        &[],
    )?;
    choice(&v["format"], &["zkc.contract-declarations/0"])?;
    let fields = [
        ("sorts", array(&v["sorts"], quoted)?),
        ("types", array(&v["types"], constructor)?),
        ("operations", array(&v["operations"], operation)?),
        (
            "consumer_profiles",
            array(&v["consumerProfiles"], consumer_profile)?,
        ),
        (
            "members",
            array(&v["members"], |v| {
                object(v, &["name", "owner", "result"], &[])?;
                Ok(record(
                    "Member",
                    &[
                        ("name", quoted(&v["name"])?),
                        ("owner", kind(&v["owner"])?),
                        ("result", kind(&v["result"])?),
                    ],
                ))
            })?,
        ),
        (
            "rules",
            array(&v["rules"], |v| {
                let pair = list(v)?;
                if pair.len() != 2 {
                    return Err("implication needs two predicates".into());
                }
                Ok(record(
                    "Rule",
                    &[
                        ("premise", quoted(&pair[0])?),
                        ("conclusion", quoted(&pair[1])?),
                    ],
                ))
            })?,
        ),
        (
            "capabilities",
            array(&v["capabilities"], |v| {
                object(v, &["name", "parameters"], &[])?;
                Ok(record(
                    "Capability",
                    &[
                        ("name", quoted(&v["name"])?),
                        ("parameters", array(&v["parameters"], kind)?),
                    ],
                ))
            })?,
        ),
        (
            "exports",
            array(&v["exports"], |v| {
                let (key, ty) = if v.get("constructor").is_some() {
                    ("constructor", "Constructor")
                } else {
                    ("predicate", "Predicate")
                };
                object(v, &["module", "name", key], &[])?;
                Ok(record(
                    "Export",
                    &[
                        ("module", quoted(&v["module"])?),
                        ("name", quoted(&v["name"])?),
                        (
                            "target",
                            format!("ExportTarget::{ty}({})", quoted(&v[key])?),
                        ),
                    ],
                ))
            })?,
        ),
        (
            "families",
            array(&v["families"], |v| {
                object(
                    v,
                    &["family", "elementConstructor", "resultConstructor"],
                    &[],
                )?;
                Ok(record(
                    "Family",
                    &[
                        ("family", quoted(&v["family"])?),
                        ("element", quoted(&v["elementConstructor"])?),
                        ("result", quoted(&v["resultConstructor"])?),
                    ],
                ))
            })?,
        ),
        (
            "associated_types",
            array(&v["associatedTypes"], |v| {
                object(v, &["sort", "member", "constructor"], &[])?;
                Ok(record(
                    "AssociatedType",
                    &[
                        ("sort", quoted(&v["sort"])?),
                        ("member", quoted(&v["member"])?),
                        ("constructor", quoted(&v["constructor"])?),
                    ],
                ))
            })?,
        ),
        (
            "mathematical_identities",
            array(&v["mathematicalIdentities"], |v| {
                object(v, &["name", "laws"], &[])?;
                Ok(record(
                    "MathematicalIdentity",
                    &[
                        ("name", quoted(&v["name"])?),
                        ("laws", optional(v.get("laws"), laws)?),
                    ],
                ))
            })?,
        ),
        (
            "mathematical_intrinsics",
            array(&v["mathematicalIntrinsics"], |v| {
                object(
                    v,
                    &[
                        "name",
                        "identity",
                        "domainKind",
                        "naturals",
                        "domainPoints",
                        "scalar",
                    ],
                    &[],
                )?;
                Ok(record(
                    "Intrinsic",
                    &[
                        ("name", quoted(&v["name"])?),
                        ("identity", quoted(&v["identity"])?),
                        (
                            "domain",
                            variant(
                                &v["domainKind"],
                                "IntrinsicDomain",
                                &[
                                    "Boolean",
                                    "Index",
                                    "Collection",
                                    "Field",
                                    "Group",
                                    "Quotient",
                                ],
                            )?,
                        ),
                        ("naturals", count(&v["naturals"])?),
                        ("domain_points", flag(&v["domainPoints"])?),
                        ("scalar", flag(&v["scalar"])?),
                    ],
                ))
            })?,
        ),
    ];
    validation::validate(&v)?;
    Ok(format!(
        "// Generated from the shared declaration source.\npub static CATALOG: Catalog = {};\n",
        record("Catalog", &fields)
    ))
}
