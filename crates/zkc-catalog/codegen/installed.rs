//! Projection of the installed-instance tables and the native installation
//! document, after both are validated. Each row keeps its declared order; a
//! domain reference becomes a `DomainIdentity`, whose variant names are
//! presentation only.
use super::{Result, array, boolean, choice, count, flag, list, object, quoted, record, string};
use serde_json::Value;
use std::collections::BTreeMap;

/// Domain identities and their generated variant names.
pub(super) struct Identities(BTreeMap<String, String>);

impl Identities {
    /// One variant per declared domain; distinct identities whose
    /// presentations coincide refuse.
    pub(super) fn new(v: &Value) -> Result<Self> {
        let mut variants = BTreeMap::new();
        let mut presentations: BTreeMap<String, String> = BTreeMap::new();
        for row in list(&v["domains"])? {
            let identity = string(&row["identity"])?;
            let mut variant: String = identity
                .split(|c: char| !c.is_ascii_alphanumeric())
                .filter(|part| !part.is_empty())
                .map(|part| {
                    let mut chars = part.chars();
                    chars
                        .next()
                        .map(|first| first.to_ascii_uppercase().to_string() + chars.as_str())
                        .unwrap_or_default()
                })
                .collect();
            if variant.is_empty() || variant.starts_with(|c: char| c.is_ascii_digit()) {
                variant.insert_str(0, "Domain");
            }
            if variant == "Self" {
                variant.insert_str(0, "Domain");
            }
            if let Some(other) = presentations.insert(variant.clone(), identity.into()) {
                return Err(format!(
                    "domain identities {other} and {identity} have the same Rust presentation {variant}"
                ));
            }
            variants.insert(identity.to_owned(), variant);
        }
        Ok(Self(variants))
    }
    fn variant(&self, identity: &str) -> Result<String> {
        self.0
            .get(identity)
            .map(|variant| format!("DomainIdentity::{variant}"))
            .ok_or_else(|| format!("{identity} is not a declared domain"))
    }
    /// `None` for the empty domain of a nullary instance.
    fn optional(&self, v: &Value) -> Result<String> {
        let identity = string(v)?;
        if identity.is_empty() {
            Ok("None".into())
        } else {
            Ok(format!("Some({})", self.variant(identity)?))
        }
    }
    fn reference(&self, v: &Value) -> Result<String> {
        self.variant(string(v)?)
    }

    /// The identity enumeration in declared order.
    pub(super) fn enumeration(&self, v: &Value) -> Result<String> {
        let mut names = Vec::new();
        for row in list(&v["domains"])? {
            let identity = string(&row["identity"])?;
            names.push((identity, self.0[identity].as_str()));
        }
        let variants = names
            .iter()
            .map(|(_, variant)| format!("{variant},"))
            .collect::<String>();
        let all = names
            .iter()
            .map(|(_, variant)| format!("Self::{variant},"))
            .collect::<String>();
        let name = names
            .iter()
            .map(|(identity, variant)| format!("Self::{variant} => {identity:?},"))
            .collect::<String>();
        let parse = names
            .iter()
            .map(|(identity, variant)| format!("{identity:?} => Some(Self::{variant}),"))
            .collect::<String>();
        Ok(format!(
            "/// The installed nominal domains. A variant name is presentation only:\n\
             /// the canonical identity is `name()`, and no position is an identity.\n\
             #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]\n\
             pub enum DomainIdentity {{ {variants} }}\n\
             impl DomainIdentity {{\n\
             /// Every installed domain, in declared order.\n\
             pub const ALL: &'static [Self] = &[{all}];\n\
             pub const fn name(self) -> &'static str {{ match self {{ {name} }} }}\n\
             /// The exact declared identity; no other spelling parses.\n\
             pub fn parse(name: &str) -> Option<Self> {{ match name {{ {parse} _ => None, }} }}\n\
             }}\n"
        ))
    }

    /// The logical installed-instance fields of `CATALOG`.
    pub(super) fn logical(&self, v: &Value) -> Result<Vec<(&'static str, String)>> {
        Ok(vec![
            ("domains", array(&v["domains"], |row| self.domain(row))?),
            (
                "logical_types",
                array(&v["logicalTypes"], |row| self.instance(row))?,
            ),
            ("frame_tags", array(&v["frameTags"], frame_tag)?),
            ("codecs", array(&v["codecs"], |row| self.codec(row))?),
            (
                "aggregate_frames",
                array(&v["aggregateFrames"], |row| {
                    Ok(record(
                        "AggregateFrame",
                        &[
                            ("constructor", quoted(&row["constructor"])?),
                            ("domain", self.optional(&row["domain"])?),
                            ("tag", count(&row["tag"])?),
                        ],
                    ))
                })?,
            ),
            (
                "random_services",
                array(&v["randomServices"], |row| {
                    Ok(record(
                        "RandomService",
                        &[
                            ("contract", quoted(&row["contract"])?),
                            ("field", self.reference(&row["field"])?),
                        ],
                    ))
                })?,
            ),
            ("limits", array(&v["limits"], limit)?),
            (
                "finite_definitions",
                array(&v["finiteDefinitions"], finite_definition)?,
            ),
            (
                "domain_constructors",
                array(&v["domainConstructors"], |row| {
                    Ok(record(
                        "DomainConstructor",
                        &[
                            ("identity", quoted(&row["identity"])?),
                            (
                                "kind",
                                format!("DomainConstructorKind::{}", string(&row["kind"])?),
                            ),
                            ("axis", count(&row["axis"])?),
                        ],
                    ))
                })?,
            ),
        ])
    }

    fn domain(&self, row: &Value) -> Result<String> {
        let members = array(&row["members"], |pair| {
            let [member, identity] = list(pair)? else {
                return Err("expected a [member, identity] pair".into());
            };
            Ok(format!(
                "({}, {})",
                quoted(member)?,
                self.reference(identity)?
            ))
        })?;
        let facts = match string(&row["sort"])? {
            "Field" => format!("DomainFacts::Field({})", field(&row["field"])?),
            "Transcript" => format!(
                "DomainFacts::Transcript({})",
                transcript(&row["transcript"])?
            ),
            "Commitment" => format!(
                "DomainFacts::Commitment({})",
                commitment(&row["commitment"])?
            ),
            _ => "DomainFacts::None".into(),
        };
        Ok(record(
            "InstalledDomain",
            &[
                ("identity", self.reference(&row["identity"])?),
                ("sort", quoted(&row["sort"])?),
                ("members", members),
                ("capabilities", array(&row["capabilities"], quoted)?),
                ("facts", facts),
            ],
        ))
    }

    fn instance(&self, row: &Value) -> Result<String> {
        Ok(record(
            "LogicalTypeInstance",
            &[
                ("kind", quoted(&row["kind"])?),
                ("domain", self.optional(&row["domain"])?),
            ],
        ))
    }

    fn codec(&self, row: &Value) -> Result<String> {
        let frame = &row["frame"];
        let frame = if frame.is_null() {
            "None".into()
        } else {
            let field = |name: &str| -> Result<String> {
                Ok(match frame.get(name) {
                    Some(value) => format!("Some({})", count(value)?),
                    None => "None".into(),
                })
            };
            format!(
                "Some({})",
                record(
                    "CodecFrame",
                    &[
                        ("tag", count(&frame["tag"])?),
                        ("element_bytes", field("elementBytes")?),
                        ("bytes", field("bytes")?),
                        ("bytes_per_arity", field("bytesPerArity")?),
                    ],
                )
            )
        };
        Ok(record(
            "Codec",
            &[
                ("identity", quoted(&row["identity"])?),
                ("kind", quoted(&row["kind"])?),
                ("domain", self.optional(&row["domain"])?),
                ("frame", frame),
            ],
        ))
    }

    /// The physical tables, emitted as the separate `INSTALLATION` static.
    pub(super) fn installation(&self, v: &Value) -> Result<String> {
        let fields = [
            (
                "representations",
                array(&v["representations"], |row| {
                    let layout = string(&row["layout"])?;
                    Ok(record(
                        "Representation",
                        &[
                            ("identity", quoted(&row["identity"])?),
                            ("kind", quoted(&row["kind"])?),
                            ("domain", self.optional(&row["domain"])?),
                            ("default", flag(&row["default"])?),
                            (
                                "layout",
                                if layout.is_empty() {
                                    "None".into()
                                } else {
                                    format!("Some({layout:?})")
                                },
                            ),
                            ("frame", value_frame(&row["frame"])?),
                            ("unit", unit(&row["unit"])?),
                        ],
                    ))
                })?,
            ),
            (
                "applied_representations",
                array(&v["appliedRepresentations"], |row| self.applied(row))?,
            ),
            (
                "providers",
                array(&v["providers"], |row| {
                    Ok(record(
                        "ProviderPreference",
                        &[
                            ("domain", self.reference(&row["domain"])?),
                            ("default", provider(&row["default"])?),
                            ("alternatives", array(&row["alternatives"], provider)?),
                        ],
                    ))
                })?,
            ),
            (
                "provider_units",
                array(&v["providerUnits"], |row| {
                    Ok(record(
                        "ProviderUnit",
                        &[
                            ("provider", provider(&row["provider"])?),
                            ("unit", unit(&row["unit"])?),
                        ],
                    ))
                })?,
            ),
            (
                "field_forms",
                array(&v["fieldForms"], |row| self.field_form(row))?,
            ),
            (
                "physical_arguments",
                array(&v["physicalArguments"], |row| {
                    Ok(record(
                        "PhysicalArguments",
                        &[("operation", quoted(&row["operation"])?)],
                    ))
                })?,
            ),
        ];
        Ok(format!(
            "/// The available physical choices; actual target support is admitted separately.\n\
             pub static INSTALLATION: Installation = {};\n",
            record("Installation", &fields)
        ))
    }

    fn applied(&self, row: &Value) -> Result<String> {
        let arguments = array(&row["arguments"], |pattern| {
            let items = list(pattern)?;
            match string(&items[0])? {
                "any" => Ok("ArgumentPattern::Any".into()),
                "domain" => Ok(format!(
                    "ArgumentPattern::Domain({})",
                    self.reference(&items[2])?
                )),
                "type" => {
                    let tree = list(&items[1])?;
                    let domain = match list(&tree[2])? {
                        [] => "None".into(),
                        [argument] => format!("Some({})", self.reference(&list(argument)?[2])?),
                        _ => return Err("type pattern is not a logical type instance".into()),
                    };
                    Ok(format!(
                        "ArgumentPattern::Type(LogicalTypeInstance {{ kind: {}, domain: {domain} }})",
                        quoted(&tree[1])?
                    ))
                }
                _ => Ok(format!(
                    "ArgumentPattern::Naturals {{ minimum: {}, maximum: {} }}",
                    string(&items[1])?,
                    string(&items[2])?
                )),
            }
        })?;
        let representation_key = |value: &Value| -> Result<String> {
            if value.is_null() {
                return Ok("None".into());
            }
            Ok(format!(
                "Some({})",
                record(
                    "RepresentationReference",
                    &[
                        ("kind", quoted(&value["kind"])?),
                        ("domain", self.optional(&value["domain"])?),
                        ("representation", quoted(&value["representation"])?),
                    ],
                )
            ))
        };
        let provider = &row["provider"];
        let provider = if provider.is_null() {
            "None".into()
        } else {
            format!("Some({})", self::provider(provider)?)
        };
        Ok(record(
            "AppliedRepresentation",
            &[
                ("constructor", quoted(&row["constructor"])?),
                ("arguments", arguments),
                ("identity", quoted(&row["identity"])?),
                ("default", flag(&row["default"])?),
                ("child", representation_key(&row["child"])?),
                ("frame", value_frame(&row["frame"])?),
                ("provider", provider),
                ("unit", unit(&row["unit"])?),
                ("vector_port", representation_key(&row["vectorPort"])?),
            ],
        ))
    }

    fn field_form(&self, row: &Value) -> Result<String> {
        let arithmetic = &row["arithmetic"];
        let arithmetic = if arithmetic.is_null() {
            "None".into()
        } else {
            format!(
                "Some(ResidueArithmetic {{ representation: {} }})",
                quoted(&arithmetic["representation"])?
            )
        };
        let montgomery = &row["montgomery"];
        let montgomery = if montgomery.is_null() {
            "None".into()
        } else {
            format!(
                "Some(MontgomeryForm {{ word_bytes: {}, radix_bits: {} }})",
                count(&montgomery["wordBytes"])?,
                count(&montgomery["radixBits"])?
            )
        };
        let encoding = &row["byteEncoding"];
        let encoding = if encoding.is_null() {
            "None".into()
        } else {
            choice(&encoding["order"], &["littleEndian"])?;
            format!(
                "Some(ByteEncoding {{ codec: {}, order: ByteOrder::LittleEndian }})",
                quoted(&encoding["codec"])?
            )
        };
        Ok(record(
            "FieldForm",
            &[
                ("field", self.reference(&row["field"])?),
                ("arithmetic", arithmetic),
                ("montgomery", montgomery),
                ("byte_encoding", encoding),
            ],
        ))
    }
}

fn field(v: &Value) -> Result<String> {
    let shape = &v["structure"];
    let structure = if string(&shape["kind"])? == "prime" {
        "FieldStructure::Prime".into()
    } else {
        let reduction = array(&shape["reduction"], |term| {
            let [exponent, coefficient] = list(term)? else {
                return Err("expected an [exponent, coefficient] term".into());
            };
            Ok(format!("({}, {})", count(exponent)?, quoted(coefficient)?))
        })?;
        format!(
            "FieldStructure::Extension {{ over: ExtensionBase::{}, degree: {}, reduction: {reduction} }}",
            choice(&shape["over"], &["BaseField", "PrimeSubfield"])?,
            count(&shape["degree"])?
        )
    };
    let two_adic = &v["twoAdic"];
    let two_adic = if two_adic.is_null() {
        "None".into()
    } else {
        choice(&two_adic["ordering"], &["powers"])?;
        format!(
            "Some({})",
            record(
                "TwoAdicConvention",
                &[
                    ("convention", quoted(&two_adic["convention"])?),
                    ("maximal_root", quoted(&two_adic["maximalRoot"])?),
                    ("two_adicity", count(&two_adic["twoAdicity"])?),
                ],
            )
        )
    };
    Ok(record(
        "FieldFacts",
        &[
            ("characteristic", quoted(&v["characteristic"])?),
            ("structure", structure),
            ("two_adic", two_adic),
        ],
    ))
}

fn transcript(v: &Value) -> Result<String> {
    let family = match string(&v["family"])? {
        "merlin3" => "Merlin3",
        "spongefish0.8.0" => "Spongefish080",
        _ => "HashChain",
    };
    let hash = if v["hash"].is_null() {
        "None"
    } else {
        "Some(ByteHash::Keccak256)"
    };
    let decoder = match string(&v["decoder"])? {
        "fr64be" => "Fr64Be",
        "rejection31le" => "Rejection31Le",
        "rejection64le" => "Rejection64Le",
        _ => "Scalar64Le",
    };
    Ok(format!(
        "TranscriptFacts {{ family: TranscriptFamily::{family}, hash: {hash}, decoder: ChallengeDecoder::{decoder}, binds_suite: {} }}",
        boolean(&v["bindsSuite"])?
    ))
}

fn commitment(v: &Value) -> Result<String> {
    Ok(match string(&v["scheme"])? {
        "keccak256Rows" => format!(
            "CommitmentFacts::Keccak256Rows {{ digest_bytes: {} }}",
            count(&v["digestBytes"])?
        ),
        "poseidon2Rows" => format!(
            "CommitmentFacts::Poseidon2Rows {{ permutation: {}, digest_bytes: {}, digest_word_bytes: {} }}",
            quoted(&v["permutation"])?,
            count(&v["digestBytes"])?,
            count(&v["digestWordBytes"])?
        ),
        _ => "CommitmentFacts::MultilinearKzg".into(),
    })
}

fn scheme(v: &Value) -> Result<String> {
    Ok(format!(
        "CommitmentScheme::{}",
        match string(v)? {
            "keccak256Rows" => "Keccak256Rows",
            "poseidon2Rows" => "Poseidon2Rows",
            _ => "MultilinearKzg",
        }
    ))
}

fn frame_tag(row: &Value) -> Result<String> {
    let shared = &row["shared"];
    let shared = if shared.is_null() {
        "None".into()
    } else {
        object(shared, &["kind", "scheme"], &[])?;
        format!(
            "Some(SharedFrame {{ kind: {}, scheme: {} }})",
            quoted(&shared["kind"])?,
            scheme(&shared["scheme"])?
        )
    };
    Ok(record(
        "FrameTag",
        &[
            ("tag", count(&row["tag"])?),
            (
                "layout",
                format!("FrameLayout::{}", string(&row["layout"])?),
            ),
            ("shared", shared),
        ],
    ))
}

fn limit(row: &Value) -> Result<String> {
    let value = row["value"]
        .as_u64()
        .ok_or("limit value must be a JSON integer")?;
    let capitalized = |v: &Value| -> Result<String> {
        let text = string(v)?;
        let mut chars = text.chars();
        Ok(chars
            .next()
            .map(|first| first.to_ascii_uppercase().to_string() + chars.as_str())
            .unwrap_or_default())
    };
    Ok(record(
        "Limit",
        &[
            ("name", quoted(&row["name"])?),
            ("value", value.to_string()),
            ("unit", format!("LimitUnit::{}", capitalized(&row["unit"])?)),
            ("owner", quoted(&row["owner"])?),
            ("scope", quoted(&row["scope"])?),
            (
                "phase",
                format!("LimitPhase::{}", capitalized(&row["phase"])?),
            ),
        ],
    ))
}

fn finite_definition(row: &Value) -> Result<String> {
    let collection = &row["collection"];
    Ok(record(
        "FiniteDefinition",
        &[
            ("identity", quoted(&row["identity"])?),
            (
                "mode",
                match string(&row["mode"])? {
                    "math" => "FiniteMode::Math".into(),
                    _ => "FiniteMode::Local".into(),
                },
            ),
            (
                "operation",
                match string(&row["operation"])? {
                    "fold" => "FiniteOperation::Fold".into(),
                    _ => "FiniteOperation::Collect".into(),
                },
            ),
            (
                "collection",
                if collection.is_null() {
                    "None".into()
                } else {
                    format!("Some({})", quoted(collection)?)
                },
            ),
            ("filtered", flag(&row["filtered"])?),
        ],
    ))
}

fn value_frame(v: &Value) -> Result<String> {
    Ok(match choice(v, &["canonical", "local"])? {
        "canonical" => "ValueFrame::Canonical".into(),
        _ => "ValueFrame::Local".into(),
    })
}

fn provider(v: &Value) -> Result<String> {
    Ok(format!(
        "Provider::{}",
        match string(v)? {
            "arkworks" => "Arkworks",
            "blst" => "Blst",
            "dalek" => "Dalek",
            "halo2curves-axiom" => "Halo2curvesAxiom",
            "plonky3" => "Plonky3",
            "spongefish" => "Spongefish",
            other => return Err(format!("unknown provider {other}")),
        }
    ))
}

fn unit(v: &Value) -> Result<String> {
    Ok(format!(
        "InstallationUnit::{}",
        match string(v)? {
            "arkworks" => "Arkworks",
            "blst" => "Blst",
            "dalek" => "Dalek",
            "halo2curves" => "Halo2curves",
            "plonky3" => "Plonky3",
            "independent" => "Independent",
            other => return Err(format!("unknown installation unit {other}")),
        }
    ))
}
