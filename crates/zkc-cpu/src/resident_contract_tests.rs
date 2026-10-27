//! Independent witnesses for the resident installation boundary. Neither the
//! expected catalog nor actual Native shapes supply this oracle's port lists.
//! See docs/spec/runtime/{vm,numerical}.md and docs/spec/domains/vectors.md.
use crate::{CpuBackend, Domain, EntryPolicy, Policy, Value, cpu_contracts};
use serde_json::json;
use std::collections::BTreeSet;
use zkc_runtime::vm::{
    AttributeRule, Backend, BoundSignature, Contracts, ErrorCode, ExecutionPolicy, Frame,
    FrameExit, ImplementationId, ImplementationRequirements, InstalledOperation, Invocation,
    OperationBinding, OperationSignature, PhysicalType, Program, TimingRequirement,
};

const UNSPECIFIED: ImplementationRequirements = ImplementationRequirements {
    timing: TimingRequirement::Unspecified,
    timing_operands: &[],
};
const MSM: ImplementationRequirements = ImplementationRequirements {
    timing: TimingRequirement::VariableTime,
    timing_operands: &[0, 1],
};

#[derive(Clone, Copy)]
enum Port {
    Field,
    Vector,
    Group,
    Groups,
    G1Vector,
    G2Vector,
    Bool,
    Index,
}

struct Fixture {
    contract: &'static str,
    inputs: &'static [Port],
    outputs: &'static [Port],
    attributes: AttributeRule,
    requirements: ImplementationRequirements,
}
const fn fixture(
    contract: &'static str,
    inputs: &'static [Port],
    outputs: &'static [Port],
    attributes: AttributeRule,
) -> Fixture {
    Fixture {
        contract,
        inputs,
        outputs,
        attributes,
        requirements: UNSPECIFIED,
    }
}

// All ordered ports are written here, including control ports and both split
// results. These rows must remain independent of all production family tables.
const COMMON: &[Fixture] = {
    use AttributeRule::{NaturalIndex, None};
    use Port::*;
    &[
        fixture("field.from_index", &[Index], &[Field], None),
        fixture("field.add", &[Field, Field], &[Field], None),
        fixture("field.sub", &[Field, Field], &[Field], None),
        fixture("field.neg", &[Field], &[Field], None),
        fixture("field.mul", &[Field, Field], &[Field], None),
        fixture("field.inverse", &[Field], &[Field], None),
        fixture("field.equal", &[Field, Field], &[Bool], None),
        fixture("vector.empty", &[], &[Vector], None),
        fixture("vector.splat", &[Field], &[Vector], NaturalIndex),
        fixture("vector.append", &[Vector, Field], &[Vector], None),
        fixture("vector.at", &[Vector], &[Field], NaturalIndex),
        fixture("vector.get", &[Vector, Index], &[Field], None),
        fixture("vector.length", &[Vector], &[Index], None),
        fixture("vector.length_check", &[Vector], &[Bool], NaturalIndex),
        fixture("vector.add", &[Vector, Vector], &[Vector], None),
        fixture("vector.sub", &[Vector, Vector], &[Vector], None),
        fixture("vector.mul", &[Vector, Vector], &[Vector], None),
        fixture("vector.dot", &[Vector, Vector], &[Field], None),
        fixture("vector.scale", &[Vector, Field], &[Vector], None),
        fixture("vector.sum", &[Vector], &[Field], None),
        fixture("vector.product", &[Vector], &[Field], None),
        fixture("vector.split", &[Vector], &[Vector, Vector], None),
        fixture("vector.concat", &[Vector, Vector], &[Vector], None),
        fixture("vector.slice", &[Vector, Index, Index], &[Vector], None),
        fixture("vector.equal", &[Vector, Vector], &[Bool], None),
    ]
};
const BLST_VECTOR: &[Fixture] = {
    use AttributeRule::{MatrixShape, NaturalIndex, NaturalIndices, None, ScatterShape};
    use Port::*;
    &[
        fixture("vector.transpose", &[Vector, Index, Index], &[Vector], None),
        fixture("vector.find_last", &[Vector, Field], &[Index], None),
        fixture("vector.rotate", &[Vector, Index], &[Vector], None),
        fixture("vector.bit_reverse", &[Vector], &[Vector], None),
        fixture("vector.bit_reverse_rows", &[Vector, Index], &[Vector], None),
        fixture("vector.interleave", &[Vector, Vector], &[Vector], None),
        fixture("vector.prefix_product", &[Vector], &[Vector], None),
        fixture("vector.prefix_sum", &[Vector], &[Vector], None),
        fixture("vector.inverse", &[Vector], &[Vector], None),
        fixture("vector.fill", &[Field, Index], &[Vector], None),
        fixture("vector.geometric", &[Field, Index], &[Vector], None),
        fixture("vector.scatter_sum", &[Vector], &[Vector], ScatterShape),
        fixture("vector.powers", &[Field], &[Vector], NaturalIndex),
        fixture("vector.gather", &[Vector], &[Vector], NaturalIndices),
        fixture("vector.kronecker", &[Vector, Vector], &[Vector], None),
        fixture("vector.matvec", &[Vector, Vector], &[Vector], MatrixShape),
    ]
};
const CURVE: &[Fixture] = {
    use AttributeRule::{NaturalIndex, None};
    use Port::*;
    &[
        fixture("curve.generator", &[], &[Group], None),
        fixture("curve.identity", &[], &[Group], None),
        fixture("curve.add", &[Group, Group], &[Group], None),
        fixture("curve.neg", &[Group], &[Group], None),
        fixture("curve.equal", &[Group, Group], &[Bool], None),
        fixture("curve.nonidentity", &[Group], &[Bool], None),
        fixture("curve.scale", &[Group, Field], &[Group], None),
        fixture("curve.empty", &[], &[Groups], None),
        fixture("curve.append", &[Groups, Group], &[Groups], None),
        fixture("curve.at", &[Groups], &[Group], NaturalIndex),
        fixture("curve.get", &[Groups, Index], &[Group], None),
        fixture("curve.length", &[Groups], &[Index], None),
        fixture("curve.vector_add", &[Groups, Groups], &[Groups], None),
        fixture("curve.scale_each", &[Vector, Groups], &[Groups], None),
        fixture("curve.vector_scale", &[Groups, Field], &[Groups], None),
        fixture("curve.split", &[Groups], &[Groups, Groups], None),
        fixture("curve.concat", &[Groups, Groups], &[Groups], None),
        Fixture {
            requirements: MSM,
            ..fixture("curve.msm", &[Vector, Groups], &[Group], None)
        },
    ]
};

struct Provider {
    name: &'static str,
    field: &'static str,
    field_layout: &'static str,
    groups: [&'static str; 2],
    group_layouts: [&'static str; 2],
    default_layouts: [&'static str; 6],
    literals: [Fixture; 2],
    extra_vectors: &'static [Fixture],
}
const PROVIDERS: &[Provider] = &[
    Provider {
        name: "blst",
        field: "bls12-381.fr",
        field_layout: "blst/fr",
        groups: ["bls12-381.g1", "bls12-381.g2"],
        group_layouts: ["blst/g1", "blst/g2"],
        default_layouts: [
            "arkworks.fr/0",
            "arkworks.fr-vector/0",
            "arkworks.g1/0",
            "arkworks.g1-vector/0",
            "arkworks.bls12-381-g2/0",
            "arkworks.bls12-381-g2-vector/0",
        ],
        literals: [
            fixture(
                "field.constant",
                &[],
                &[Port::Field],
                AttributeRule::FieldDecimal,
            ),
            fixture(
                "vector.constant",
                &[],
                &[Port::Vector],
                AttributeRule::FieldDecimals,
            ),
        ],
        extra_vectors: BLST_VECTOR,
    },
    Provider {
        name: "halo2curves-axiom",
        field: "bn254.fr",
        field_layout: "halo2curves-axiom/bn254.fr",
        groups: ["bn254.g1", "bn254.g2"],
        group_layouts: ["halo2curves-axiom/bn254.g1", "halo2curves-axiom/bn254.g2"],
        default_layouts: [
            "arkworks.bn254-fr/0",
            "arkworks.bn254-fr-vector/0",
            "arkworks.bn254-g1/0",
            "arkworks.bn254-g1-vector/0",
            "arkworks.bn254-g2/0",
            "arkworks.bn254-g2-vector/0",
        ],
        literals: [
            fixture(
                "field.constant",
                &[],
                &[Port::Field],
                AttributeRule::Bn254Decimal,
            ),
            fixture(
                "vector.constant",
                &[],
                &[Port::Vector],
                AttributeRule::Bn254Decimals,
            ),
        ],
        extra_vectors: &[],
    },
];
impl Provider {
    fn port(&self, port: Port, group: usize, contracts: &Contracts) -> PhysicalType {
        let spelling = match port {
            Port::Field => format!("field:{}@{}", self.field, self.field_layout),
            Port::Vector => format!("vector:{}@{}", self.field, self.field_layout),
            Port::Group => format!("group:{}@{}", self.groups[group], self.group_layouts[group]),
            Port::Groups => format!(
                "groups:{}@{}",
                self.groups[group], self.group_layouts[group]
            ),
            Port::G1Vector => format!("groups:{}@{}", self.groups[0], self.group_layouts[0]),
            Port::G2Vector => format!("groups:{}@{}", self.groups[1], self.group_layouts[1]),
            Port::Bool => "bool@native.bool/0".into(),
            Port::Index => "index@native.index/0".into(),
        };
        // Parsing retrieves scoped IDs only; the spelling and shape are ours.
        let physical = contracts.physical_type(&spelling).unwrap();
        assert_eq!(physical.spelling(), spelling);
        physical
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Facts {
    signature: BoundSignature,
    requirements: ImplementationRequirements,
}
impl Facts {
    fn actual(operation: &impl InstalledOperation) -> Self {
        Self {
            signature: operation.signature().clone(),
            requirements: operation.requirements(),
        }
    }
}
struct Case {
    declaration: OperationBinding,
    facts: Facts,
}
impl Case {
    fn resident(provider: &Provider, row: &Fixture, group: usize, contracts: &Contracts) -> Self {
        Self {
            declaration: OperationBinding {
                contract: row.contract.into(),
                arguments: vec![if row.contract.starts_with("curve.") {
                    provider.groups[group].into()
                } else {
                    provider.field.into()
                }],
                implementation: format!("{}/resident/{}", provider.name, row.contract),
                physical_arguments: vec![],
            },
            facts: Facts {
                signature: OperationSignature {
                    inputs: row
                        .inputs
                        .iter()
                        .map(|&p| provider.port(p, group, contracts))
                        .collect(),
                    outputs: row
                        .outputs
                        .iter()
                        .map(|&p| provider.port(p, group, contracts))
                        .collect(),
                    attributes: row.attributes,
                },
                requirements: row.requirements,
            },
        }
    }
}

fn cases(contracts: &Contracts) -> Vec<Case> {
    let pairing = fixture(
        "pairing.check",
        &[Port::G1Vector, Port::G2Vector],
        &[Port::Bool],
        AttributeRule::None,
    );
    let mut cases = Vec::new();
    for provider in PROVIDERS {
        for row in provider
            .literals
            .iter()
            .chain(COMMON)
            .chain(provider.extra_vectors)
            .chain([&pairing])
        {
            cases.push(Case::resident(provider, row, 0, contracts));
        }
        for group in 0..2 {
            for row in CURVE {
                cases.push(Case::resident(provider, row, group, contracts));
            }
        }
        // Six leaf layouts per provider, in each explicit bridge direction.
        for (index, (port, group)) in [
            (Port::Field, 0),
            (Port::Vector, 0),
            (Port::Group, 0),
            (Port::Groups, 0),
            (Port::Group, 1),
            (Port::Groups, 1),
        ]
        .into_iter()
        .enumerate()
        {
            let resident = provider.port(port, group, contracts);
            let default = contracts
                .physical_type(&format!(
                    "{}@{}",
                    resident.logical().spelling(),
                    provider.default_layouts[index]
                ))
                .unwrap();
            for (source, target) in [(&default, &resident), (&resident, &default)] {
                cases.push(Case {
                    declaration: OperationBinding {
                        contract: "representation.convert".into(),
                        arguments: vec![resident.logical().spelling()],
                        implementation: "native/representation.convert".into(),
                        physical_arguments: vec![source.spelling(), target.spelling()],
                    },
                    facts: Facts {
                        signature: OperationSignature {
                            inputs: vec![source.clone()],
                            outputs: vec![target.clone()],
                            attributes: AttributeRule::None,
                        },
                        requirements: UNSPECIFIED,
                    },
                });
            }
        }
    }
    cases
}

fn backend(contracts: &Contracts) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        Default::default(),
    )
    .unwrap()
    .with_contracts(contracts.clone())
    .unwrap()
}
fn refused(contracts: &Contracts, native: &CpuBackend, declaration: &OperationBinding) {
    assert!(
        contracts.resolve(declaration.clone()).is_err(),
        "expected accepted {declaration:?}"
    );
    assert!(
        native.prepare_binding(declaration).is_none(),
        "actual accepted {declaration:?}"
    );
}

#[test]
fn complete_resident_signatures_and_requirements() {
    let contracts = cpu_contracts().with_policy(ExecutionPolicy::general_purpose());
    let native = backend(&contracts);
    let cases = cases(&contracts);
    let declarations: BTreeSet<_> = cases.iter().map(|c| c.declaration.clone()).collect();
    assert_eq!(declarations.len(), cases.len(), "duplicate fixture");
    let names: BTreeSet<_> = cases
        .iter()
        .map(|c| {
            (
                c.declaration.implementation.clone(),
                c.declaration.contract.clone(),
            )
        })
        .collect();
    for (surface, inventory) in [
        ("actual", native.installed_implementations()),
        ("expected", contracts.installed_implementations()),
    ] {
        let inventory: BTreeSet<_> = inventory
            .into_iter()
            .filter(|(name, contract)| {
                // Aggregate implementation families have length/layout parameters;
                // this suite covers the flat field/vector/curve/pairing inventory.
                !contract.starts_with("field_array.")
                    && !contract.starts_with("fixed_vector.")
                    && (name.starts_with("blst/resident/")
                        || name.starts_with("halo2curves-axiom/resident/")
                        || name == "native/representation.convert")
            })
            .map(|(name, contract)| (name, contract.to_owned()))
            .collect();
        assert!(
            inventory == names,
            "{surface}: missing fixtures {:?}; stale fixtures {:?}",
            inventory.difference(&names).collect::<Vec<_>>(),
            names.difference(&inventory).collect::<Vec<_>>()
        );
    }
    for case in &cases {
        let expected = contracts.resolve(case.declaration.clone()).unwrap();
        let actual = native.prepare_binding(&case.declaration).unwrap();
        assert_eq!(
            Facts {
                signature: expected.signature().clone(),
                requirements: expected.requirements()
            },
            case.facts,
            "expected {:?}",
            case.declaration
        );
        assert_eq!(
            Facts::actual(&actual),
            case.facts,
            "actual {:?}",
            case.declaration
        );
        assert!(expected.implementation_id().is_some());
        assert_eq!(actual.implementation_id(), expected.implementation_id());
    }
    let count = |prefix: &str| {
        cases
            .iter()
            .filter(|c| c.declaration.implementation.starts_with(prefix))
            .count()
    };
    assert_eq!(
        (
            count("blst/resident/"),
            count("halo2curves-axiom/resident/"),
            count("native/representation.convert")
        ),
        (80, 64, 24)
    );
    assert_eq!(names.len(), 109);
    assert_eq!(native.active_frames(), 0);
    eprintln!("checked 168 exact bindings and 109 registrations on both surfaces");
}

#[test]
fn resident_specializations_reject_malformed_and_foreign_declarations() {
    let contracts = cpu_contracts().with_policy(ExecutionPolicy::general_purpose());
    let native = backend(&contracts);
    for case in cases(&contracts)
        .iter()
        .filter(|c| c.declaration.physical_arguments.is_empty())
    {
        for mutation in 0..7 {
            let mut declaration = case.declaration.clone();
            match mutation {
                0 => declaration.arguments.clear(),
                1 => declaration.arguments.push(declaration.arguments[0].clone()),
                2 => {
                    declaration.arguments[0] = match declaration.arguments[0].as_str() {
                        "bls12-381.fr" => "bn254.fr",
                        "bls12-381.g1" => "bn254.g1",
                        "bls12-381.g2" => "bn254.g2",
                        "bn254.fr" => "bls12-381.fr",
                        "bn254.g1" => "bls12-381.g1",
                        "bn254.g2" => "bls12-381.g2",
                        _ => unreachable!(),
                    }
                    .into()
                }
                3 => declaration.arguments[0] = "bn254.gt".into(),
                4 => declaration.implementation.push_str("/unknown"),
                5 => declaration.contract = "field.from_index".into(),
                6 => declaration
                    .physical_arguments
                    .push("index@native.index/0".into()),
                _ => unreachable!(),
            }
            // Keep the contract/implementation mismatch mutation nontrivial.
            if declaration == case.declaration {
                declaration.contract = "field.add".into();
            }
            refused(&contracts, &native, &declaration);
        }
    }
    for provider in PROVIDERS {
        for contract in [
            "pairing.apply",
            "poly.boundary",
            "matrix.mul_vector",
            "vector.embed",
            "curve.response",
        ] {
            let row = fixture(contract, &[], &[], AttributeRule::None);
            refused(
                &contracts,
                &native,
                &Case::resident(provider, &row, 0, &contracts).declaration,
            );
        }
    }
}

#[test]
fn conversions_require_exact_distinct_matching_endpoints() {
    let contracts = cpu_contracts().with_policy(ExecutionPolicy::general_purpose());
    let native = backend(&contracts);
    for case in cases(&contracts)
        .iter()
        .filter(|c| c.declaration.contract == "representation.convert")
    {
        for mutation in 0..6 {
            let mut declaration = case.declaration.clone();
            match mutation {
                0 => declaration.physical_arguments[1] = declaration.physical_arguments[0].clone(),
                1 => declaration.physical_arguments[0] = declaration.physical_arguments[1].clone(),
                2 => {
                    declaration.physical_arguments.pop();
                }
                3 => declaration
                    .physical_arguments
                    .push(declaration.physical_arguments[0].clone()),
                4 => declaration.arguments[0] = "field:bn254.fr".into(),
                5 => declaration.physical_arguments[1] = "bool@native.bool/0".into(),
                _ => unreachable!(),
            }
            if declaration == case.declaration {
                declaration.arguments[0] = "field:bls12-381.fr".into();
            }
            refused(&contracts, &native, &declaration);
        }
    }
}

#[test]
fn timing_policy_and_grants_preserve_exact_msm_requirements() {
    let cases = cases(cpu_contracts());
    for (policy, permit_unspecified, permit_msm) in [
        (cpu_contracts().policy(), true, false),
        (ExecutionPolicy::operand_independent(), false, false),
        (
            ExecutionPolicy {
                allow_unspecified_timing: false,
                allow_variable_time: true,
            },
            false,
            true,
        ),
    ] {
        let contracts = cpu_contracts().with_policy(policy);
        let native = backend(&contracts);
        for case in &cases {
            let allowed = if case.facts.requirements == MSM {
                permit_msm
            } else {
                permit_unspecified
            };
            assert_eq!(
                contracts.resolve(case.declaration.clone()).is_ok(),
                allowed,
                "expected {:?}",
                case.declaration
            );
            assert_eq!(
                native.prepare_binding(&case.declaration).is_some(),
                allowed,
                "actual {:?}",
                case.declaration
            );
        }
    }
    let msm: Vec<_> = cases
        .iter()
        .filter(|c| c.facts.requirements == MSM)
        .collect();
    assert_eq!(msm.len(), 4);
    for granted in &msm {
        let contracts = cpu_contracts()
            .with_timing_grant(granted.declaration.clone(), MSM)
            .unwrap();
        let native = backend(&contracts);
        for case in &msm {
            let allowed = case.declaration == granted.declaration;
            assert_eq!(contracts.resolve(case.declaration.clone()).is_ok(), allowed);
            assert_eq!(native.prepare_binding(&case.declaration).is_some(), allowed);
        }
        for wrong in [
            UNSPECIFIED,
            ImplementationRequirements {
                timing: TimingRequirement::OperandIndependent,
                timing_operands: &[],
            },
            ImplementationRequirements {
                timing_operands: &[0],
                ..MSM
            },
            ImplementationRequirements {
                timing_operands: &[1],
                ..MSM
            },
            ImplementationRequirements {
                timing_operands: &[1, 0],
                ..MSM
            },
            ImplementationRequirements {
                timing_operands: &[0, 2],
                ..MSM
            },
        ] {
            assert!(
                cpu_contracts()
                    .with_timing_grant(granted.declaration.clone(), wrong)
                    .is_err()
            );
        }
    }
}

// Report a modified copy of actual Native installation facts. None of these
// controls executes a handler, enters a frame, or changes production registries.
struct Report {
    facts: Facts,
    id: Option<ImplementationId>,
}
impl InstalledOperation for Report {
    fn signature(&self) -> &BoundSignature {
        &self.facts.signature
    }
    fn requirements(&self) -> ImplementationRequirements {
        self.facts.requirements
    }
    fn implementation_id(&self) -> Option<ImplementationId> {
        self.id
    }
}
struct ReportBackend<'a> {
    native: &'a CpuBackend,
    facts: Facts,
}
impl Backend for ReportBackend<'_> {
    type Value = Value;
    type Operation = Report;
    type Call = ();
    type Checkpoint = ();
    fn prepare_binding(&self, declaration: &OperationBinding) -> Option<Report> {
        let actual = self.native.prepare_binding(declaration)?;
        Some(Report {
            facts: self.facts.clone(),
            id: actual.implementation_id(),
        })
    }
    fn validate_value(&self, _: &Value) -> crate::Result<()> {
        panic!("preflight must be read-only")
    }
    fn enter_frame(&mut self, _: &Frame, _: &[Value]) -> crate::Result<()> {
        panic!("preflight must be read-only")
    }
    fn leave_frame(&mut self, _: &Frame, _: FrameExit, _: &[Value]) -> crate::Result<()> {
        panic!("preflight must be read-only")
    }
    fn apply(&mut self, _: &Report, _: &Invocation<'_>, _: &[Value]) -> crate::Result<Vec<Value>> {
        panic!("preflight must be read-only")
    }
}
fn binding_program(case: &Case, contracts: &Contracts) -> Program {
    let declaration = &case.declaration;
    let signature = &case.facts.signature;
    let inputs: Vec<_> = signature
        .inputs
        .iter()
        .enumerate()
        .map(|(index, ty)| json!([format!("a{index}"), ty.spelling()]))
        .collect();
    let names: Vec<_> = (0..inputs.len()).map(|index| format!("a{index}")).collect();
    let outputs: Vec<_> = signature
        .outputs
        .iter()
        .map(PhysicalType::spelling)
        .collect();
    let returns: Vec<_> = (0..outputs.len())
        .map(|index| format!("r{index}"))
        .collect();
    let attributes: &[&str] = match signature.attributes {
        AttributeRule::None => &[],
        AttributeRule::FieldDecimal | AttributeRule::Bn254Decimal => &["1"],
        AttributeRule::FieldDecimals | AttributeRule::Bn254Decimals => &["1", "2"],
        AttributeRule::NaturalIndex | AttributeRule::NaturalIndices => &["0"],
        AttributeRule::ScatterShape => &["1", "0"],
        AttributeRule::MatrixShape => &["0", "0", "0"],
        _ => panic!("missing independently authored attribute witness"),
    };
    // Ports come from the fixture. A real call site keeps the binding in the
    // executable; the preflight remains read-only and executes no arithmetic.
    let bytes = serde_json::to_vec(&json!([
        "zkc.program/0",
        [[
            "b",
            declaration.contract,
            declaration.arguments,
            declaration.implementation,
            declaration.physical_arguments
        ]],
        [[
            "function",
            "f",
            inputs,
            outputs,
            [
                ["op", "site", "b", attributes, names, returns],
                ["return", returns]
            ],
            ["f", []]
        ]],
        [[
            "participant",
            "actor",
            "root",
            "P",
            inputs,
            outputs,
            [["local", "work", "f", names, returns], ["return", returns]],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap();
    Program::decode(&bytes, contracts).unwrap()
}

#[test]
fn independent_fixtures_and_runtime_linking_detect_mutated_reports() {
    let contracts = cpu_contracts().with_policy(ExecutionPolicy::general_purpose());
    let native = backend(&contracts);
    let mut mutation_count = 0;
    for case in cases(&contracts) {
        let program = binding_program(&case, &contracts);
        let actual = native.prepare_binding(&case.declaration).unwrap();
        let mut reported = ReportBackend {
            native: &native,
            facts: Facts::actual(&actual),
        };
        assert_eq!(reported.facts, case.facts);
        program.check_installation(&reported).unwrap();
        let mut mutations = Vec::new();
        for (output, ports) in [
            (false, &case.facts.signature.inputs),
            (true, &case.facts.signature.outputs),
        ] {
            for (index, port) in ports.iter().enumerate() {
                let mut wrong = case.facts.clone();
                let mut replacement = PhysicalType::default_for(port.logical().clone()).unwrap();
                if replacement == *port {
                    replacement = contracts
                        .physical_type(if port.kind() == zkc_runtime::vm::Type::Bool {
                            "index@native.index/0"
                        } else {
                            "bool@native.bool/0"
                        })
                        .unwrap();
                }
                let ports = if output {
                    &mut wrong.signature.outputs
                } else {
                    &mut wrong.signature.inputs
                };
                ports[index] = replacement;
                mutations.push((
                    format!("{} port {index}", if output { "output" } else { "input" }),
                    wrong,
                ));
            }
        }
        for output in [false, true] {
            let mut wrong = case.facts.clone();
            let ports = if output {
                &mut wrong.signature.outputs
            } else {
                &mut wrong.signature.inputs
            };
            if ports.is_empty() {
                ports.push(contracts.physical_type("bool@native.bool/0").unwrap());
            } else {
                ports.pop();
            }
            mutations.push((
                format!("{} arity", if output { "output" } else { "input" }),
                wrong,
            ));
        }
        if case.facts.signature.inputs.len() >= 2
            && case.facts.signature.inputs[0] != case.facts.signature.inputs[1]
        {
            let mut wrong = case.facts.clone();
            wrong.signature.inputs.swap(0, 1);
            mutations.push(("input order".into(), wrong));
        }
        let mut wrong = case.facts.clone();
        wrong.signature.attributes = if wrong.signature.attributes == AttributeRule::None {
            AttributeRule::NaturalIndex
        } else {
            AttributeRule::None
        };
        mutations.push(("attributes".into(), wrong));
        let mut wrong = case.facts.clone();
        wrong.requirements.timing = TimingRequirement::OperandIndependent;
        wrong.requirements.timing_operands = &[];
        mutations.push(("timing class".into(), wrong));
        let mut wrong = case.facts.clone();
        wrong.requirements.timing_operands = if wrong.requirements == MSM {
            &[0]
        } else {
            &[0, 1]
        };
        mutations.push(("timing operands".into(), wrong));
        for (label, wrong) in mutations {
            // Equal changes in expected and actual resolvers would still fail
            // this independent oracle; cross-surface agreement cannot hide drift.
            assert_ne!(wrong, case.facts, "ineffective mutation: {label}");
            reported.facts = wrong;
            let error = program
                .check_installation(&reported)
                .expect_err(&format!("accepted {label}: {:?}", case.declaration));
            assert_eq!(
                error.code,
                ErrorCode::Backend,
                "{label}: {:?}",
                case.declaration
            );
            mutation_count += 1;
        }
    }
    eprintln!("rejected {mutation_count} mutated installation reports");
    assert_eq!(native.active_frames(), 0);
}
