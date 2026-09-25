//! Admission for protocols that already exchange a one-way proof.
//!
//! This checks executable shape, not cryptographic soundness. It introduces no
//! transcript, verifier randomness, or source-correspondence assertion. The
//! caller still selects and authenticates the statement and prepared public
//! parameters. Compiler correspondence is retained from the input `Admitted`.

use super::{Admitted, EntryRole, Type, model::*};
use std::collections::BTreeSet;

/// A checked pair of independently executable proof endpoints.
#[derive(Clone, Debug)]
pub struct NoninteractiveEntry {
    admitted: Admitted,
    entry: String,
    producer: EntryRole,
    verifier: EntryRole,
    acceptance: usize,
}

/// Reasons that an admitted participant graph is not a public one-way proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoninteractiveError {
    Entry,
    Roles,
    Acceptance,
    Communication,
    VerifierResource,
    Incomplete,
}
impl std::fmt::Display for NoninteractiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Entry => "noninteractive-entry",
            Self::Roles => "noninteractive-roles",
            Self::Acceptance => "noninteractive-acceptance",
            Self::Communication => "noninteractive-communication",
            Self::VerifierResource => "noninteractive-verifier-resource",
            Self::Incomplete => "noninteractive-incomplete",
        })
    }
}
impl std::error::Error for NoninteractiveError {}

impl NoninteractiveEntry {
    /// Check the actual, already-admitted participant graph, including callees
    /// and nonzero loops. Verifier inputs and intermediate values must have
    /// public value representations. This deliberately excludes secret-key or
    /// interactive verification profiles, which need a different contract.
    pub fn new(
        admitted: Admitted,
        entry: &str,
        producer: &str,
        verifier: &str,
        acceptance: usize,
    ) -> Result<Self, NoninteractiveError> {
        check(&admitted.program, entry, producer, verifier, acceptance)?;
        let roles = admitted.entry(entry).ok_or(NoninteractiveError::Entry)?;
        let find = |role: &str| {
            roles
                .iter()
                .find(|endpoint| endpoint.role == role)
                .cloned()
                .ok_or(NoninteractiveError::Roles)
        };
        Ok(Self {
            producer: find(producer)?,
            verifier: find(verifier)?,
            admitted,
            entry: entry.to_owned(),
            acceptance,
        })
    }

    pub fn admitted(&self) -> &Admitted {
        &self.admitted
    }
    pub fn entry(&self) -> &str {
        &self.entry
    }
    pub fn producer(&self) -> &EntryRole {
        &self.producer
    }
    pub fn verifier(&self) -> &EntryRole {
        &self.verifier
    }
    pub fn acceptance(&self) -> usize {
        self.acceptance
    }
}

fn check(
    program: &Program,
    entry: &str,
    producer: &str,
    verifier: &str,
    acceptance: usize,
) -> Result<(), NoninteractiveError> {
    use NoninteractiveError as E;
    let roots = program.entries.get(entry).ok_or(E::Entry)?;
    if producer == verifier
        || roots.len() != 2
        || !roots.contains_key(producer)
        || !roots.contains_key(verifier)
    {
        return Err(E::Roles);
    }
    let verification = &program.participants[&roots[verifier]];
    if verification
        .outputs
        .get(acceptance)
        .is_none_or(|ty| ty.kind() != Type::Bool)
    {
        return Err(E::Acceptance);
    }
    let mut pending = roots.values().collect::<Vec<_>>();
    let mut visited = BTreeSet::new();
    while let Some(symbol) = pending.pop() {
        if !visited.insert(symbol) {
            continue;
        }
        let participant = &program.participants[symbol];
        let verifying = participant.role == verifier;
        if !verifying && participant.role != producer {
            return Err(E::Roles);
        }
        if verifying
            && (participant.inputs.iter().any(|(_, t)| !t.is_serializable())
                || participant.outputs.iter().any(|t| !t.is_serializable()))
        {
            return Err(E::VerifierResource);
        }
        let mut bodies = vec![participant.body.as_ref()];
        while let Some(body) = bodies.pop() {
            for instruction in body {
                match instruction {
                    Instruction::Send { peer, .. } => {
                        if verifying || peer != verifier {
                            return Err(E::Communication);
                        }
                    }
                    Instruction::Receive { peer, .. } => {
                        if !verifying || peer != producer {
                            return Err(E::Communication);
                        }
                    }
                    Instruction::Local { function, .. } if verifying => {
                        let function = &program.functions[function];
                        if function.inputs.iter().any(|(_, t)| !t.is_serializable())
                            || function.outputs.iter().any(|t| !t.is_serializable())
                        {
                            return Err(E::VerifierResource);
                        }
                        for operation in LocalInstruction::walk(&function.body) {
                            if matches!(
                                operation,
                                LocalInstruction::Variant { .. } | LocalInstruction::Match { .. }
                            ) {
                                return Err(E::VerifierResource);
                            }
                            if let LocalInstruction::Op { binding, .. } = operation {
                                let signature = binding.signature();
                                if signature
                                    .inputs
                                    .iter()
                                    .chain(&signature.outputs)
                                    .any(|t| !t.is_serializable())
                                {
                                    return Err(E::VerifierResource);
                                }
                            }
                        }
                    }
                    Instruction::Call { participant, .. } => pending.push(participant),
                    Instruction::Loop { count, body, .. } if count.may_run() => bodies.push(body),
                    Instruction::Incomplete { .. } => return Err(E::Incomplete),
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interactive::{ArtifactFormat, LogicalType, PhysicalType};
    use std::{collections::BTreeMap, sync::Arc};

    fn ty(name: &str) -> PhysicalType {
        PhysicalType::default_for(LogicalType::parse(name).unwrap())
    }

    fn participant(role: &str, body: Vec<Instruction>) -> Arc<Participant> {
        Arc::new(Participant {
            symbol: role.into(),
            instance: "root".into(),
            role: role.into(),
            parameters: BTreeMap::new(),
            families: BTreeMap::new(),
            inputs: vec![],
            outputs: if role == "Verifier" {
                vec![ty("bool")]
            } else {
                vec![]
            },
            body: body.into(),
        })
    }

    fn program() -> Program {
        Program {
            format: ArtifactFormat::ExplicitBindings,
            functions: BTreeMap::new(),
            participants: BTreeMap::from([
                (
                    "Prover".into(),
                    participant(
                        "Prover",
                        vec![Instruction::Send {
                            site: "proof".into(),
                            schema: "proof".into(),
                            peer: "Verifier".into(),
                            input: "p".into(),
                        }],
                    ),
                ),
                (
                    "Verifier".into(),
                    participant(
                        "Verifier",
                        vec![Instruction::Receive {
                            site: "proof".into(),
                            schema: "proof".into(),
                            peer: "Prover".into(),
                            output: "p".into(),
                            ty: ty("bool"),
                        }],
                    ),
                ),
            ]),
            entries: BTreeMap::from([(
                "main".into(),
                BTreeMap::from([
                    ("Prover".into(), "Prover".into()),
                    ("Verifier".into(), "Verifier".into()),
                ]),
            )]),
        }
    }

    // These tests target the additional one-way policy on the typed graph.
    // Ordinary source/SSA admission is tested by the existing admission suite.
    #[test]
    fn roles_acceptance_and_direction_are_independent_checks() {
        let mut p = program();
        assert_eq!(check(&p, "main", "Prover", "Verifier", 0), Ok(()));
        assert_eq!(
            check(&p, "absent", "Prover", "Verifier", 0),
            Err(NoninteractiveError::Entry)
        );
        assert_eq!(
            check(&p, "main", "Prover", "Prover", 0),
            Err(NoninteractiveError::Roles)
        );
        assert_eq!(
            check(&p, "main", "Prover", "Verifier", 1),
            Err(NoninteractiveError::Acceptance)
        );
        p.participants.insert(
            "Prover".into(),
            participant(
                "Prover",
                vec![Instruction::Receive {
                    site: "challenge".into(),
                    schema: "challenge".into(),
                    peer: "Verifier".into(),
                    output: "c".into(),
                    ty: ty("bool"),
                }],
            ),
        );
        assert_eq!(
            check(&p, "main", "Prover", "Verifier", 0),
            Err(NoninteractiveError::Communication)
        );
    }

    #[test]
    fn inspects_nested_calls_and_skips_only_fixed_zero_loops() {
        let mut p = program();
        p.participants.insert(
            "child".into(),
            participant(
                "Prover",
                vec![Instruction::Incomplete {
                    site: "unfinished".into(),
                }],
            ),
        );
        let call = || Instruction::Call {
            site: "nested".into(),
            participant: "child".into(),
            inputs: vec![],
            outputs: vec![],
        };
        let body = |count| {
            vec![Instruction::Loop {
                site: "repeat".into(),
                count: Count::Constant(count),
                carried: vec![],
                captures: vec![],
                body: vec![call()].into(),
                outputs: vec![],
            }]
        };
        p.participants
            .insert("Prover".into(), participant("Prover", body(0)));
        assert_eq!(check(&p, "main", "Prover", "Verifier", 0), Ok(()));
        p.participants
            .insert("Prover".into(), participant("Prover", body(1)));
        assert_eq!(
            check(&p, "main", "Prover", "Verifier", 0),
            Err(NoninteractiveError::Incomplete)
        );
    }

    #[test]
    fn verifier_cannot_acquire_private_or_random_resources() {
        // The rule refuses a verifier holding anything it could not have
        // serialized, so both a random resource and a private one are run,
        // and both the way in and the way out: the rule reads the outputs as
        // well as the inputs, and only the input side was ever exercised.
        for spelling in ["rng:bls12-381.fr", "nonce:bls12-381.fr"] {
            for as_output in [false, true] {
                let mut p = program();
                let mut verifier = participant("Verifier", vec![]);
                let held = Arc::get_mut(&mut verifier).unwrap();
                if as_output {
                    held.outputs.push(ty(spelling));
                } else {
                    held.inputs.push(("coins".into(), ty(spelling)));
                }
                p.participants.insert("Verifier".into(), verifier);
                assert_eq!(
                    check(&p, "main", "Prover", "Verifier", 0),
                    Err(NoninteractiveError::VerifierResource),
                    "{spelling} as {}",
                    if as_output { "output" } else { "input" }
                );
            }
        }
    }
    #[test]
    fn verifier_resource_scan_reaches_both_local_branches() {
        use crate::interactive::{LogicalOrigin, OperationBinding, ResolvedBinding};
        // The draw goes in one arm at a time. A scanner that descended into
        // only one of them would pass the case that put it there, so both
        // placements are run and the empty arm is the other one.
        for draw_in_then in [true, false] {
            let arm = |holds_draw: bool| {
                let mut body = Vec::new();
                if holds_draw {
                    body.push(LocalInstruction::Op {
                        site: "draw".into(),
                        binding: Arc::new(
                            ResolvedBinding::explicit(OperationBinding {
                                contract: "random.draw".into(),
                                arguments: vec!["bls12-381.fr".into()],
                                implementation: "arkworks/random.draw".into(),
                            })
                            .unwrap(),
                        ),
                        attributes: vec![],
                        inputs: vec![],
                        outputs: vec![],
                    });
                }
                body.push(LocalInstruction::Yield(vec![]));
                body
            };
            let mut p = program();
            p.functions.insert(
                "f".into(),
                Arc::new(crate::interactive::model::Function {
                    name: "f".into(),
                    inputs: vec![],
                    outputs: vec![],
                    origin: LogicalOrigin {
                        definition: "f".into(),
                        arguments: vec![],
                    },
                    body: vec![
                        LocalInstruction::Conditional {
                            site: "branch".into(),
                            condition: "condition".into(),
                            captures: vec![],
                            outputs: vec![],
                            then_body: arm(draw_in_then).into(),
                            else_body: arm(!draw_in_then).into(),
                        },
                        LocalInstruction::Return(vec![]),
                    ]
                    .into(),
                }),
            );
            p.participants.insert(
                "Verifier".into(),
                participant(
                    "Verifier",
                    vec![Instruction::Local {
                        site: "local".into(),
                        function: "f".into(),
                        inputs: vec![],
                        outputs: vec![],
                    }],
                ),
            );
            // This unit targets the additional profile checker; ordinary SSA
            // admission remains a separate prerequisite of its public constructor.
            assert_eq!(
                check(&p, "main", "Prover", "Verifier", 0),
                Err(NoninteractiveError::VerifierResource),
                "draw in {} arm",
                if draw_in_then { "then" } else { "else" }
            );
        }
    }
    #[test]
    fn verifier_cannot_hide_an_intermediate_variant() {
        let spelling =
            zkc_test_support::variants::logical("Private", serde_json::json!([["zero", []]]));
        let mut p = program();
        p.functions.insert(
            "f".into(),
            Arc::new(Function {
                name: "f".into(),
                inputs: vec![],
                outputs: vec![],
                origin: super::super::LogicalOrigin {
                    definition: "f".into(),
                    arguments: vec![],
                },
                body: vec![
                    LocalInstruction::Variant {
                        site: "pack".into(),
                        ty: ty(&spelling),
                        alternative: "zero".into(),
                        payload: vec![],
                        output: "v".into(),
                    },
                    LocalInstruction::Return(vec![]),
                ]
                .into(),
            }),
        );
        p.participants.insert(
            "Verifier".into(),
            participant(
                "Verifier",
                vec![Instruction::Local {
                    site: "work".into(),
                    function: "f".into(),
                    inputs: vec![],
                    outputs: vec![],
                }],
            ),
        );
        assert_eq!(
            check(&p, "main", "Prover", "Verifier", 0),
            Err(NoninteractiveError::VerifierResource)
        );
    }
}
