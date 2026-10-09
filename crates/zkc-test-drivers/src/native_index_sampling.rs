//! Derived UniformIndex transcripts through the general independent proof host.
//! The replay below calls upstream Merlin directly; it does not use the host's
//! origin, transition or sampler constructors.
#[allow(dead_code)]
#[path = "support/native_transcript.rs"]
mod encoding;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_backends::{KoalaBear, KoalaBearExt8};
use zkc_runtime::logical;
use zkc_test_support::hex;
use zkc_tools::proof::NativeDeployment;

fn index_wire(value: u64) -> Vec<u8> {
    [b"ZKCV\x00\x1f".as_slice(), &value.to_le_bytes()].concat()
}
fn extension_wire(value: KoalaBearExt8) -> Vec<u8> {
    let mut wire = b"ZKCV\x00\x1a".to_vec();
    for x in <KoalaBearExt8 as BasedVectorSpace<KoalaBear>>::as_basis_coefficients_slice(&value) {
        wire.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
    }
    wire
}
fn unhex(text: &str) -> Vec<u8> {
    (0..text.len())
        .step_by(2)
        .map(|n| u8::from_str_radix(&text[n..n + 2], 16).unwrap())
        .collect()
}
fn inputs(envelope: &Json, rounds: u64, producing: bool, transitions: usize) -> Json {
    let wire = hex(&index_wire(rounds));
    let public: Vec<_> = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], wire]))
        .collect();
    let role = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == envelope[2][1][if producing { 2 } else { 3 }])
        .unwrap();
    let data: Vec<_> = role[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], ["wire", wire]]))
        .collect();
    json!([
        "zkc.native-proof-inputs/0",
        public,
        data,
        "",
        [],
        transitions.to_string()
    ])
}
fn run(
    deployment: &NativeDeployment,
    inputs: &Json,
    proof: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    let report = zkc_test_drivers::execute(
        deployment,
        inputs,
        zkc_tools::proof::Invocation::one_shot(proof),
    )?;
    assert!(report.cleanup_errors.is_empty());
    report.outcome
}
fn admit(envelope: &Json) -> Result<NativeDeployment, String> {
    let bytes = serde_json::to_vec(envelope).unwrap();
    NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
}

/// Independent replay of the selected suite's framing. Each origin is the
/// descriptor's template with the loop coordinate substituted.
struct Replay<'a> {
    events: &'a [Json],
    proof: &'a [u8],
    position: usize,
    event: usize,
    transcript: merlin::Transcript,
}
impl<'a> Replay<'a> {
    fn new(envelope: &'a Json, input: &Json, proof: &'a [u8]) -> Self {
        let root = encoding::root(envelope, input);
        assert_eq!(&proof[..8], b"ZKCPRF00");
        assert_eq!(&proof[8..40], &Sha256::digest(&root)[..]);
        let mut transcript = merlin::Transcript::new(b"zkc.artifact/0");
        transcript.append_message(b"binding", &root);
        Self {
            events: envelope[2][3].as_array().unwrap(),
            proof,
            position: 40,
            event: 0,
            transcript,
        }
    }
    fn origin(&mut self, kind: &str, round: u64) -> &'a Json {
        // The descriptor lists each static template once; every round reuses
        // it with that round's coordinate.
        let row = &self.events[self.event % self.events.len()];
        self.event += 1;
        assert_eq!(row[0], kind);
        let mut tree = logical::decode_tree(&unhex(row[1].as_str().unwrap())).unwrap();
        tree[0] = json!("zkc.native-origin/0");
        tree[3] = json!([round.to_string()]);
        self.transcript
            .append_message(b"origin", &encoding::tree(&tree));
        row
    }
    fn observe(&mut self, round: u64, wire: &[u8]) {
        self.origin("message", round);
        self.transcript.append_message(b"value", wire);
    }
    fn receive(&mut self, round: u64) -> &'a [u8] {
        let at = self.position;
        let size = u64::from_le_bytes(self.proof[at..at + 8].try_into().unwrap()) as usize;
        self.position += 8 + size;
        let wire = &self.proof[at + 8..self.position];
        self.observe(round, wire);
        wire
    }
    fn field(&mut self, round: u64) -> KoalaBearExt8 {
        self.origin("query", round);
        let mut coordinates = Vec::new();
        for _ in 0..16 {
            let mut bytes = [0; 64];
            self.transcript.challenge_bytes(b"challenge", &mut bytes);
            for word in bytes.as_chunks::<4>().0 {
                let n = u32::from_le_bytes(*word) % (1 << 31);
                if n < 2_130_706_433 {
                    coordinates.push(KoalaBear::from_u32(n));
                    if coordinates.len() == 8 {
                        return KoalaBearExt8::from(
                            <[KoalaBear; 8]>::try_from(coordinates).unwrap(),
                        );
                    }
                }
            }
        }
        panic!("independent challenge sampler exhausted");
    }
    // UniformIndex(N): the bound is absorbed after the occurrence, then the
    // first eight little-endian bytes of a 64-byte squeeze are masked.
    fn index(&mut self, round: u64, bound: u64) -> u64 {
        let row = self.origin("index", round);
        assert_eq!(row[2], bound.to_string());
        self.transcript
            .append_message(b"bound", &bound.to_le_bytes());
        let mut bytes = [0; 64];
        self.transcript.challenge_bytes(b"index", &mut bytes);
        u64::from_le_bytes(bytes[..8].try_into().unwrap()) % bound
    }
    fn finish(self, rounds: u64) {
        assert_eq!(self.position, self.proof.len());
        assert_eq!(self.event, self.events.len() * rounds as usize);
    }
}

/// Echo rounds: field draw, delivery, index draw, delivery, then both echoes.
fn replay(envelope: &Json, input: &Json, proof: &[u8], rounds: u64, bound: u64) -> Vec<u64> {
    let mut r = Replay::new(envelope, input, proof);
    let mut positions = Vec::new();
    for round in 0..rounds {
        let challenge = r.field(round);
        r.observe(round, &extension_wire(challenge));
        let position = r.index(round, bound);
        assert!(position < bound);
        r.observe(round, &index_wire(position));
        assert_eq!(r.receive(round), extension_wire(challenge));
        assert_eq!(r.receive(round), index_wire(position));
        positions.push(position);
    }
    r.finish(rounds);
    positions
}

fn with_candidate(envelope: &Json, edit: impl FnOnce(&mut Json)) -> Json {
    let mut changed = envelope.clone();
    let mut program: Json = serde_json::from_str(changed[4].as_str().unwrap()).unwrap();
    edit(&mut program);
    let text = program.to_string();
    changed[5] = json!(hex(&Sha256::digest(text.as_bytes())));
    changed[4] = json!(text);
    changed
}
fn with_descriptor(envelope: &Json, edit: impl FnOnce(&mut Vec<Json>)) -> Json {
    let mut changed = envelope.clone();
    edit(changed[2][3].as_array_mut().unwrap());
    changed[3] = json!(hex(&Sha256::digest(
        logical::encode_tree(&changed[2]).unwrap()
    )));
    changed
}
/// Edit the one local operation bound to `contract` in the generated helpers.
fn edit_operation(program: &mut Json, contract: &str, edit: impl FnOnce(&mut Json)) {
    let bindings: Vec<String> = program[1]
        .as_array()
        .unwrap()
        .iter()
        .filter(|b| b[1] == contract)
        .map(|b| b[0].as_str().unwrap().to_owned())
        .collect();
    let mut operations = program[2]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|function| function[4].as_array_mut().unwrap().iter_mut())
        .filter(|op| op[0] == "op" && bindings.iter().any(|b| op[2] == b.as_str()));
    let operation = operations.next().expect("helper operation");
    assert!(operations.next().is_none(), "one helper uses {contract}");
    edit(operation);
}
fn set_index_attribute(program: &mut Json, contract: &str, value: Json) {
    edit_operation(program, contract, |op| op[3] = value);
}

fn check_admission(envelope: &Json) {
    let index_row = envelope[2][3]
        .as_array()
        .unwrap()
        .iter()
        .position(|r| r[0] == "index")
        .unwrap();
    let draw_row = envelope[2][3]
        .as_array()
        .unwrap()
        .iter()
        .position(|r| r[0] == "query")
        .unwrap();
    let cases: Vec<(&str, Json, &str)> = vec![
        // The helper's materialized bound must equal the descriptor event.
        (
            "helper bound differs from descriptor",
            with_candidate(envelope, |p| {
                set_index_attribute(p, "index.constant", json!(["64"]))
            }),
            "native-proof-state-chain",
        ),
        (
            "helper bound is not a power of two",
            with_candidate(envelope, |p| {
                set_index_attribute(p, "index.constant", json!(["3"]))
            }),
            "native-proof-index-bound",
        ),
        (
            "descriptor bound differs from helper",
            with_descriptor(envelope, |e| e[index_row][2] = json!("64")),
            "native-proof-state-chain",
        ),
        (
            "descriptor bound missing",
            with_descriptor(envelope, |e| {
                e[index_row].as_array_mut().unwrap().pop();
            }),
            "artifact-record",
        ),
        (
            "descriptor index read as a field draw",
            with_descriptor(envelope, |e| {
                e[index_row][0] = json!("query");
                e[index_row].as_array_mut().unwrap().pop();
            }),
            "native-proof-query-origin",
        ),
        (
            "descriptor draw read as an index",
            with_descriptor(envelope, |e| {
                e[draw_row][0] = json!("index");
                e[draw_row].as_array_mut().unwrap().push(json!("32"));
            }),
            "native-proof-query-origin",
        ),
        (
            "descriptor events reordered",
            with_descriptor(envelope, |e| e.swap(draw_row, index_row)),
            "native-proof-state-chain",
        ),
    ];
    for (name, changed, expected) in cases {
        assert_eq!(admit(&changed).err().as_deref(), Some(expected), "{name}");
    }
    for bound in [
        "032",
        "0",
        "3",
        "18446744073709551616",
        "9223372036854775809",
    ] {
        let changed = with_descriptor(envelope, |e| e[index_row][2] = json!(bound));
        assert_eq!(
            admit(&changed).err().as_deref(),
            Some("native-proof-index-bound"),
            "descriptor bound {bound}"
        );
    }
    // The transition's origin names the source method. An index transition
    // carrying a draw occurrence is not admitted, and vice versa.
    for (contract, from, to) in [
        ("transcript.native.indexed.index", "index", "draw"),
        ("transcript.native.indexed.challenge", "draw", "index"),
    ] {
        let changed = with_candidate(envelope, |p| {
            edit_operation(p, contract, |op| {
                let mut tree = logical::decode_tree(&unhex(op[3][0].as_str().unwrap())).unwrap();
                assert_eq!(tree[4][5], from);
                tree[4][5] = json!(to);
                op[3] = json!([hex(&logical::encode_tree(&tree).unwrap())]);
            });
        });
        assert_eq!(
            admit(&changed).err().as_deref(),
            Some("Attributes: interactive-kernel-parameters: exact kernel attributes required"),
            "{contract}"
        );
    }
}

fn main() {
    let directory = std::env::args().nth(1).expect("generated directory");
    let directory = Path::new(&directory);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    let cases = manifest.as_array().unwrap();
    let deployments: Vec<(Json, NativeDeployment)> = cases
        .iter()
        .map(|case| {
            let name = case["name"].as_str().unwrap();
            let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
            let envelope: Json = serde_json::from_slice(&bytes).unwrap();
            let deployment =
                NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
                    .unwrap();
            (envelope, deployment)
        })
        .collect();
    let mut first_positions = None;
    for (case, (envelope, deployment)) in cases.iter().zip(&deployments) {
        let bound = case["bound"].as_u64().unwrap();
        let rounds = case["rounds"].as_u64().unwrap();
        // Six ordered transitions per round, including both erased deliveries.
        let transitions = envelope[2][3].as_array().unwrap().len() * rounds as usize;
        let producer = inputs(envelope, rounds, true, transitions);
        let validator = inputs(envelope, rounds, false, transitions);
        let proof = run(deployment, &producer, None).unwrap();
        run(deployment, &validator, Some(&proof)).unwrap();
        let positions = replay(envelope, &producer, &proof, rounds, bound);
        // Lowering options are not part of the binding: every compilation of
        // the same source and policy derives the same transcript.
        assert_eq!(*first_positions.get_or_insert(positions.clone()), positions);
        for (other, other_deployment) in &deployments {
            run(
                other_deployment,
                &inputs(other, rounds, false, transitions),
                Some(&proof),
            )
            .unwrap();
        }
        assert_eq!(
            run(deployment, &producer, None).unwrap(),
            proof,
            "deterministic prover"
        );

        let mut exact = validator.clone();
        exact[5] = json!((transitions - 1).to_string());
        assert_eq!(
            run(deployment, &exact, Some(&proof)).unwrap_err(),
            "exhausted:resource-budget"
        );
        let mut trailing = proof.clone();
        trailing.push(0);
        assert_eq!(
            run(deployment, &validator, Some(&trailing)).unwrap_err(),
            "proof-trailing"
        );
        assert_eq!(
            run(deployment, &validator, Some(&proof[..proof.len() - 1])).unwrap_err(),
            "proof-truncated"
        );
        let mut context = validator.clone();
        context[3] = json!("01");
        assert_eq!(
            run(deployment, &context, Some(&proof)).unwrap_err(),
            "proof-header"
        );
        // Public inputs belong to the binding root, which seeds every index.
        let fewer = inputs(envelope, rounds - 1, false, transitions);
        assert_eq!(
            run(deployment, &fewer, Some(&proof)).unwrap_err(),
            "proof-header"
        );

        // The last frame echoes the final position. A different in-range
        // position is decoded and observed, then V's comparison rejects it.
        let last = proof.len() - 8;
        let mut moved = proof.clone();
        let position = u64::from_le_bytes(moved[last..].try_into().unwrap());
        moved[last..].copy_from_slice(&((position + 1) % bound).to_le_bytes());
        assert_eq!(
            run(deployment, &validator, Some(&moved)).unwrap_err(),
            "artifact-stopped:Explicit(\"reject\")"
        );
        let mut malformed = proof.clone();
        malformed[last - 1] = 0x1a; // A field tag where an index frame is due.
        assert_eq!(
            run(deployment, &validator, Some(&malformed)).unwrap_err(),
            "artifact-stopped:Decode(Header)"
        );

        if case["name"] == "echo" {
            check_admission(envelope);
            std::fs::write(
                directory.join("echo.producer.json"),
                serde_json::to_vec(&producer).unwrap(),
            )
            .unwrap();
            std::fs::write(
                directory.join("echo.validator.json"),
                serde_json::to_vec(&validator).unwrap(),
            )
            .unwrap();
            std::fs::write(directory.join("echo.proof"), &proof).unwrap();
        }
    }
    println!(
        "derived index transcripts accepted and replayed; altered bounds, events and frames refused"
    );
}
