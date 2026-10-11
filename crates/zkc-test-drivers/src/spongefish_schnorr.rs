//! Independent interoperability oracle using Spongefish 0.7.4's public API.
//! Schnorr equations and call order follow its `examples/schnorr.rs`:
//! https://github.com/arkworks-rs/spongefish/blob/ef9741346a150039427d9e0c02d6b2d73e93ec81/spongefish/examples/schnorr.rs
//! This driver imports no zkc compiler, codec, transcript or backend code.
use ark_bls12_381::{Fr, G1Projective as G};
use ark_ec::PrimeGroup;
use ark_ff::UniformRand;
use serde_json::json;
use spongefish::{Encoding, VerificationError, VerifierState};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn verify(mut state: VerifierState, base: G, point: G) -> bool {
    let check = || -> Result<(), VerificationError> {
        let commitment = state.prover_message::<G>()?;
        let challenge = state.verifier_message::<Fr>();
        let response = state.prover_message::<Fr>()?;
        if base * response != commitment + point * challenge {
            return Err(VerificationError);
        }
        state.check_eof()
    };
    check().is_ok()
}
fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(args.len(), 2, "export DIRECTORY | verify FILE");
    let base = G::generator();
    let scalar = Fr::from(7u64);
    let point = base * scalar;
    let instance = [base, point];
    let domain =
        spongefish::domain_separator!("schnorr proof"; "spongefish examples").instance(&instance);
    if args[0] == "verify" {
        let proof = std::fs::read(&args[1]).unwrap();
        println!(
            "{}",
            json!({"accepted": verify(domain.std_verifier(&proof), base, point)})
        );
        return;
    }
    assert_eq!(args[0], "export");
    let directory = std::path::Path::new(&args[1]);
    std::fs::create_dir_all(directory).unwrap();
    let mut vectors = Vec::new();
    for fixed in [false, true] {
        let mut state = domain.std_prover();
        let nonce = if fixed {
            Fr::from(11u64)
        } else {
            Fr::rand(state.rng())
        };
        let commitment = base * nonce;
        state.prover_message(&commitment);
        let challenge = state.verifier_message::<Fr>();
        let response = nonce + challenge * scalar;
        state.prover_message(&response);
        let proof = state.narg_string().to_vec();
        assert!(verify(domain.std_verifier(&proof), base, point));
        // Pins absorb-after-squeeze against the actual upstream implementation.
        let after_response = state.verifier_message::<Fr>();
        let file = if fixed { "fixed.bin" } else { "reference.bin" };
        std::fs::write(directory.join(file), &proof).unwrap();
        vectors.push(
            json!({"file":file,"challenge":hex(challenge.encode().as_ref()),
            "after_response":hex(after_response.encode().as_ref()),"bytes":proof.len()}),
        );
    }
    let public = json!({"tag":b"schnorr proof".to_vec(),"session":b"spongefish examples".to_vec(),
        "base":{"bytes":hex(base.encode().as_ref())},"point":{"bytes":hex(point.encode().as_ref())}});
    std::fs::write(
        directory.join("public.json"),
        serde_json::to_vec(&public).unwrap(),
    )
    .unwrap();
    std::fs::write(
        directory.join("witness.json"),
        br#"{"scalar":"7","nonce":"11"}"#,
    )
    .unwrap();
    println!("{}", json!({"vectors":vectors}));
}
