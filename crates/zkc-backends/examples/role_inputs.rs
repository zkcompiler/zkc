//! Small runnable host input boundary; not a complete protocol CLI.
use std::sync::Arc;
use zkc_backends::{
    Domain, EntryPolicy, InputBindings, Keys, NativeBackend, Policy, PublicInputs, Value,
};
use zkc_runtime::interactive::{Action, Runner, admit_supplied};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let policy = Policy::default();
    // Development-only setup. A production application must establish its setup
    // provenance and authenticate the verifier fingerprint independently.
    let keys = Keys::setup_for_development(1, &policy.ark_bounds())?;
    let domain = Domain::new("P", "demo-session", "main", Some("demo"));
    let mut backend = NativeBackend::new(
        policy,
        EntryPolicy::new(domain.clone(), Some(1), PublicInputs::LocalOnly),
        None,
    )?;
    let mut host = InputBindings::new();
    host.insert(
        "prover-key",
        Value::ProverKey(Arc::new(keys.prover_key().clone())),
    )?;
    host.insert("challenge-source", backend.issue_rng(domain, 1)?)?;
    let artifact = br#"["zkc.participants/1",[["commit","pcs.commit",["multilinear.kzg.bls12-381/1"],"arkworks/pcs.commit"],["draw","random.draw",["bls12-381.fr"],"arkworks/random.draw"]],"physical",
      [["function","commit_one",[["pk","prover_key:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1"],["t","table:bls12-381.fr@arkworks.mle-lsb/1"],["rng","rng:bls12-381.fr@host.resource/1"]],["commitment:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1","opening_state:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1","field:bls12-381.fr@arkworks.fr/1","rng:bls12-381.fr@host.resource/1"],
        [["op","commit","commit",[],["pk","t"],["C","state"]],
         ["op","draw","draw",[],["rng"],["r","next"]],
         ["return",["C","state","r","next"]]], ["commit_one",[]]]],
      [["participant","prover","demo","P",[["n","1"]],[["pk","prover_key:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1"],["t","table:bls12-381.fr@arkworks.mle-lsb/1"],["rng","rng:bls12-381.fr@host.resource/1"]],["commitment:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1","opening_state:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1","field:bls12-381.fr@arkworks.fr/1","rng:bls12-381.fr@host.resource/1"],
        [["local","local_commit","commit_one",["pk","t","rng"],["C","state","r","next"]],["return",["C","state","r","next"]]]]],
      [["entry","main",[["P","prover"]]]]]"#;
    let admitted = admit_supplied(artifact, &backend)?;
    let role = admitted.entry("main").ok_or("entry")?.remove(0);
    let json = br#"["zkc.inputs/1",[
      ["pk",["host","prover-key"]],
      ["t",["table",["2","3"]]],
      ["rng",["host","challenge-source"]]
    ]]"#;
    let inputs = backend.inputs_from_json(&role, json, &host)?;
    let mut runner = Runner::new(&admitted, "main", "P", "demo-session", backend, inputs)
        .map_err(|e| e.error)?;
    loop {
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut)?,
            Action::Returned(values) => {
                if let Value::OpeningState(state) = &values[1] {
                    println!(
                        "private opening state arity: {}",
                        state.commitment().metadata().arity()
                    );
                }
                println!(
                    "public commitment bytes: {}",
                    runner.backend().encode_value(&values[0])?.len()
                );
                if let Value::Rng(token) = &values[3] {
                    println!("resource state: {:?}", runner.backend().observe(token)?);
                }
                return Ok(());
            }
            Action::Stopped(stop) => return Err(format!("local stop: {:?}", stop.kind).into()),
            _ => return Err("unexpected transport action".into()),
        }
    }
}
