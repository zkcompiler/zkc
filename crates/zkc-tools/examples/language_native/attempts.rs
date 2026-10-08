//! Named Entry decisions delegate retry, provider retention and quotas to the native Host.
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::Value as Native;
use zkc_tools::{
    entry::{
        AttemptOptions, BindingPolicy, DEFAULT_DRAW_BUDGET, NamedValues, Package, ProofEntry,
        ProofOptions, ProofRequest, RoleInputs, RunEntry, RunRequest,
    },
    run::HostLimits,
};
fn package(directory: &Path, entry: &str, suite: usize) -> Package {
    let bytes = std::fs::read(directory.join(format!("attempt-{entry}-{suite}.entry"))).unwrap();
    Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES).unwrap()
}
fn role(producing: bool, done: bool) -> RoleInputs {
    RoleInputs {
        inputs: if producing {
            [("done".into(), Native::Bool(done).into())].into()
        } else {
            NamedValues::new()
        },
        ..Default::default()
    }
}
fn request(producing: bool, done: bool) -> ProofRequest {
    ProofRequest {
        private: role(producing, done),
        ..Default::default()
    }
}
pub(super) fn run(directory: &Path) {
    for (name, suite) in [("Derived", 0), ("Derived", 1), ("Plain", 0)] {
        let options = ProofOptions {
            binding: BindingPolicy::AllowHeaderOnly,
            ..Default::default()
        };
        let publication = package(directory, name, suite);
        let prover = ProofEntry::admit(publication.clone(), options, Default::default()).unwrap();
        let verifier = ProofEntry::admit(publication.clone(), options, Default::default()).unwrap();
        let retry = AttemptOptions {
            count: 3,
            ..Default::default()
        };
        let produced = prover.prove_attempts(request(true, true), retry).unwrap();
        assert!(produced.is_success(), "{:?}", produced.native.outcome);
        assert_eq!(produced.native.attempts.len(), 1);
        assert_eq!(produced.native.attempts[0].decision, Ok(true));
        assert!(produced.outputs.as_ref().unwrap().contains_key("result"));
        let proof = produced.native.outcome.unwrap();
        assert!(
            verifier
                .verify(request(false, true), &proof)
                .unwrap()
                .is_success()
        );

        // One-shot proving never publishes a result the Entry marks incomplete.
        let single = prover.prove(request(true, false)).unwrap();
        assert!(!single.is_success());
        assert_eq!(
            single.native.outcome.as_ref().unwrap_err(),
            "native-attempt-limit"
        );
        assert!(single.outputs.is_none());
        assert_eq!(single.native.attempts.len(), 1);
        let exhausted = prover.prove_attempts(request(true, false), retry).unwrap();
        assert_eq!(
            exhausted.native.outcome.err().unwrap().to_string(),
            "native-attempt-limit"
        );
        assert!(exhausted.outputs.is_none());
        assert_eq!(exhausted.native.attempts.len(), 3);
        assert!(
            exhausted
                .native
                .attempts
                .iter()
                .all(|a| a.decision == Ok(false))
        );
        assert!(exhausted.native.cleanup_errors.is_empty());
        let per_attempt = exhausted.native.attempts[0].usage.instructions;
        let mut cumulative_options = options;
        cumulative_options.capacity.work.instructions = 2 * per_attempt + per_attempt / 2;
        let cumulative =
            ProofEntry::admit(publication.clone(), cumulative_options, Default::default()).unwrap();
        let stopped = cumulative
            .prove_attempts(request(true, false), retry)
            .unwrap();
        assert_eq!(stopped.native.attempts.len(), 3);
        assert_eq!(stopped.native.attempts[0].decision, Ok(false));
        assert_eq!(stopped.native.attempts[1].decision, Ok(false));
        assert!(
            stopped.native.attempts[2].decision.is_err(),
            "{:?}",
            stopped.native.outcome
        );
        assert_ne!(
            stopped.native.outcome.as_ref().unwrap_err(),
            "native-attempt-limit"
        );
        assert_eq!(exhausted.native.resources.len(), 1);
        let state = &exhausted.native.resources[0];
        assert_eq!(state["state"]["transitions"], 3);
        assert_eq!(state["leased"], false);
        assert_eq!(state["poisoned"], false);
        if name == "Derived" {
            for attempt in &exhausted.native.attempts {
                assert_eq!(
                    attempt.transcript.as_ref().unwrap()["budget"]
                        .as_u64()
                        .unwrap()
                        + attempt.transcript.as_ref().unwrap()["transitions"]
                            .as_u64()
                            .unwrap(),
                    DEFAULT_DRAW_BUDGET
                );
            }
        }
        let mut zero = request(true, true);
        zero.private.services.insert("coins".into(), 0);
        let stopped = prover.prove_attempts(zero, retry).unwrap();
        assert!(!stopped.is_success());
        assert_eq!(stopped.native.attempts.len(), 1);
        assert_eq!(
            stopped.native.attempts[0].decision.as_ref().unwrap_err(),
            "exhausted:resource-budget"
        );
        let mut limited = request(true, false);
        limited.private.services.insert("coins".into(), 1);
        let stopped = prover.prove_attempts(limited, retry).unwrap();
        assert_eq!(stopped.native.attempts.len(), 2);
        assert_eq!(stopped.native.attempts[0].decision, Ok(false));
        assert!(stopped.native.attempts[1].decision.is_err());
        // Native transitions include the failed draw; its allowance stays exhausted.
        assert_eq!(stopped.native.resources[0]["state"]["transitions"], 2);
        assert_eq!(stopped.native.resources[0]["state"]["budget"], 0);
        assert_eq!(
            stopped.native.attempts[1].decision.as_ref().unwrap_err(),
            "exhausted:resource-budget"
        );
        let mut unknown = request(true, true);
        unknown.private.services.insert("absent".into(), 1);
        assert_eq!(
            prover.prove(unknown).err().unwrap().to_string(),
            "entry-service-names"
        );
        if name == "Derived" {
            let mut derived = request(true, true);
            derived.private.services.insert("challenges".into(), 1);
            assert_eq!(
                prover.prove(derived).err().unwrap().to_string(),
                "entry-service-names"
            );
        }
        for count in [0, 1025] {
            assert_eq!(
                prover
                    .prove_attempts(request(true, true), AttemptOptions { count, ..retry })
                    .err()
                    .unwrap()
                    .to_string(),
                "native-attempt-limits"
            );
        }
        let stopped = prover
            .prove_attempts(
                request(true, true),
                AttemptOptions {
                    proof_bytes: 0,
                    ..retry
                },
            )
            .unwrap();
        assert!(!stopped.is_success());
        assert_eq!(stopped.native.outcome.as_ref().unwrap_err(), "proof-limit");
        let mut small = options;
        small.capacity.work.instructions = 0;
        let limited = ProofEntry::admit(publication, small, Default::default()).unwrap();
        assert!(
            !limited
                .prove_attempts(request(true, true), retry)
                .unwrap()
                .is_success()
        );
        let mut transcript = request(true, true);
        transcript.transcript_budget = Some(0);
        let result = prover.prove(transcript).unwrap();
        assert_eq!(result.is_success(), name == "Plain");
        if name == "Plain" {
            let mut transcript = request(true, true);
            transcript.transcript_budget = Some(1);
            assert_eq!(
                prover.prove(transcript).err().unwrap().to_string(),
                "native-proof-unselected-transcript"
            );
        }
    }
    let options = ProofOptions {
        binding: BindingPolicy::AllowHeaderOnly,
        ..Default::default()
    };
    let once =
        ProofEntry::admit(package(directory, "Once", 0), options, Default::default()).unwrap();
    assert_eq!(
        once.prove_attempts(request(true, true), Default::default())
            .err()
            .unwrap()
            .to_string(),
        "entry-attempt-completion"
    );

    let host = RunEntry::admit(
        package(directory, "Run", 0),
        HostLimits::default(),
        Default::default(),
    )
    .unwrap();
    let run_request = || RunRequest {
        session: "named_budgets".into(),
        roles: [
            ("P".into(), role(true, true)),
            ("V".into(), role(false, true)),
        ]
        .into(),
        setups: BTreeMap::new(),
    };
    let completed = host.prepare(run_request()).unwrap().execute();
    assert!(completed.outputs.is_some());
    assert!(completed.native.cleanup_errors.is_empty());
    let mut zero = run_request();
    zero.roles
        .get_mut("V")
        .unwrap()
        .services
        .insert("challenges".into(), 0);
    let stopped = host.prepare(zero).unwrap().execute();
    assert!(stopped.outputs.is_none());
}
