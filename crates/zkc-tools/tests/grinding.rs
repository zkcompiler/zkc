//! Search trials and the compiled live transcript have independent budgets.
use zkc_backends::{
    Value,
    choices::Namespace,
    external::{
        grinding::{Candidates, Limits, Progress, Search},
        openvm::{Duplex, Snapshot},
    },
};
use zkc_runtime::interactive::{Action, BackendError, Runner, admit_physical};
use zkc_tools::protocol::ParticipantChecker;

#[path = "common/backend.rs"]
mod fixture;

struct Sequential(u32);
impl Candidates for Sequential {
    fn next(&mut self, namespace: &Namespace) -> Result<u32, BackendError> {
        assert_eq!(
            (namespace.role(), namespace.purpose()),
            ("Worker", "grinding")
        );
        let value = self.0;
        self.0 += 1;
        Ok(value)
    }
}
fn encoded(snapshot: &Snapshot) -> Value {
    let mut data = vec![1_514_881_876, 1, 2];
    data.extend(snapshot.state.map(u64::from));
    data.push(snapshot.absorb_index as u64);
    data.push(snapshot.sample_index as u64);
    Value::Indices(data.into())
}

#[test]
fn searched_witness_commits_once_through_the_compiled_body() {
    let path = zkc_test_support::source("input-families/grinding-commit.pir");
    let source = zkc_test_support::compile("protocol-source", &path);
    let candidate = zkc_test_support::compile("protocol-compile", &path);
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let mut live = Duplex::new();
    live.observe(&[42]).unwrap();
    let before = live.snapshot();
    let mut search = Search::new(
        &live,
        3,
        Namespace::new("Worker", "grinding").unwrap(),
        Sequential(0),
        Limits {
            candidates: 3,
            work: 9,
        },
    )
    .unwrap();
    assert_eq!(search.advance(10), &Progress::Found(2));
    assert_eq!(search.usage().work.units().unwrap(), 9);
    assert_eq!(live.snapshot(), before);

    for (bits, witness, accepted, limit) in [(3, 2, true, 3), (3, 0, false, 3), (0, 0, true, 0)] {
        let backend = fixture::backend_at("Worker", "test", "main").with_external_work_limit(limit);
        let admitted = admit_physical(&source, &candidate, &backend, &checker).unwrap();
        let mut runner = Runner::new(
            &admitted,
            "main",
            "Worker",
            "test",
            backend,
            vec![encoded(&before), Value::Index(bits), Value::Index(witness)],
        )
        .unwrap_or_else(|e| panic!("load: {}", e.error));
        let outputs = loop {
            match runner.poll() {
                Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                Action::Returned(outputs) => break outputs,
                unexpected => panic!("unexpected action: {unexpected:?}"),
            }
        };
        let mut direct = Duplex::from_snapshot(before.clone()).unwrap();
        assert_eq!(
            direct
                .check_witness(bits as u32, witness as u32)
                .unwrap()
                .value,
            accepted
        );
        let [Value::Indices(state), Value::Bool(result)] = outputs.as_slice() else {
            panic!("results")
        };
        let Value::Indices(expected) = encoded(&direct.snapshot()) else {
            unreachable!()
        };
        assert_eq!(state, &expected);
        assert_eq!(*result, accepted);
        assert_eq!(runner.backend().external_work_spent(), limit);
        assert_eq!(runner.backend().active_frames(), 0);
        assert_eq!(search.usage().work.units().unwrap(), 9);
    }
}
