mod support;
use serde_json::json;
use support::{binding_with, decl, program, state};
use zkc_runtime::{
    AdmittedJob, Budget, Error, Outcome, Stop,
    buffer::{BufferStore, BufferUsage, PackedBuffers, SegmentedBuffers},
    table::{Domain, SmallPrimeKernel, TableBindings, TapeProvider},
};

#[test]
fn completed_residual_keeps_original_storage() {
    completed_residual(PackedBuffers::new().unwrap());
    completed_residual(SegmentedBuffers::new().unwrap());
}
fn completed_residual<S: BufferStore<u8>>(store: S) {
    let p = program(
        json!(["apply", ["view", "f7", 1], [0], ["return", 0]]),
        json!([decl("t", json!(["table", "f7", 1]))]),
        json!(["residual", "f7", 1]),
    );
    let job = AdmittedJob::bind(
        p,
        json!([["t", ["table", "f7", 1], [8, [2, 5]]]]),
        binding_with(store),
    )
    .unwrap_or_else(|e| panic!("{}", e.reason));
    let completed = job
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    let Ok(Outcome::Returned(value)) = completed.outcome() else {
        panic!("did not return");
    };
    assert_eq!(
        completed.bindings().value_json(value).unwrap(),
        json!([8, [2, 5], []])
    );
    assert_eq!(
        binding_with(PackedBuffers::new().unwrap()).value_json(value),
        Err(Error("foreign-handle"))
    );
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StorageFault {
    None,
    Reserve,
    Corrupt,
    Overallocate,
    Read,
    WrongLength,
}
struct FaultyStore {
    inner: PackedBuffers<u8>,
    fault: std::rc::Rc<std::cell::Cell<StorageFault>>,
}
impl BufferStore<u8> for FaultyStore {
    type Reference = <PackedBuffers<u8> as BufferStore<u8>>::Reference;
    fn required_bytes(&self, elements: usize, buffers: usize) -> Result<usize, Error> {
        self.inner.required_bytes(elements, buffers)
    }
    fn reserve(&mut self, elements: usize, buffers: usize) -> Result<(), Error> {
        match self.fault.get() {
            StorageFault::Reserve => Err(Error("reservation-failed")),
            StorageFault::Overallocate => self.inner.reserve(elements + 1_000_000, buffers),
            _ => self.inner.reserve(elements, buffers),
        }
    }
    fn publish(&mut self, values: &[u8]) -> Result<Self::Reference, Error> {
        if self.fault.get() == StorageFault::Corrupt && !values.is_empty() {
            let mut bad = values.to_vec();
            bad[0] = (bad[0] + 1) % 7;
            self.inner.publish(&bad)
        } else {
            self.inner.publish(values)
        }
    }
    fn read(&self, reference: &Self::Reference) -> Result<&[u8], Error> {
        if self.fault.get() == StorageFault::Read {
            return Err(Error("store-read-refused"));
        }
        let cells = self.inner.read(reference)?;
        if self.fault.get() == StorageFault::WrongLength && !cells.is_empty() {
            Ok(&cells[..cells.len() - 1])
        } else {
            Ok(cells)
        }
    }
    fn usage(&self) -> BufferUsage {
        self.inner.usage()
    }
}
fn faulty_store() -> (FaultyStore, std::rc::Rc<std::cell::Cell<StorageFault>>) {
    let fault = std::rc::Rc::new(std::cell::Cell::new(StorageFault::None));
    (
        FaultyStore {
            inner: PackedBuffers::new().unwrap(),
            fault: fault.clone(),
        },
        fault,
    )
}
#[test]
fn storage_start_failure_keeps_capture_and_provider_custody() {
    use zkc_runtime::Bindings;
    let (store, fault) = faulty_store();
    let mut bindings = binding_with(store);
    let old = bindings
        .input(
            &zkc_runtime::Sort(json!(["table", "f7", 1])),
            &json!([8, [2, 5]]),
        )
        .unwrap();
    let p = program(
        json!(["apply", ["draw"], [], ["return", 0]]),
        json!([]),
        json!(["scalar", "f7"]),
    );
    let job = AdmittedJob::bind(p, json!([]), bindings).unwrap_or_else(|e| panic!("{}", e.reason));
    fault.set(StorageFault::Reserve);
    let failed = match job.reserve(Budget::default()) {
        Err(e) => e,
        Ok(_) => panic!("faulty reservation started"),
    };
    assert_eq!(failed.reason, Error("reservation-failed"));
    assert_eq!(
        failed.job.bindings().value_json(&old).unwrap(),
        json!([8, [2, 5]])
    );
    assert_eq!(
        failed.job.bindings().state_json(),
        json!([0, 0, 0, [], [3, 6]])
    );
    assert!(failed.job.bindings().events().is_empty());
    fault.set(StorageFault::None);
    let completed = failed
        .job
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert_eq!(
        completed.bindings().value_json(&old).unwrap(),
        json!([8, [2, 5]])
    );
    assert_eq!(completed.bindings().events(), &[json!(["drawn", 3])]);
}
#[test]
fn canonical_payload_corruption_is_not_detected_by_handle_validity() {
    let (store, fault) = faulty_store();
    fault.set(StorageFault::Corrupt);
    let p = program(
        json!([
            "apply",
            ["view", "f7", 0],
            [0],
            ["apply", ["evaluate", "f7", 0], [0, 2], ["return", 0]]
        ]),
        json!([
            decl("t", json!(["table", "f7", 0])),
            decl("q", json!(["point", "f7"]))
        ]),
        json!(["scalar", "f7"]),
    );
    let completed = AdmittedJob::bind(
        p,
        json!([
            ["t", ["table", "f7", 0], [8, [2]]],
            ["q", ["point", "f7"], []]
        ]),
        binding_with(store),
    )
    .unwrap_or_else(|e| panic!("{}", e.reason))
    .reserve(Budget::default())
    .unwrap_or_else(|e| panic!("{}", e.reason))
    .execute();
    let Ok(Outcome::Returned(value)) = completed.outcome() else {
        panic!("did not return")
    };
    // Correct logical evaluation is 2. All handles and field encodings are
    // valid, so only adapter correspondence/testing exposes this defect.
    assert_eq!(completed.bindings().value_json(value).unwrap(), json!(3));
}
#[test]
fn actual_storage_capacity_is_checked_before_execution() {
    let (store, fault) = faulty_store();
    fault.set(StorageFault::Overallocate);
    let p = program(
        json!(["apply", ["draw"], [], ["return", 0]]),
        json!([]),
        json!(["scalar", "f7"]),
    );
    let job = AdmittedJob::bind(p, json!([]), binding_with(store))
        .unwrap_or_else(|e| panic!("{}", e.reason));
    let failed = match job.reserve(Budget {
        bytes: 100_000,
        ..Budget::default()
    }) {
        Err(e) => e,
        Ok(_) => panic!("excess backing capacity admitted"),
    };
    assert_eq!(failed.reason, Error("capacity-limit"));
    assert_eq!(
        failed.job.bindings().state_json(),
        json!([0, 0, 0, [], [3, 6]])
    );
    assert!(failed.job.bindings().events().is_empty());
}
#[test]
fn shape_metadata_precedes_buffer_access_and_checks_returned_lengths() {
    use zkc_runtime::{
        Bindings, Resources, Sort,
        table::{Operation, Value},
    };
    let (store, fault) = faulty_store();
    let mut b = binding_with(store);
    let r = b
        .input(
            &Sort(json!(["residual", "f7", 1])),
            &json!([8, [2, 5], [0]]),
        )
        .unwrap();
    let q = b.input(&Sort(json!(["point", "f7"])), &json!([1])).unwrap();
    let empty = b.input(&Sort(json!(["point", "f7"])), &json!([])).unwrap();
    b.reserve(
        Resources {
            scratch: 2,
            ..Resources::default()
        },
        &Budget::default(),
    )
    .unwrap();
    fault.set(StorageFault::Read);
    assert!(b.bound(&q).is_ok());
    assert!(matches!(
        b.invoke(
            &Operation::Restrict(Domain::Seven, 1u8.into()),
            &[r.clone(), Value::Scalar(Domain::Seven, 2)]
        ),
        Ok(Outcome::Stopped(Stop::Refused))
    ));
    assert!(matches!(
        b.invoke(
            &Operation::Evaluate(Domain::Seven, 1u8.into()),
            &[r.clone(), q]
        ),
        Ok(Outcome::Stopped(Stop::Refused))
    ));
    assert!(matches!(
        b.invoke(
            &Operation::Evaluate(Domain::Seven, 1u8.into()),
            &[r.clone(), empty.clone()]
        ),
        Err(Error("store-read-refused"))
    ));
    fault.set(StorageFault::WrongLength);
    assert!(matches!(
        b.invoke(&Operation::Evaluate(Domain::Seven, 1u8.into()), &[r, empty]),
        Err(Error("buffer-contract-violation"))
    ));
    assert_eq!(b.state_json(), json!([0, 0, 0, [], [3, 6]]));
    assert!(b.events().is_empty());
}

#[test]
fn restriction_at_the_profile_rank_limit_preserves_earlier_views() {
    use zkc_runtime::{
        Bindings, Resources, Sort,
        table::{Operation, Value},
    };
    fn check<S: BufferStore<u8>>(store: S) {
        let mut b = binding_with(store);
        let cells = vec![0; 4096];
        let old = b
            .input(
                &Sort(json!(["residual", "f7", 12])),
                &json!([8, cells, vec![0; 11]]),
            )
            .unwrap();
        b.reserve(
            Resources {
                bytes: 12,
                values: 1,
                ..Resources::default()
            },
            &Budget::default(),
        )
        .unwrap();
        let op = Operation::Restrict(Domain::Seven, 12u8.into());
        let Ok(Outcome::Returned(new)) =
            b.invoke(&op, &[old.clone(), Value::Scalar(Domain::Seven, 3)])
        else {
            panic!("restriction failed")
        };
        assert_eq!(b.value_json(&old).unwrap()[2], json!(vec![0; 11]));
        let mut prefix = vec![0; 11];
        prefix.push(3);
        assert_eq!(b.value_json(&new).unwrap()[2], json!(prefix));
        assert!(matches!(
            b.invoke(&op, &[new, Value::Scalar(Domain::Seven, 1)]),
            Ok(Outcome::Stopped(Stop::Refused))
        ));
    }
    check(PackedBuffers::new().unwrap());
    check(SegmentedBuffers::new().unwrap());
}

#[test]
fn reentry_capacity_is_layout_dependent_with_custody_preserved() {
    fn count<S: BufferStore<u8>>(name: &str, store: S) -> usize {
        let p = program(
            json!([
                "apply",
                ["draw"],
                [],
                ["apply", ["point"], [0], ["return", 0]]
            ]),
            json!([]),
            json!(["point", "f7"]),
        );
        let mut b = TableBindings::with_storage(
            SmallPrimeKernel,
            TapeProvider::new(vec![3; 256]).unwrap(),
            state(),
            store,
        )
        .unwrap();
        let mut old = None;
        let budget = Budget {
            bytes: 4096,
            ..Budget::default()
        };
        for completed_count in 0..256 {
            let before_state = b.state_json();
            let before_events = b.events().to_vec();
            let job = AdmittedJob::bind(p.clone(), json!([]), b)
                .unwrap_or_else(|e| panic!("{}", e.reason));
            match job.reserve(budget) {
                Ok(session) => {
                    let c = session.execute();
                    let Ok(Outcome::Returned(value)) = c.outcome() else {
                        panic!("failed execution")
                    };
                    if old.is_none() {
                        old = Some(value.clone());
                    }
                    assert_eq!(
                        c.bindings().value_json(old.as_ref().unwrap()).unwrap(),
                        json!([3])
                    );
                    b = c.into_parts().1;
                }
                Err(failed) => {
                    assert_eq!(failed.reason, Error("capacity-limit"));
                    assert_eq!(failed.job.bindings().state_json(), before_state);
                    assert_eq!(failed.job.bindings().events(), before_events);
                    assert_eq!(
                        failed
                            .job
                            .bindings()
                            .value_json(old.as_ref().unwrap())
                            .unwrap(),
                        json!([3])
                    );
                    eprintln!(
                        "REENTRY {name} completed={completed_count} buffers={:?}",
                        failed.job.bindings().buffer_usage()
                    );
                    assert!(failed.job.reserve(budget).is_err());
                    return completed_count;
                }
            }
        }
        panic!("capacity limit was not reached")
    }
    let packed = count("packed", PackedBuffers::new().unwrap());
    let segmented = count("segmented", SegmentedBuffers::new().unwrap());
    assert!(packed > segmented);
}
