//! Identity-aware retained-value accounting with real native values: shared
//! immutable allocations, equal but independent allocations, multiwidth base
//! and extension row commitments, and the element ceiling on height times width.
#[path = "domains/support.rs"]
mod support;
use support::one;

use serde_json::{Value as Json, json};
use zkc_backends::{KoalaBear, KoalaBearExt8, NativeBackend, Policy, Value, oracle::Domain};
use zkc_runtime::interactive::{
    Action, Identity, LogicalType, OperationBinding, PhysicalType, Runner, StopKind, Type, Usage,
    ValueBudget, WorkBudget, admit_supplied,
};

const INLINE: usize = 512;

fn size(n: usize, width: usize) -> usize {
    n * width + 256
}
fn element_bytes(domain: Domain) -> usize {
    match domain {
        Domain::Base => std::mem::size_of::<KoalaBear>(),
        Domain::Extension => std::mem::size_of::<KoalaBearExt8>(),
    }
}
fn field(domain: Domain) -> Identity {
    match domain {
        Domain::Base => Identity::KoalaBear,
        Domain::Extension => Identity::KoalaBearExt8,
    }
}
fn spelling(kind: Type, identity: Identity) -> String {
    PhysicalType::default_for(LogicalType::new(kind, identity).unwrap())
        .unwrap()
        .spelling()
}
fn index() -> String {
    spelling(Type::Index, Identity::None)
}
fn row(name: &str, contract: &str, identity: Identity, provider: &str) -> Json {
    json!([
        name,
        contract,
        [identity.name()],
        format!("{provider}/{contract}")
    ])
}
fn program(rows: Vec<Json>, functions: Vec<Json>, inputs: Json, body: Json) -> Vec<u8> {
    serde_json::to_vec(&json!([
        "zkc.program/0",
        rows,
        functions,
        [[
            "participant",
            "actor",
            "instance",
            "P",
            inputs,
            [],
            body,
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap()
}
fn function(name: &str, ports: Json, results: Json, body: Json) -> Json {
    json!(["function", name, ports, results, body, [name, []]])
}
fn backend(elements: usize) -> NativeBackend {
    support::backend(Policy {
        max_table_elements: elements,
        ..Policy::default()
    })
}
fn run(
    bytes: &[u8],
    backend: NativeBackend,
    inputs: Vec<Value>,
    values: ValueBudget,
    work: WorkBudget,
) -> (Result<(), String>, Usage) {
    let admitted = admit_supplied(bytes, &backend).unwrap();
    let mut runner = Runner::new_with_budgets(
        &admitted, "main", "P", "session", backend, inputs, values, work,
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let outcome = loop {
        runner.advance_local_control().unwrap();
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Returned(_) => break Ok(()),
            Action::Stopped(stop) => {
                break Err(match stop.kind {
                    StopKind::Backend(e) => e.code,
                    other => format!("{other:?}"),
                });
            }
            action => panic!("unexpected {action:?}"),
        }
    };
    (outcome, runner.usage())
}
fn unbounded() -> ValueBudget {
    ValueBudget {
        live_bytes: usize::MAX,
        total_bytes: usize::MAX,
    }
}
fn live(live_bytes: usize) -> ValueBudget {
    ValueBudget {
        live_bytes,
        total_bytes: usize::MAX,
    }
}
/// Smallest live budget with which `attempt` completes.
fn minimal_live(attempt: impl Fn(usize) -> bool) -> usize {
    let (mut low, mut high) = (0usize, 1usize << 30);
    assert!(attempt(high));
    while low + 1 < high {
        let middle = low + (high - low) / 2;
        if attempt(middle) {
            high = middle;
        } else {
            low = middle;
        }
    }
    high
}

// A local function fills three vectors with the same element. `aliased` returns
// the first vector twice and the second once; otherwise it returns three
// independently allocated vectors with equal contents. A second call then
// allocates one more vector while the results are bound.
fn vectors(aliased: bool) -> Vec<u8> {
    let vector = spelling(Type::Vector, Identity::KoalaBearExt8);
    let scalar = spelling(Type::Field, Identity::KoalaBearExt8);
    let returned = if aliased {
        json!(["a", "a", "b"])
    } else {
        json!(["a", "b", "c"])
    };
    program(
        vec![row(
            "fill",
            "vector.fill",
            Identity::KoalaBearExt8,
            "plonky3",
        )],
        vec![
            function(
                "make",
                json!([["x", scalar], ["n", index()]]),
                json!([vector, vector, vector]),
                json!([
                    ["op", "a", "fill", [], ["x", "n"], ["a"]],
                    ["op", "b", "fill", [], ["x", "n"], ["b"]],
                    ["op", "c", "fill", [], ["x", "n"], ["c"]],
                    ["return", returned]
                ]),
            ),
            function(
                "more",
                json!([["x", scalar], ["n", index()]]),
                json!([vector]),
                json!([
                    ["op", "d", "fill", [], ["x", "n"], ["d"]],
                    ["return", ["d"]]
                ]),
            ),
        ],
        json!([["x", scalar], ["n", index()]]),
        json!([
            ["local", "make", "make", ["x", "n"], ["p", "q", "r"]],
            ["local", "more", "more", ["x", "n"], ["s"]],
            ["return", []]
        ]),
    )
}

#[test]
fn equal_independent_vectors_count_separately_and_aliases_count_once() {
    const N: usize = 4096;
    let vector = size(N, 32);
    let inputs = || {
        vec![
            Value::KoalaBearExt8Field(KoalaBearExt8::from(KoalaBear::new(5))),
            Value::Index(N as u64),
        ]
    };
    let usage = |aliased| {
        run(
            &vectors(aliased),
            backend(1 << 16),
            inputs(),
            unbounded(),
            WorkBudget::default(),
        )
        .1
    };
    let (aliased, independent) = (usage(true), usage(false));
    // Four vectors were allocated in both programs, all with equal contents.
    assert_eq!(aliased.total_value_bytes, independent.total_value_bytes);
    assert_eq!(aliased.logical_bytes, independent.logical_bytes);
    // Inline inputs and the two calls' arguments are charged per binding.
    assert_eq!(independent.total_value_bytes, 4 * vector + 6 * INLINE);
    let minimal = |aliased| {
        minimal_live(|budget| {
            run(
                &vectors(aliased),
                backend(1 << 16),
                inputs(),
                live(budget),
                WorkBudget::default(),
            )
            .0
            .is_ok()
        })
    };
    let (aliased, independent) = (minimal(true), minimal(false));
    // During the second call the bound results retain two allocations when
    // aliased and three when independent, plus the new vector.
    assert_eq!(independent, 4 * vector + 4 * INLINE);
    assert_eq!(aliased, 3 * vector + 4 * INLINE);
    // Returning the same allocation three times costs no more than once.
    let once = program(
        vec![row(
            "fill",
            "vector.fill",
            Identity::KoalaBearExt8,
            "plonky3",
        )],
        vec![function(
            "make",
            json!([
                ["x", spelling(Type::Field, Identity::KoalaBearExt8)],
                ["n", index()]
            ]),
            json!(vec![spelling(Type::Vector, Identity::KoalaBearExt8); 3]),
            json!([
                ["op", "a", "fill", [], ["x", "n"], ["a"]],
                ["return", ["a", "a", "a"]]
            ]),
        )],
        json!([
            ["x", spelling(Type::Field, Identity::KoalaBearExt8)],
            ["n", index()]
        ]),
        json!([
            ["local", "make", "make", ["x", "n"], ["p", "q", "r"]],
            ["return", []]
        ]),
    );
    let shared = minimal_live(|budget| {
        run(
            &once,
            backend(1 << 16),
            inputs(),
            live(budget),
            WorkBudget::default(),
        )
        .0
        .is_ok()
    });
    assert_eq!(shared, vector + 4 * INLINE);
}

// Commit a height x width matrix once and open `count` rows from a loop that
// captures the opening state and passes it to a local call each iteration.
fn openings(domains: &[(Domain, usize, usize)], count: u64) -> (Vec<u8>, Vec<Value>) {
    let mut rows = vec![];
    let mut functions = vec![];
    let mut inputs = vec![];
    let mut values = vec![];
    let mut body = vec![];
    let mut captures = vec![];
    let mut loop_body = vec![];
    for (k, (domain, height, width)) in domains.iter().enumerate() {
        let identity = field(*domain);
        let tree = domain.identity();
        let vector = spelling(Type::Vector, identity);
        let scalar = spelling(Type::Field, identity);
        let state = spelling(Type::OpeningState, tree);
        let root = spelling(Type::Commitment, tree);
        let path = spelling(Type::Proof, tree);
        rows.push(row(
            &format!("fill_kernel{k}"),
            "vector.fill",
            identity,
            "plonky3",
        ));
        rows.push(row(
            &format!("commit_kernel{k}"),
            "oracle.commit",
            tree,
            "plonky3",
        ));
        rows.push(row(
            &format!("open_kernel{k}"),
            "oracle.open",
            tree,
            "plonky3",
        ));
        functions.push(function(
            &format!("make{k}"),
            json!([["x", scalar], ["n", index()], ["w", index()]]),
            json!([root, state]),
            json!([
                [
                    "op",
                    "fill",
                    format!("fill_kernel{k}"),
                    [],
                    ["x", "n"],
                    ["v"]
                ],
                [
                    "op",
                    "commit",
                    format!("commit_kernel{k}"),
                    [],
                    ["v", "w"],
                    ["root", "state"]
                ],
                ["return", ["root", "state"]]
            ]),
        ));
        functions.push(function(
            &format!("open{k}"),
            json!([["state", state], ["at", index()]]),
            json!([vector, path]),
            json!([
                [
                    "op",
                    "open",
                    format!("open_kernel{k}"),
                    [],
                    ["state", "at"],
                    ["row", "path"]
                ],
                ["return", ["row", "path"]]
            ]),
        ));
        let (x, n, w) = (format!("x{k}"), format!("n{k}"), format!("w{k}"));
        inputs.extend([json!([x, scalar]), json!([n, index()]), json!([w, index()])]);
        values.extend([
            match domain {
                Domain::Base => Value::KoalaBearField(KoalaBear::new(3)),
                Domain::Extension => {
                    Value::KoalaBearExt8Field(KoalaBearExt8::from(KoalaBear::new(3)))
                }
            },
            Value::Index((height * width) as u64),
            Value::Index(*width as u64),
        ]);
        body.push(json!([
            "local",
            format!("make{k}"),
            format!("make{k}"),
            [x, n, w],
            [format!("root{k}"), format!("state{k}")]
        ]));
        captures.push(json!(format!("state{k}")));
        loop_body.push(json!([
            "local",
            format!("open{k}"),
            format!("open{k}"),
            [format!("state{k}"), "i"],
            [format!("row{k}"), format!("path{k}")]
        ]));
    }
    inputs.push(json!(["count", index()]));
    values.push(Value::Index(count));
    loop_body.push(json!(["yield", []]));
    body.push(json!([
        "loop",
        "openings",
        ["value", "count", "64", "i"],
        [],
        captures,
        loop_body,
        []
    ]));
    body.push(json!(["return", []]));
    (
        program(rows, functions, Json::Array(inputs), Json::Array(body)),
        values,
    )
}
fn state_bytes(domain: Domain, height: usize, width: usize) -> usize {
    height * width * element_bytes(domain) + (2 * height.next_power_of_two() - 1) * 32 + 256
}
fn depth(height: usize) -> usize {
    (usize::BITS - (height - 1).leading_zeros()) as usize
}

#[test]
fn captured_multiwidth_states_are_retained_once_and_openings_charge_their_extent() {
    for (domain, height, width) in [
        (Domain::Extension, 1024, 1),
        (Domain::Extension, 1024, 4),
        (Domain::Extension, 1024, 8),
        (Domain::Base, 1024, 1),
        (Domain::Base, 1024, 8),
        (Domain::Base, 1024, 16),
        (Domain::Extension, 4096, 4),
    ] {
        let e = element_bytes(domain);
        let vector = size(height * width, e);
        let state = state_bytes(domain, height, width);
        let opened = size(width, e) + size(depth(height), 32);
        let usage = |count| {
            let (bytes, values) = openings(&[(domain, height, width)], count);
            let (outcome, usage) = run(
                &bytes,
                backend(1 << 20),
                values,
                unbounded(),
                WorkBudget::default(),
            );
            outcome.unwrap();
            usage
        };
        for count in [1u64, 64] {
            let u = usage(count);
            let label = format!("{domain:?} {height}x{width} count {count}");
            // Inputs, call arguments and the commitment root are inline; each
            // iteration adds its index, the call's index argument and one opening.
            assert_eq!(
                u.total_value_bytes,
                vector + state + 9 * INLINE + count as usize * (2 * INLINE + opened),
                "{label}"
            );
            // Fill and commit read and write their data once; each opening reads
            // one row and path plus its index, then allocates them.
            assert_eq!(
                u.logical_bytes,
                (2 * vector + state + 4 * INLINE + count as usize * (2 * opened + INLINE)) as u64,
                "{label}"
            );
            assert_eq!((u.live_values, u.live_value_bytes), (0, 0));
        }
        // The peak is inside the committing call: inputs, arguments, vector,
        // root and state. Captured and passed states add nothing afterwards.
        let peak = vector + state + 8 * INLINE;
        for budget in [peak - 1, peak] {
            let (bytes, values) = openings(&[(domain, height, width)], 64);
            let (outcome, _) = run(
                &bytes,
                backend(1 << 20),
                values,
                live(budget),
                WorkBudget::default(),
            );
            assert_eq!(
                outcome.is_ok(),
                budget == peak,
                "{domain:?} {height}x{width}"
            );
        }
    }
}

#[test]
fn mixed_base_and_extension_commitments_use_their_own_element_widths() {
    let (height, base, extension) = (2048, 16, 2);
    let parts = [
        (Domain::Base, height, base),
        (Domain::Extension, height, extension),
    ];
    let (bytes, values) = openings(&parts, 64);
    let (outcome, u) = run(
        &bytes,
        backend(1 << 20),
        values,
        unbounded(),
        WorkBudget::default(),
    );
    outcome.unwrap();
    // Sixteen base columns and two extension columns both occupy 64 bytes per row.
    assert_eq!(
        base * element_bytes(Domain::Base),
        extension * element_bytes(Domain::Extension)
    );
    // Seven inputs, two calls with three inline arguments, two roots returned
    // and rebound; per iteration one index and two inline call arguments.
    let mut total = 17 * INLINE + 64 * 3 * INLINE;
    for (domain, height, width) in parts {
        let e = element_bytes(domain);
        total += size(height * width, e)
            + state_bytes(domain, height, width)
            + 64 * (size(width, e) + size(depth(height), 32));
    }
    assert_eq!(u.total_value_bytes, total);
}

#[test]
fn row_commitment_preflights_height_times_width_before_allocation() {
    for domain in [Domain::Base, Domain::Extension] {
        // Exactly at the element ceiling succeeds for every width.
        for width in [1usize, 4, 8] {
            let height = (1 << 14) / width;
            let (bytes, values) = openings(&[(domain, height, width)], 1);
            let (outcome, _) = run(
                &bytes,
                backend(1 << 14),
                values,
                unbounded(),
                WorkBudget::default(),
            );
            assert!(outcome.is_ok(), "{domain:?} {height}x{width}: {outcome:?}");
        }
        // One more row exceeds the ceiling although height and width each fit;
        // the refusal precedes the vector and the committed copy.
        for width in [1usize, 4, 8] {
            let height = (1 << 14) / width + 1;
            let (bytes, values) = openings(&[(domain, height, width)], 1);
            let (outcome, usage) = run(
                &bytes,
                backend(1 << 14),
                values,
                unbounded(),
                WorkBudget::default(),
            );
            assert_eq!(
                outcome.unwrap_err(),
                "exhausted:element-limit",
                "{domain:?} {height}x{width}"
            );
            assert_eq!(usage.total_value_bytes, 7 * INLINE);
        }
        // A live budget that cannot hold the committed table and tree refuses the
        // commitment before allocating it, with the vector already retained.
        let (height, width) = (1024, 8);
        let e = element_bytes(domain);
        let budget = size(height * width, e) + 8 * INLINE + state_bytes(domain, height, width) - 1;
        let (bytes, values) = openings(&[(domain, height, width)], 1);
        let (outcome, usage) = run(
            &bytes,
            backend(1 << 20),
            values,
            live(budget),
            WorkBudget::default(),
        );
        assert_eq!(outcome.unwrap_err(), "exhausted:output-bytes");
        assert_eq!(
            usage.total_value_bytes,
            size(height * width, e) + 7 * INLINE
        );
    }
}

#[test]
fn retained_regression_opens_65536_extension_rows_64_times_under_default_budgets() {
    // The previous per-binding charge refused this at the twentieth opening with
    // 264,512,048 bytes against the 268,435,456 cumulative default.
    let (bytes, values) = openings(&[(Domain::Extension, 65536, 1)], 64);
    let (outcome, u) = run(
        &bytes,
        backend(1 << 16),
        values,
        ValueBudget::default(),
        WorkBudget::default(),
    );
    outcome.unwrap();
    let vector = size(65536, 32);
    let state = state_bytes(Domain::Extension, 65536, 1);
    let opened = size(1, 32) + size(16, 32);
    assert_eq!(u.iterations, 64);
    assert_eq!(
        u.total_value_bytes,
        vector + state + 9 * INLINE + 64 * (2 * INLINE + opened)
    );
    assert_eq!(
        u.logical_bytes,
        (2 * vector + state + 4 * INLINE + 64 * (2 * opened + INLINE)) as u64
    );
}

#[test]
fn row_check_preflights_claimed_height_times_width_without_allocation() {
    for domain in [Domain::Base, Domain::Extension] {
        let committed = one(
            backend(1 << 16),
            OperationBinding {
                contract: "oracle.commit".into(),
                arguments: vec![domain.identity().name().into()],
                implementation: "plonky3/oracle.commit".into(),
            },
            &[],
            vec![
                match domain {
                    Domain::Base => Value::KoalaBearVector(vec![KoalaBear::new(1); 8].into()),
                    Domain::Extension => Value::KoalaBearExt8Vector(
                        vec![KoalaBearExt8::from(KoalaBear::new(1)); 8].into(),
                    ),
                },
                Value::Index(2),
            ],
        )
        .0
        .unwrap();
        let opened = one(
            backend(1 << 16),
            OperationBinding {
                contract: "oracle.open".into(),
                arguments: vec![domain.identity().name().into()],
                implementation: "plonky3/oracle.open".into(),
            },
            &[],
            vec![committed[1].clone(), Value::Index(0)],
        )
        .0
        .unwrap();
        let check = |width: u64, height: u64| {
            one(
                backend(1 << 16),
                OperationBinding {
                    contract: "oracle.check".into(),
                    arguments: vec![domain.identity().name().into()],
                    implementation: "plonky3/oracle.check".into(),
                },
                &[],
                vec![
                    committed[0].clone(),
                    Value::Index(width),
                    Value::Index(height),
                    Value::Index(0),
                    opened[0].clone(),
                    opened[1].clone(),
                ],
            )
            .0
        };
        assert!(matches!(check(2, 4).unwrap()[0], Value::Bool(true)));
        // Each claimed dimension fits; their product does not.
        assert_eq!(
            check(1 << 8, 1 << 9).unwrap_err(),
            "exhausted:oracle-element-limit"
        );
        // The product would overflow a machine word.
        assert_eq!(
            check(1 << 40, 1 << 24).unwrap_err(),
            "exhausted:oracle-element-limit"
        );
        assert_eq!(check(1, (1 << 24) + 1).unwrap_err(), "refused:oracle-shape");
    }
}
