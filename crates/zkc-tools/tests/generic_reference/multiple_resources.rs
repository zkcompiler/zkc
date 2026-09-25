//! Distinct same-kind capabilities retain identity across forwarding and draws.
use super::*;
use zkc_backends::Domain;

#[test]
fn two_resources_preserve_identity_and_stopped_prefix() {
    let fixture = Fixture::from_text(
        r#"module {
      fn Draw<F: domain Field>(state: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
        [draw] let (value, next) = random::draw::<F>(state);
        return (value, next);
      }
      configure Random = Draw(F = bls12-381.fr);
      protocol Pair {
        roles (P);
        inputs (P a: Rng<"bls12-381.fr">, P b: Rng<"bls12-381.fr">);
        outputs (P "bls12-381.fr"::Element, P "bls12-381.fr"::Element,
          P Rng<"bls12-381.fr">, P Rng<"bls12-381.fr">);
        local [first] P: let (x, an) = Random(a);
        local [second] P: let (y, bn) = Random(b);
        return (x, y, an, bn);
      }
      instance pair: Pair { roles (P = P); }
      entry main = pair;
    }"#,
    );
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    for budgets in [[1, 1], [0, 1], [1, 0]] {
        let mut inner = backend();
        let trace = Trace::new(&fixture.source);
        let mut values = Vec::new();
        let mut issued = Vec::new();
        for (index, (label, scalar)) in [("left", 5), ("right", 9)].into_iter().enumerate() {
            let value = inner
                .issue_test_tape(
                    Domain::new("P", "test", "main", None),
                    budgets[index],
                    vec![Scalar::from(scalar)],
                )
                .unwrap();
            trace.register_resource("P", &inner, &value, label);
            issued.push(json!([
                label,
                "P",
                [],
                budgets[index].to_string(),
                ["rng", [scalar.to_string()]]
            ]));
            values.push(value);
        }
        let ports: Vec<_> = ["a", "b"]
            .into_iter()
            .zip(&values)
            .map(|(n, v)| json!([n, trace.value("P", v)]))
            .collect();
        let originals = values.clone();
        let observer = Observed {
            inner,
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        };
        let mut runner = Runner::new(&admitted, "main", "P", "test", observer, values)
            .unwrap_or_else(|e| panic!("{}", e.error));
        let terminal = loop {
            match runner.poll() {
                Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                result @ (Action::Returned(_) | Action::Stopped(_)) => break result,
                _ => panic!("local only"),
            }
        };
        let result = fixture.reference(&json!([
            "zkc.reference-inputs/1",
            "main",
            "test",
            [["P", ports]],
            issued,
            [],
            []
        ]));
        assert_eq!(result[4], json!(trace.snapshot()));
        match terminal {
            Action::Returned(values) => assert_eq!(
                result[3],
                json!([
                    "returned",
                    values
                        .iter()
                        .map(|v| trace.value("P", v))
                        .collect::<Vec<_>>()
                ])
            ),
            Action::Stopped(stop) => {
                assert_eq!(result[3][0], "exhausted");
                assert_eq!(result[3][1], "resource-budget");
                assert_stop_location(&trace, &stop, &result[3][2], true);
            }
            _ => unreachable!(),
        }
        let actual: Vec<_> = ["left", "right"]
            .into_iter()
            .zip(&originals)
            .map(|(label, value)| {
                let Value::Rng(token) = value else {
                    unreachable!()
                };
                let r = runner.backend().inner.observe(token).unwrap();
                json!([
                    label,
                    "P",
                    [],
                    r.generation.to_string(),
                    r.draw_count.to_string(),
                    r.budget.to_string(),
                    r.stage
                ])
            })
            .collect();
        assert_eq!(result[5], json!(actual));
        assert_eq!(runner.backend().inner.active_frames(), 0);
    }
}
