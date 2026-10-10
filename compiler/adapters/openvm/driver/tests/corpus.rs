use zkc_openvm_relation::model::{Export, RowClass, Scope};
use zkc_openvm_relation::slice::RANGE;
use zkc_openvm_relation_driver::{Case, Disagreement, compare, corpus};

#[test]
fn trace_mutations_agree_with_upstream_constraints_and_buses() {
    let (export, cases) = corpus();
    assert_eq!(export.airs.len(), 5);
    assert!(cases.len() > 150);
    eprintln!(
        "{} cases, {} satisfying",
        cases.len(),
        cases.iter().filter(|c| c.outcome.satisfied()).count()
    );
}

/// Every lowered assertion reports a nonzero residual on every row class
/// its scope covers and the corpus heights contain. With the exact
/// comparison, deleting any assertion therefore leaves a residual uncovered.
#[test]
fn every_lowered_assertion_reports_a_residual_on_each_row_class() {
    let (export, cases) = corpus();
    let mut missing = vec![];
    for (t, air) in export.airs.iter().enumerate() {
        for (a, assertion) in air.assertions.iter().enumerate() {
            for class in RowClass::ALL
                .into_iter()
                .filter(|c| assertion.scope.covers(*c))
            {
                let occurs = cases.iter().any(|case| {
                    case.data.tables[t]
                        .as_ref()
                        .is_some_and(|table| class != RowClass::Interior || table.height > 2)
                });
                let reported = cases.iter().any(|case| {
                    case.outcome.residuals.iter().any(|&(tt, aa, row, _)| {
                        let height = case.data.tables[t].as_ref().map(|table| table.height);
                        tt == t && aa == a && Some(class) == height.map(|h| RowClass::of(row, h))
                    })
                });
                if occurs && !reported {
                    missing.push(format!(
                        "{} assertion {a} ({}) on {class:?} rows",
                        air.name,
                        assertion.scope.name()
                    ));
                }
            }
        }
    }
    assert!(missing.is_empty(), "{missing:#?}");
}

/// Whether some case leaves an upstream residual of the constraint on a row
/// of the scope uncovered by the lowered assertions of `mutant`.
fn detected(
    mutant: &Export,
    cases: &[Case],
    table: usize,
    constraint: usize,
    scope: Scope,
) -> bool {
    cases.iter().any(|case| {
        let height = case.data.tables[table].as_ref().map_or(0, |t| t.height);
        compare(mutant, &case.data, &case.oracle).is_err_and(|found| {
            found.iter().any(|d| {
                matches!(*d, Disagreement::Uncovered { table: t, constraint: c, row }
                    if t == table && c == constraint && scope.contains(row, height))
            })
        })
    })
}

#[test]
fn deleting_lowered_assertions_is_detected() {
    let (export, cases) = corpus();
    for (t, air) in export.airs.iter().enumerate() {
        for a in 0..air.assertions.len() {
            let mut mutant = export.clone();
            let removed = mutant.airs[t].assertions.remove(a);
            assert!(
                detected(&mutant, &cases, t, removed.constraint, removed.scope),
                "deleting {} assertion {a} ({}) is not detected",
                air.name,
                removed.scope.name()
            );
        }
    }
    // Drop every assertion of one row-class scope at once.
    let scopes = [
        Scope::All,
        Scope::First,
        Scope::Last,
        Scope::Transition,
        Scope::Interior,
        Scope::Tail,
    ];
    for scope in scopes {
        let mut mutant = export.clone();
        let mut removed = vec![];
        for (t, air) in mutant.airs.iter_mut().enumerate() {
            removed.extend(
                air.assertions
                    .iter()
                    .filter(|a| a.scope == scope)
                    .map(|a| (t, a.constraint)),
            );
            air.assertions.retain(|a| a.scope != scope);
        }
        for (t, constraint) in removed {
            assert!(
                detected(&mutant, &cases, t, constraint, scope),
                "dropping {} assertions leaves {} constraint {constraint} covered",
                scope.name(),
                export.airs[t].name
            );
        }
    }
    // Without last-row assertions the Bundle accepts the range table that
    // offers an out-of-range value; upstream still rejects it.
    let forged = cases
        .iter()
        .find(|c| c.name == "range-padding-out-of-range")
        .unwrap();
    let height = forged.data.tables[RANGE].as_ref().unwrap().height;
    assert!(
        forged
            .outcome
            .residuals
            .iter()
            .all(|&(t, a, row, _)| t == RANGE
                && export.airs[RANGE].assertions[a].scope == Scope::Last
                && row + 1 == height)
    );
    let mut mutant = export.clone();
    mutant.airs[RANGE]
        .assertions
        .retain(|a| a.scope != Scope::Last);
    let found = compare(&mutant, &forged.data, &forged.oracle).unwrap_err();
    assert!(found.contains(&Disagreement::Satisfaction {
        bundle: true,
        upstream: false
    }));
}
