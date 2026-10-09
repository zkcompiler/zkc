//! Maintained fixtures of the Plonky3 AIR adapter and their checks.
//!
//! The fixture set names the client AIRs it captures. This selection belongs
//! to the adapter's driver; the zkc compiler and runtime never see AIR names.

use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use zkc_plonky3_air::field::F;
use zkc_plonky3_air::reference::upstream_failures;
use zkc_plonky3_air::view::{ClosedView, SelectorLaw, violations};
use zkc_plonky3_air::{Export, Instance, Refusal, Witness};
use zkc_plonky3_air_client::{CounterAir, RecurrenceAir};

/// Path of each fixture directory relative to the repository root, as written
/// into ring-asset manifests.
pub const FIXTURE_ROOT: &str = "compiler/adapters/plonky3/fixtures";

pub struct Fixture {
    pub name: &'static str,
    pub export: Export,
    pub instance: Instance,
    pub witness: Witness,
    /// Upstream debug-builder failures of this instance and witness.
    pub upstream_failures: Vec<(usize, usize)>,
}

fn fixture<A>(
    name: &'static str,
    air: &A,
    trace: RowMajorMatrix<F>,
    public_values: Vec<F>,
) -> Result<Fixture, Refusal>
where
    A: p3_air::Air<p3_air::SymbolicAirBuilder<F>>
        + for<'a> p3_air::Air<p3_air::DebugConstraintBuilder<'a, F>>,
{
    let export = zkc_plonky3_air::export(air, name)?;
    let instance = Instance {
        export_sha256: export.sha256(),
        height: trace.values.len() / trace.width,
        public_values,
    };
    let upstream_failures = upstream_failures(air, &trace, &instance.public_values);
    Ok(Fixture {
        name,
        export,
        instance,
        witness: Witness { trace },
        upstream_failures,
    })
}

/// The maintained fixture set.
pub fn fixtures() -> Result<Vec<Fixture>, Refusal> {
    let recurrence = RecurrenceAir { log_height: 3 };
    let (trace, publics) = recurrence.generate(F::from_u32(2), F::from_u32(5));
    Ok(vec![
        fixture("recurrence", &recurrence, trace, publics)?,
        fixture(
            "counter-guarded",
            &CounterAir { guarded: true },
            CounterAir::generate(8),
            vec![],
        )?,
        fixture(
            "counter-wrapping",
            &CounterAir { guarded: false },
            CounterAir::generate(8),
            vec![],
        )?,
    ])
}

fn failures_text(failures: &[(usize, usize)]) -> String {
    let rows: Vec<String> = failures.iter().map(|(r, c)| format!("[{r},{c}]")).collect();
    format!("{{\"upstream_failures\":[{}]}}\n", rows.join(","))
}

/// Exact file contents of one fixture, by file name.
pub fn files(fixture: &Fixture) -> Vec<(&'static str, String)> {
    let digest = fixture.export.arena.sha256();
    vec![
        ("export.json", fixture.export.to_text()),
        ("arena.json", fixture.export.arena_text()),
        (
            "ring-assets.json",
            format!(
                "[\"zkc.ring-assets/0\",[[\"{digest}\",\"{FIXTURE_ROOT}/{}/arena.json\"]]]\n",
                fixture.name
            ),
        ),
        ("instance.json", fixture.instance.to_text()),
        ("witness.json", fixture.witness.to_text()),
        ("expected.json", failures_text(&fixture.upstream_failures)),
    ]
}

/// Import a fixture's files independently of its in-memory capture and
/// recompute the violation set with the adapter's arena interpreter.
pub fn import_violations(
    export: &str,
    instance: &str,
    witness: &str,
) -> Result<Vec<(usize, usize)>, Refusal> {
    let export = Export::parse(export)?;
    let instance = Instance::parse(instance)?;
    let witness = Witness::parse(witness)?;
    let view = ClosedView::bind(&export, &instance)?;
    let inputs = view.row_inputs(&witness.trace, SelectorLaw::RowIndicator)?;
    Ok(violations(
        &view.residuals(&inputs),
        export.assertions.len(),
    ))
}

pub fn expected_text(failures: &[(usize, usize)]) -> String {
    failures_text(failures)
}
