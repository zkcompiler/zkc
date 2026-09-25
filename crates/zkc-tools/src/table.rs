//! Host entry for the finite closed-source table interpreter.
use crate::LeanChecker;
use serde_json::{Value, json};
use std::path::Path;
use zkc_runtime::{
    AdmittedJob, AdmittedProgram, Budget, Error, Outcome, PhaseEvidence,
    buffer::{BufferStore, PackedBuffers, SegmentedBuffers},
    format,
    table::{
        Phase, PhysicalTableBindings, SmallPrimeKernel, State, TableBindings, TableLibrary,
        TapeProvider,
    },
};
fn read(path: &str) -> Result<Vec<u8>, Error> {
    crate::host::io::read_bounded(path, 1024 * 1024).map_err(|error| match error {
        crate::host::io::ReadError::Io(_) => Error("io-error"),
        crate::host::io::ReadError::Limit => Error("byte-limit"),
    })
}
/// Execute table CLI arguments, retaining the selected storage, checker and phase policy.
pub fn run(args: &[String]) -> Result<Value, Error> {
    let (args, storage) = match args {
        [rest @ .., flag, storage] if flag == "--storage" => (rest, storage.as_str()),
        _ => (args, "packed"),
    };
    match storage {
        "packed" => run_with_storage(args, PackedBuffers::new()?),
        "segmented" => run_with_storage(args, SegmentedBuffers::new()?),
        _ => Err(Error("unsupported-storage")),
    }
}
fn run_with_storage<S: BufferStore<u8>>(args: &[String], storage: S) -> Result<Value, Error> {
    let physical = args.first().is_some_and(|mode| mode == "run-physical");
    let mut endpoint = false;
    let mut phase = match args {
        [mode, _, _, _, _] if mode == "run" || mode == "run-physical" => None,
        [mode, _, _, _, _, flag, profile, certificate]
            if (mode == "run" || physical) && flag == "--phase" =>
        {
            Some(PhaseEvidence {
                entry: None,
                profile: profile.clone(),
                certificate: read(certificate)?,
            })
        }
        [mode, _, _, _, _, flag, profile, certificate]
            if (mode == "run" || physical) && flag == "--endpoint" =>
        {
            endpoint = true;
            Some(PhaseEvidence {
                profile: profile.clone(),
                certificate: read(certificate)?,
                entry: None,
            })
        }
        _ => {
            return Err(Error(
                "usage: zkc run|run-physical SOURCE PLAN INPUTS CHECKER [--phase PROFILE CERTIFICATE | --endpoint PROFILE CERTIFICATE] [--storage packed|segmented]",
            ));
        }
    };
    let source = read(&args[1])?;
    let candidate = read(&args[2])?;
    let checker = LeanChecker::new(Path::new(&args[4])).map_err(|_| Error("checker-io-error"))?;
    let invocation = format::parse(&read(&args[3])?)?;
    let invocation = format::array(&invocation, 2)?;
    let bindings = if endpoint {
        let state = format::array(&invocation[1], 3)?;
        let actor = format::string(&state[0])?.to_owned();
        let entry_phase = Phase::decode(&state[1])?;
        let (state, provider) = State::decode(&state[2])?;
        TableBindings::with_storage(SmallPrimeKernel, provider, state, storage)?
            .with_endpoint(actor, entry_phase)?
    } else {
        let (state, provider) = State::decode(&invocation[1])?;
        TableBindings::with_storage(SmallPrimeKernel, provider, state, storage)?
    };
    if let Some(evidence) = phase.as_mut() {
        evidence.entry = bindings.endpoint_entry();
    }
    if physical {
        return run_physical(source, candidate, phase, &invocation[0], bindings, &checker);
    }
    let program = AdmittedProgram::admit(source, candidate, phase, &TableLibrary, &checker)
        .map_err(|e| e.reason)?;
    let job = AdmittedJob::bind(program, invocation[0].clone(), bindings)
        .map_err(|failure| failure.reason)?;
    let session = match job.reserve(Budget::default()) {
        Ok(session) => session,
        Err(failure) => {
            return Ok(json!({"status":"start-failed","code":failure.reason.0,
            "state":failure.job.bindings().state_json(),"events":failure.job.bindings().events()}));
        }
    };
    let done = session.execute();
    let failure_status = if done.started() {
        "interrupted"
    } else {
        "start-failed"
    };
    let (outcome, bindings) = done.into_parts();
    match outcome {
        Err(error) => Ok(
            json!({"status":failure_status,"code":error.0,"state":bindings.state_json(),"events":bindings.events()}),
        ),
        Ok(outcome) => {
            let outcome = match outcome {
                Outcome::Returned(value) => {
                    json!(["returned", bindings.value_json(&value)?])
                }
                Outcome::Stopped(reason) => json!(["stopped", reason.name()]),
            };
            Ok(
                json!({"status":"executed","outcome":outcome,"state":bindings.state_json(),"events":bindings.events()}),
            )
        }
    }
}

fn physical_report<S: BufferStore<u8>>(
    execution: Value,
    bindings: &PhysicalTableBindings<SmallPrimeKernel, TapeProvider, S>,
) -> Value {
    json!({"execution": execution, "table-evaluations": bindings.table_evaluations(),
        "scalar-cells": bindings.scalar_cells()})
}
fn run_physical<S: BufferStore<u8>>(
    source: Vec<u8>,
    candidate: Vec<u8>,
    phase: Option<PhaseEvidence>,
    inputs: &Value,
    bindings: TableBindings<SmallPrimeKernel, TapeProvider, S>,
    checker: &LeanChecker,
) -> Result<Value, Error> {
    let program =
        AdmittedProgram::admit_physical(source, candidate, phase, checker).map_err(|e| e.reason)?;
    let bindings = PhysicalTableBindings::new(bindings)?;
    let job = match AdmittedJob::bind(program, inputs.clone(), bindings) {
        Ok(job) => job,
        Err(failure) if matches!(failure.reason.0, "reservation-failed" | "capacity-overflow") => {
            return Ok(physical_report(
                json!({"status":"start-failed","code":failure.reason.0,
                "state":failure.bindings.state_json(),"events":failure.bindings.events()}),
                &failure.bindings,
            ));
        }
        Err(failure) => return Err(failure.reason),
    };
    let session = match job.reserve(Budget::default()) {
        Ok(session) => session,
        Err(failure) => {
            let bindings = failure.job.bindings();
            return Ok(physical_report(
                json!({"status":"start-failed","code":failure.reason.0,
                "state":bindings.state_json(),"events":bindings.events()}),
                bindings,
            ));
        }
    };
    let done = session.execute();
    let status = if done.started() {
        "interrupted"
    } else {
        "start-failed"
    };
    let (outcome, mut bindings) = done.into_parts();
    // Completion retains the exact owner through output decoding, including a
    // returned lazy reference's scratch and table-evaluation accounting.
    let outcome = outcome.and_then(|outcome| match outcome {
        Outcome::Returned(value) => Ok(json!(["returned", bindings.value_json(&value)?])),
        Outcome::Stopped(reason) => Ok(json!(["stopped", reason.name()])),
    });
    let execution = match outcome {
        Ok(outcome) => json!({"status":"executed","outcome":outcome,
            "state":bindings.state_json(),"events":bindings.events()}),
        Err(error) => json!({"status":status,"code":error.0,
            "state":bindings.state_json(),"events":bindings.events()}),
    };
    Ok(physical_report(execution, &bindings))
}
