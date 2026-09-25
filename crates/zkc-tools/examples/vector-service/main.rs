//! Explicit consumer wiring: artifacts do not choose providers or checker tools.
mod library;
use library::Service;
use serde_json::{Value, json};
use std::{env, fs::File, io::Read};
use zkc_runtime::{AdmittedJob, AdmittedProgram, Budget, Error, Outcome, format};
use zkc_tools::LeanChecker;

fn read(path: &str) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|_| Error("io-error"))?
        .take(1024 * 1024 + 1)
        .read_to_end(&mut bytes)
        .map_err(|_| Error("io-error"))?;
    if bytes.len() > 1024 * 1024 {
        return Err(Error("byte-limit"));
    }
    Ok(bytes)
}
fn run(args: &[String]) -> Result<Value, Error> {
    if args.len() != 4 && args.len() != 7 {
        return Err(Error(
            "usage: vector-service SOURCE PLAN INPUTS LEAN [--fault KIND CALL]",
        ));
    }
    let fault = if args.len() == 7 {
        if args[4] != "--fault"
            || !matches!(
                args[5].as_str(),
                "wrong-length" | "noncanonical" | "wrong-flag" | "wrong-type" | "wrong-content"
            )
        {
            return Err(Error("invalid-fault"));
        }
        Some((
            args[5].clone(),
            args[6]
                .parse::<usize>()
                .ok()
                .filter(|n| *n > 0)
                .ok_or(Error("invalid-fault"))?,
        ))
    } else {
        None
    };
    let invocation = format::parse(&read(&args[2])?)?;
    let invocation = format::array(&invocation, 2)?;
    let bindings = Service::new(&invocation[1], fault)?;
    let checker = LeanChecker::new(&args[3]).map_err(|_| Error("checker-io"))?;
    let program =
        match AdmittedProgram::admit(read(&args[0])?, read(&args[1])?, None, &bindings, &checker) {
            Ok(program) => program,
            Err(failure) => {
                return Ok(json!({"status":"admission-failed", "code":failure.reason.0,
            "state":bindings.state(), "events":bindings.events()}));
            }
        };
    let job = match AdmittedJob::bind(program, invocation[0].clone(), bindings) {
        Ok(job) => job,
        Err(failure) => {
            return Ok(json!({"status":"binding-failed", "code":failure.reason.0,
            "state":failure.bindings.state(), "events":failure.bindings.events()}));
        }
    };
    let session = match job.reserve(Budget::default()) {
        Ok(session) => session,
        Err(failure) => {
            return Ok(json!({"status":"start-failed", "code":failure.reason.0,
            "state":failure.job.bindings().state(), "events":failure.job.bindings().events()}));
        }
    };
    let done = session.execute();
    let failure_status = if done.started() {
        "interrupted"
    } else {
        "start-failed"
    };
    let outcome = match done.outcome() {
        Ok(Outcome::Returned(value)) => json!(["returned", value.json()]),
        Ok(Outcome::Stopped(why)) => json!(["stopped", why.name()]),
        Err(error) => {
            return Ok(json!({"status":failure_status, "code":error.0,
            "state":done.bindings().state(), "events":done.bindings().events()}));
        }
    };
    Ok(json!({"status":"executed", "outcome":outcome,
        "state":done.bindings().state(), "events":done.bindings().events()}))
}
fn main() {
    match run(&env::args().skip(1).collect::<Vec<_>>()) {
        Ok(value) => println!("{value}"),
        Err(error) => {
            println!("{}", json!({"status":"refused", "code":error.0}));
            std::process::exit(1);
        }
    }
}
