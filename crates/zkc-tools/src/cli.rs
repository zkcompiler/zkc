//! Human-facing discovery, kept separate from machine-readable execution reports.

const HELP: &str = "zkc — execute mathematical Entry packages and native proofs

Usage: zkc COMMAND [ARGUMENTS]

Commands:
  compile                   Compile .zkc source to an authenticated Entry package
  run                       Run a source Entry package with named inputs
  prove                     Produce a proof from a source Entry package
  verify                    Verify a proof using independent named public inputs
  bindings                  Generate Rust data bindings pinned to an Entry package
  run-bundle                Execute an authenticated native run bundle
  prove-bundle              Produce a proof from a pinned native deployment
  verify-bundle             Verify a proof with a pinned native deployment

Options:
  -h, --help                Show this help
  --version                 Show the package version

Use 'zkc COMMAND --help' for arguments. Compile .zkc sources with zkc compile; use zkc-compile for direct IR.
File inputs must be bounded regular files. Output aliases and symlink destinations refuse.
All outputs are encoded/staged before per-file atomic replacement; partial publication is reported.
Oversized capacity requests refuse instead of being clamped.
Start in a prepared checkout with 'just demo'; see docs/getting-started.md.
";

fn command_help(command: &str) -> Option<&'static str> {
    match command {
        "compile" => Some(
            "Usage: zkc compile --entry=MODULE::ENTRY --module=MODULE=FILE.zkc --output=PACKAGE [--compiler=PATH] [--asset=NAME=FORMAT=FILE] [--no-simplify] [--release-storage]\n\n\
             Modules/assets may repeat. Compilation trusts the selected compiler and source.\n\
             The result reports the exact package SHA-256 for deployment configuration.\n",
        ),
        "bindings" => Some(
            "Usage: zkc bindings PACKAGE EXPECTED_SHA256 OUTPUT.rs\n\n\
             Generate named Rust data structures and an admission helper.\n\
             Execution uses the common Entry Host; protocol algorithms are not emitted.\n",
        ),
        "run" => Some(
            "Usage: zkc run PACKAGE EXPECTED_SHA256 INPUTS [--setups=AUTHORITY] [--capacity=LIMITS] [--results=FILE]\n\n\
             INPUTS is a named zkc.entry-run/1 request. Results are opt-in file output.\n",
        ),
        "prove" | "verify" => Some(
            "Usage: zkc prove|verify PACKAGE EXPECTED_SHA256 INPUTS PROOF [--setups=AUTHORITY] [--capacity=LIMITS] [--allow-header-only] [--attempts=COUNT] [--results=FILE]\n\n\
             INPUTS is a named zkc.entry-proof/1 request. Verification supplies no prover witness.\n\
             Attempts are explicit and producer-only. One-shot proving honors Entry completion.\n\
             Authored jobs require --allow-header-only. Diagnostic reports omit returned values.\n",
        ),
        "run-bundle" => Some(
            "Usage: zkc run-bundle BUNDLE EXPECTED_SHA256 INPUTS [--setups=AUTHORITY] [--capacity=LIMITS] [--limits=LIMITS]\n\n\
             BUNDLE is protocol-bundle output; INPUTS is a zkc.bundle-inputs/1 array.\n\
             EXPECTED_SHA256 must come from trusted compilation or deployment configuration.\n\
             All roles are prepared before execution resources are issued.\n\
             Completed execution does not interpret protocol acceptance outputs.\n",
        ),
        "prove-bundle" | "verify-bundle" => Some(
            "Usage: zkc prove-bundle|verify-bundle DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF [--setups=AUTHORITY] [--attempts=POLICY] [--capacity=LIMITS] [--allow-header-only]\n\n\
             DEPLOYMENT is zkc-compile protocol-proof output.\n\
             EXPECTED_SHA256 authenticates those exact file bytes and must come\n\
             from trusted compilation or deployment configuration.\n\
             Deployments without a compiler-derived transcript require --allow-header-only.\n\
             INPUTS supplies public bindings and one role's invocation values.\n\
             PROOF is atomically written by the producer and read by the validator.\n",
        ),
        _ => None,
    }
}

/// Handle discovery without opening inputs or starting execution.
pub fn discover(args: &[String]) -> Option<i32> {
    match args {
        [] => {
            eprint!("{HELP}");
            Some(2)
        }
        [option] if option == "--help" || option == "-h" => {
            print!("{HELP}");
            Some(0)
        }
        [option] if option == "--version" => {
            println!("zkc {}", env!("CARGO_PKG_VERSION"));
            Some(0)
        }
        [command, ..] if command_help(command).is_none() => {
            eprintln!("Unknown command '{command}'. Run zkc --help for commands.");
            Some(2)
        }
        [command, option] if option == "--help" || option == "-h" => {
            command_help(command).map(|help| {
                print!("{help}");
                0
            })
        }
        _ => None,
    }
}

/// Run a named command without process exit or printing. Reports omit proof payloads.
pub fn run(command: &str, args: &[String]) -> serde_json::Value {
    match command {
        "compile" | "run" | "prove" | "verify" | "bindings" => {
            crate::entry::cli::run(command, args)
        }
        "run-bundle" => crate::run::cli::run(args),
        "prove-bundle" | "verify-bundle" => crate::proof::cli::run(command == "prove-bundle", args),
        _ => serde_json::json!({"status":"refused", "phase":"arguments", "code":"unknown-command"}),
    }
}
/// Successful exit requires the requested operation and all requested publications.
pub fn succeeded(report: &serde_json::Value) -> bool {
    if report["format"] == "zkc.bundle-result/1" {
        report["status"] == "executed" && report["outcome"][0] == "completed"
    } else {
        crate::entry::cli::succeeded(report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bundle_commands_have_one_spelling() {
        for name in [
            "compile",
            "run",
            "prove",
            "verify",
            "bindings",
            "run-bundle",
            "prove-bundle",
            "verify-bundle",
        ] {
            assert!(command_help(name).is_some());
        }
        for name in ["run-entry", "produce-native-proof", "validate-native-proof"] {
            assert!(command_help(name).is_none());
            assert_eq!(run(name, &[])["code"], "unknown-command");
        }
    }
}
