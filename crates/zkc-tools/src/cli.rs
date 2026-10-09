//! Command discovery and argument admission over the Entry and bundle transports.
mod arguments;
pub(crate) use arguments::Arguments;
use arguments::{Command, OptionSpec as Opt};

const SETUPS: Opt = Opt::new("--setups=AUTHORITY");
const CAPACITY: Opt = Opt::new("--capacity=LIMITS");
const HEADER: Opt = Opt::new("--allow-header-only");
const RESULTS: Opt = Opt::new("--results=FILE");
const PROOF: &str = "INPUTS is a zkc.entry-proof/0 request. Verification supplies no prover witness.\nAuthored jobs require --allow-header-only. Returned values require --results.\nExpression assets come from the package; no evaluator manifest is accepted.";
const BUNDLE_PROOF: &str = "DEPLOYMENT is zkc-compile protocol-proof output. EXPECTED_SHA256 must come from\ntrusted compilation or deployment configuration. INPUTS supplies public bindings\nand one role's invocation values. Authored transcripts require --allow-header-only.";
const COMMANDS: &[Command] = &[
    Command {
        name: "compile",
        summary: "Compile .zkc source to an authenticated Entry package",
        positional: "",
        options: &[
            Opt::new("--entry=MODULE::ENTRY").required(),
            Opt::new("--module=MODULE=FILE.zkc").required().repeated(),
            Opt::new("--output=PACKAGE").required(),
            Opt::new("--compiler=PATH"),
            Opt::new("--asset=NAME=FORMAT=FILE").repeated(),
            Opt::new("--no-simplify"),
            Opt::new("--release-storage"),
        ],
        description: "Compilation trusts the selected compiler and source. The report supplies the\nexact package SHA-256 for deployment configuration. Modules and assets may repeat.",
    },
    Command {
        name: "inspect",
        summary: "Show an authenticated package's checked interface",
        positional: "PACKAGE EXPECTED_SHA256",
        options: &[],
        description: "Show Entry metadata, ports, services and setups without executing the package.\nEXPECTED_SHA256 must come from trusted compilation or deployment configuration.\nInspection checks metadata consistency; it does not admit executable programs.",
    },
    Command {
        name: "run",
        summary: "Run a source Entry with named inputs",
        positional: "PACKAGE EXPECTED_SHA256 INPUTS",
        options: &[SETUPS, CAPACITY, Opt::new("--limits=LIMITS"), RESULTS],
        description: "INPUTS is a zkc.entry-run/0 request. --limits reads zkc.bundle-limits/0.\nReturned values require --results. All roles are prepared before execution.\nExpression assets come from the package; no evaluator manifest is accepted.",
    },
    Command {
        name: "prove",
        summary: "Produce a proof from a source Entry",
        positional: "PACKAGE EXPECTED_SHA256 INPUTS PROOF",
        options: &[
            SETUPS,
            CAPACITY,
            HEADER,
            Opt::new("--attempts=COUNT").unsigned(),
            RESULTS,
        ],
        description: PROOF,
    },
    Command {
        name: "verify",
        summary: "Verify a proof with independent named public inputs",
        positional: "PACKAGE EXPECTED_SHA256 INPUTS PROOF",
        options: &[SETUPS, CAPACITY, HEADER, RESULTS],
        description: PROOF,
    },
    Command {
        name: "bindings",
        summary: "Generate Rust data bindings pinned to an Entry",
        positional: "PACKAGE EXPECTED_SHA256 OUTPUT.rs",
        options: &[],
        description: "Generate named Rust data structures and an admission helper. Execution uses\nthe common Entry Host; protocol algorithms are not emitted.",
    },
    Command {
        name: "run-bundle",
        summary: "Execute an authenticated run bundle",
        positional: "BUNDLE EXPECTED_SHA256 INPUTS",
        options: &[SETUPS, CAPACITY, Opt::new("--limits=LIMITS")],
        description: "BUNDLE is protocol-bundle output; INPUTS is a zkc.bundle-inputs/0 array.\nEXPECTED_SHA256 comes from trusted compilation or deployment configuration.\nCompleted execution does not interpret protocol acceptance outputs.",
    },
    Command {
        name: "prove-bundle",
        summary: "Produce a proof from a pinned deployment",
        positional: "DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF",
        options: &[SETUPS, Opt::new("--attempt-policy=FILE"), CAPACITY, HEADER],
        description: BUNDLE_PROOF,
    },
    Command {
        name: "verify-bundle",
        summary: "Verify a proof with a pinned deployment",
        positional: "DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF",
        options: &[SETUPS, CAPACITY, HEADER],
        description: BUNDLE_PROOF,
    },
];
fn command(name: &str) -> Option<&'static Command> {
    COMMANDS.iter().find(|command| command.name == name)
}
fn help() -> String {
    let mut text = "zkc — compile and execute zero-knowledge protocols\n\nUsage: zkc COMMAND [ARGUMENTS]\n\nCommands:\n".to_owned();
    for command in COMMANDS {
        text.push_str(&format!("  {:<24} {}\n", command.name, command.summary));
    }
    text.push_str("\nOptions:\n  -h, --help                Show help\n  --version                 Show the package version\n\nUse 'zkc COMMAND --help' for arguments; use zkc-compile for direct IR.\nDocumentation: https://github.com/zkcompiler/zkc/tree/main/docs\n");
    text
}

/// Handle discovery without opening inputs or starting execution.
pub fn discover(args: &[String]) -> Option<i32> {
    match args {
        [] => {
            eprint!("{}", help());
            Some(2)
        }
        [option] if option == "--help" || option == "-h" => {
            print!("{}", help());
            Some(0)
        }
        [option] if option == "--version" => {
            println!("zkc {}", env!("CARGO_PKG_VERSION"));
            Some(0)
        }
        [name, ..] if command(name).is_none() => {
            eprintln!("Unknown command '{name}'. Run zkc --help for commands.");
            Some(2)
        }
        [name, rest @ ..]
            if rest
                .iter()
                .take_while(|s| s.as_str() != "--")
                .any(|s| s == "--help" || s == "-h") =>
        {
            print!("{}", command(name).unwrap().help());
            Some(0)
        }
        _ => None,
    }
}

/// Run a named command without process exit or printing. Structural argument
/// errors are reported before file access, with a stable code and a message.
pub fn run(name: &str, args: &[String]) -> serde_json::Value {
    let Some(spec) = command(name) else {
        return serde_json::json!({"status":"refused", "phase":"arguments", "code":"unknown-command"});
    };
    let args = match spec.parse(args) {
        Ok(args) => args,
        Err(error) => {
            let format = match name {
                "compile" => "zkc.entry-build/0",
                "inspect" => "zkc.entry-inspection/0",
                "run-bundle" => "zkc.bundle-result/0",
                "prove-bundle" | "verify-bundle" => "zkc.native-proof-run/0",
                _ => "zkc.entry-result/0",
            };
            return serde_json::json!({"format":format, "status":"refused", "phase":"arguments",
                "code":error.code, "message":error.message});
        }
    };
    match name {
        "run-bundle" => crate::run::cli::run(&args),
        "prove-bundle" | "verify-bundle" => crate::proof::cli::run(name == "prove-bundle", &args),
        _ => crate::entry::cli::run(name, &args),
    }
}
/// Successful exit requires the requested operation and all requested publications.
pub fn succeeded(report: &serde_json::Value) -> bool {
    if report["format"] == "zkc.bundle-result/0" {
        report["status"] == "executed" && report["outcome"][0] == "completed"
    } else {
        crate::entry::cli::succeeded(report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|s| (*s).into()).collect()
    }

    #[test]
    fn argument_errors_are_consistent_and_precede_io() {
        for spec in COMMANDS {
            let report = run(spec.name, &[]);
            assert_eq!(report["phase"], "arguments", "{}", spec.name);
            assert_eq!(report["code"], "cli-usage");
            assert!(report["message"].is_string());
            let report = run(spec.name, &args(&["--unknown=missing"]));
            assert_eq!(report["code"], "cli-option");
            assert_eq!(report["phase"], "arguments");
        }
    }
    #[test]
    fn flags_values_duplicates_and_producer_options_are_checked_once() {
        let prove = command("prove").unwrap();
        for options in [
            vec!["--allow-header-only="],
            vec!["--results"],
            vec!["--results="],
            vec!["--attempts=3", "--attempts=4"],
            vec!["--attempt-policy=p"],
            vec!["--setups=missing", "--attempts=x"],
            vec!["--attempts=18446744073709551616"],
        ] {
            let mut values = vec!["p", "h", "i", "o"];
            values.extend(options);
            assert_eq!(
                prove.parse(&args(&values)).err().unwrap().code,
                "cli-option"
            );
        }
        for name in ["verify", "verify-bundle"] {
            assert!(!command(name).unwrap().help().contains("--attempt"));
            assert_eq!(
                run(name, &args(&["p", "h", "i", "o", "--attempts=3"]))["code"],
                "cli-option"
            );
        }
        let values = args(&["--results=out", "p", "h", "i", "o", "--allow-header-only"]);
        assert_eq!(
            prove.parse(&values).unwrap().positional,
            ["p", "h", "i", "o"]
        );
        let values = args(&["--", "-p", "h"]);
        assert_eq!(
            command("inspect")
                .unwrap()
                .parse(&values)
                .unwrap()
                .positional,
            ["-p", "h"]
        );
    }
    #[test]
    fn evaluator_manifests_are_not_accepted_on_the_entry_path() {
        for (name, positional) in [
            ("run", vec!["p", "h", "i"]),
            ("prove", vec!["p", "h", "i", "o"]),
            ("verify", vec!["p", "h", "i", "o"]),
        ] {
            assert!(!command(name).unwrap().help().contains("--evaluators"));
            let mut values = positional;
            values.push("--evaluators=assets.json");
            let report = run(name, &args(&values));
            assert_eq!(report["code"], "cli-option", "{name}");
            assert_eq!(report["phase"], "arguments");
        }
    }
    #[test]
    fn compile_requires_selection_and_allows_repeated_sources() {
        let compile = command("compile").unwrap();
        let values = args(&[
            "--entry=a::E",
            "--module=a=a.zkc",
            "--module=b=b.zkc",
            "--output=p",
        ]);
        assert!(compile.parse(&values).is_ok());
        assert_eq!(compile.parse(&values[..3]).err().unwrap().code, "cli-usage");
    }
    #[test]
    fn removed_commands_are_not_aliases() {
        for name in ["run-entry", "produce-native-proof", "validate-native-proof"] {
            assert!(command(name).is_none());
            assert_eq!(run(name, &[])["code"], "unknown-command");
        }
    }
}
