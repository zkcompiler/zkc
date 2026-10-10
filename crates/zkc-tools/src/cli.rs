//! Command discovery and argument admission for source, Entry and bundle tools.
mod arguments;
mod render;
pub(crate) use arguments::Arguments;
use arguments::{Command, OptionSpec as Opt};
pub use render::human;

const SETUPS: Opt = Opt::new("--setups=AUTHORITY");
const CAPACITY: Opt = Opt::new("--capacity=LIMITS");
const HEADER: Opt = Opt::new("--allow-header-only");
const RESULTS: Opt = Opt::new("--results=FILE");
const BUNDLE_PROOF: &str = "DEPLOYMENT is zkc-compile protocol-proof output. EXPECTED_SHA256 must come from\ntrusted compilation or deployment configuration. INPUTS supplies public bindings\nand one role's invocation values. Authored transcripts require --allow-header-only.";
// Source and pinned package modes share spelling, but cannot be combined.
macro_rules! entry_options {
    (@inspection $($extra:expr),* $(,)?) => {
        &[
            Opt::new("--project=FILE"),
            Opt::new("--module=MODULE=FILE.zkc").repeated(),
            Opt::new("--asset=NAME=FORMAT=FILE").repeated(),
            Opt::new("--compiler=PATH"),
            Opt::new("--package=FILE"),
            Opt::new("--sha256=PIN").hex(Some(32)),
            $($extra),*
        ]
    };
    ($($extra:expr),* $(,)?) => {
        entry_options!(@inspection Opt::new("--no-simplify"),
            Opt::new("--release-storage"), $($extra),*)
    };
}
const ENTRY: &str = "Select ENTRY by unique short or qualified name. With no name, execution selects the\nsole Entry of the required kind. Use project discovery, --project or explicit modules.\nPinned execution uses --package and --sha256 together and no source options.\nProject inputs default to inputs/<qualified.name>/. Proofs default to
build/zkc/<qualified.name>.zkproof; run results use .results.json. Explicit paths win.
Outside a project, input and proof paths must be explicit unless the input group is empty.
Run sessions are generated when omitted. Use run --no-results to skip result publication.";
const COMMANDS: &[Command] = &[
    Command {
        name: "check",
        summary: "Check source definitions and optionally a selected Entry",
        positional: "[ENTRY]",
        options: &[
            Opt::new("--project=FILE"),
            Opt::new("--module=MODULE=FILE.zkc").repeated(),
            Opt::new("--asset=NAME=FORMAT=FILE").repeated(),
            Opt::new("--declarations"),
            Opt::new("--notations"),
            Opt::new("--notation-private"),
            Opt::new("--notation-installation"),
            Opt::new("--compiler=PATH"),
        ],
        description:
            "Use the nearest zkc.toml, --project=FILE, or explicit modules/assets.
All definitions are checked; ENTRY also checks closure and Protocol IR correspondence.
Select an Entry by unique short name or qualified module::Name. The report lists Entries.
--declarations reports completed public callable contracts.
--notations reports diagnostic syntax metadata. Add --notation-private for local/private
records or --notation-installation for installation records; both require --notations.
Syntax metadata is not a native interface. Named-call views are tooling aids,
not capture-preserving rewrites.\nChecking does not execute the protocol or establish its security.",
    },
    Command {
        name: "compile",
        summary: "Compile .zkc source to an authenticated Entry package",
        positional: "[ENTRY]",
        options: &[
            Opt::new("--module=MODULE=FILE.zkc").repeated(),
            Opt::new("--project=FILE"),
            Opt::new("--output=PACKAGE"),
            Opt::new("--compiler=PATH"),
            Opt::new("--asset=NAME=FORMAT=FILE").repeated(),
            Opt::new("--no-simplify"),
            Opt::new("--release-storage"),
        ],
        description: "Use the nearest zkc.toml, --project=FILE, or explicit modules/assets.\nENTRY is a unique short or qualified name; omit it only when there is one Entry.\nProject output defaults to build/zkc/<qualified.name>.zkpkg beside the manifest.\nExplicit modules require --output. Compilation trusts the selected compiler and source. The report supplies the\nexact package SHA-256 for deployment configuration. Modules and assets may repeat.",
    },
    Command {
        name: "new",
        summary: "Create a project in a new directory",
        positional: "DIRECTORY",
        options: &[Opt::new("--compiler=PATH")],
        description: "Create a minimal source project and its input templates. The directory must not exist.",
    },
    Command {
        name: "init",
        summary: "Initialize a project in an existing directory",
        positional: "[DIRECTORY]",
        options: &[Opt::new("--compiler=PATH")],
        description: "Initialize the current or selected directory with source and input templates.
Existing projects and conflicting files refuse; use prepare for an existing project.",
    },
    Command {
        name: "prepare",
        summary: "Prepare missing input templates for project Entries",
        positional: "[ENTRY]",
        options: &[Opt::new("--project=FILE"), Opt::new("--compiler=PATH")],
        description: "Prepare all declared Entries, or one selected Entry. Repeated calls preserve existing files.
Values, dynamic lengths and variant cases must be filled by the user.
Use inputs check to validate existing input contents; no protocol is executed.",
    },
    Command {
        name: "inspect",
        summary: "Show a checked Entry interface and input schema",
        positional: "[ENTRY]",
        options: entry_options!(@inspection),
        description: ENTRY,
    },
    Command {
        name: "inputs init",
        summary: "Generate empty input templates for one Entry",
        positional: "[ENTRY]",
        options: entry_options!(@inspection Opt::new("--output=DIRECTORY")),
        description: "Create only required files under inputs/<qualified.name>/ in a project.\nPackage and explicit-module modes require --output. Existing files are never replaced.\nNull placeholders need values; no witness, dynamic length or variant is invented.",
    },
    Command {
        name: "inputs check",
        summary: "Prepare invocation inputs without execution",
        positional: "[ENTRY]",
        options: entry_options!(
            Opt::new("--operation=run|prove|verify"),
            Opt::new("--session=LABEL"),
            Opt::new("--input=ROLE=FILE").repeated(),
            Opt::new("--public=FILE"),
            Opt::new("--witness=FILE"),
            Opt::new("--service=ROLE.NAME=COUNT").unsigned().repeated(),
            Opt::new("--key=SLOT=FILE").repeated(),
            Opt::new("--context=HEX").hex(None),
            Opt::new("--transcript-budget=COUNT").unsigned(),
            SETUPS,
            CAPACITY,
            HEADER,
            Opt::new("--limits=LIMITS"),
            Opt::new("--attempts=COUNT").unsigned(),
        ),
        description: "--operation is required. Apply the same inputs and policies as execution.\nChecks setup material and native inputs; issues no resources and executes no protocol.\nVerification checks never open witness data or proof bytes.",
    },
    Command {
        name: "run",
        summary: "Compile and execute a run Entry",
        positional: "[ENTRY]",
        options: entry_options!(
            Opt::new("--session=LABEL"),
            Opt::new("--input=ROLE=FILE").repeated(),
            Opt::new("--service=ROLE.NAME=COUNT").unsigned().repeated(),
            Opt::new("--key=SLOT=FILE").repeated(),
            SETUPS,
            CAPACITY,
            Opt::new("--limits=LIMITS"),
            RESULTS,
            Opt::new("--no-results"),
        ),
        description: ENTRY,
    },
    Command {
        name: "prove",
        summary: "Compile a proof Entry and produce a proof",
        positional: "[ENTRY]",
        options: entry_options!(
            Opt::new("--public=FILE"),
            Opt::new("--witness=FILE"),
            Opt::new("--output=PROOF"),
            Opt::new("--service=ROLE.NAME=COUNT").unsigned().repeated(),
            Opt::new("--key=SLOT=FILE").repeated(),
            Opt::new("--context=HEX").hex(None),
            Opt::new("--transcript-budget=COUNT").unsigned(),
            SETUPS,
            CAPACITY,
            HEADER,
            Opt::new("--attempts=COUNT").unsigned(),
            RESULTS,
        ),
        description: ENTRY,
    },
    Command {
        name: "verify",
        summary: "Verify a proof with independently supplied public inputs",
        positional: "[ENTRY]",
        options: entry_options!(
            Opt::new("--public=FILE"),
            Opt::new("--proof=FILE"),
            Opt::new("--service=ROLE.NAME=COUNT").unsigned().repeated(),
            Opt::new("--key=SLOT=FILE").repeated(),
            Opt::new("--context=HEX").hex(None),
            Opt::new("--transcript-budget=COUNT").unsigned(),
            SETUPS,
            CAPACITY,
            HEADER,
            RESULTS,
        ),
        description: ENTRY,
    },
    Command {
        name: "bindings",
        summary: "Generate Rust data bindings pinned to an Entry",
        positional: "[ENTRY]",
        options: entry_options!(Opt::new("--output=FILE.rs")),
        description: "Generate typed inputs and an admission helper for the compiled package.\nProtocol execution uses the common Entry Host.",
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
    text.push_str("\nOptions:\n  -h, --help                Show help\n  --version                 Show the package version\n  --json                    Print a structured command report\n\nUse 'zkc COMMAND --help' for arguments; use zkc-compile for direct IR.\nDocumentation: https://github.com/zkcompiler/zkc/tree/main/docs\n");
    text
}

/// Handle discovery without opening inputs or starting execution.
pub fn discover(args: &[String]) -> Option<i32> {
    if args.first().is_some_and(|s| s == "inputs") {
        if args.len() == 1 || args[1] == "--help" || args[1] == "-h" {
            println!(
                "Usage: zkc inputs init|check [ENTRY] [OPTIONS]\nUse zkc inputs COMMAND --help for details."
            );
            return Some(if args.len() == 1 { 2 } else { 0 });
        }
        let mut flattened = vec![format!("inputs {}", args[1])];
        flattened.extend_from_slice(&args[2..]);
        return discover(&flattened);
    }
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
        [name, ..] if name != "inputs" && command(name).is_none() => {
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
    if name == "inputs" {
        let Some((subcommand, rest)) = args.split_first() else {
            return serde_json::json!({"status":"refused","phase":"arguments","code":"cli-usage"});
        };
        return run(&format!("inputs {subcommand}"), rest);
    }
    let Some(spec) = command(name) else {
        return serde_json::json!({"status":"refused", "phase":"arguments", "code":"unknown-command"});
    };
    let mut args = match spec.parse(args) {
        Ok(args) => args,
        Err(error) => {
            let format = match name {
                "compile" => "zkc.entry-build/0",
                "check" => "zkc.source-check/0",
                "inspect" => "zkc.entry-inspection/0",
                "init" | "new" | "prepare" | "inputs init" => "zkc.project-init/0",
                "run-bundle" => "zkc.bundle-result/0",
                "prove-bundle" | "verify-bundle" => "zkc.native-proof-run/0",
                _ => "zkc.entry-result/0",
            };
            return serde_json::json!({"format":format, "status":"refused", "phase":"arguments",
                "code":error.code, "message":error.message});
        }
    };
    // Presentation is shared by all commands; execution adapters only receive
    // options that affect the requested operation.
    args.options.retain(|(key, _)| *key != "--json");
    if name == "check"
        && !args.options.iter().any(|(name, _)| *name == "--notations")
        && args
            .options
            .iter()
            .any(|(name, _)| matches!(*name, "--notation-private" | "--notation-installation"))
    {
        return serde_json::json!({"format":"zkc.source-check/0", "status":"refused",
            "phase":"arguments", "code":"cli-option",
            "message":"notation visibility options require --notations"});
    }
    match name {
        "compile" | "check" => crate::project::cli::run(name, &args),
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
        matches!(
            report["status"].as_str(),
            Some(
                "checked"
                    | "compiled"
                    | "inspected"
                    | "executed"
                    | "produced"
                    | "accepted"
                    | "generated"
                    | "initialized"
                    | "prepared"
                    | "inputs-checked"
            )
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|s| (*s).into()).collect()
    }

    #[test]
    fn notation_flags_are_check_only_unique_and_require_the_inventory() {
        let check = command("check").unwrap();
        assert!(check.parse(&args(&["--notations"])).is_ok());
        let values = args(&[
            "--notations",
            "--notation-private",
            "--notation-installation",
        ]);
        let parsed = check.parse(&values).unwrap();
        assert_eq!(parsed.options.len(), 3);
        for flag in [
            "--notations",
            "--notation-private",
            "--notation-installation",
        ] {
            assert_eq!(run("compile", &args(&[flag]))["code"], "cli-option");
            assert_eq!(run("check", &args(&[flag, flag]))["code"], "cli-option");
            assert_eq!(
                run("check", &[format!("{flag}=true")])["code"],
                "cli-option"
            );
            assert_eq!(run("check", &[format!("{flag}=")])["code"], "cli-option");
        }
        for flag in ["--notation-private", "--notation-installation"] {
            let report = run("check", &args(&[flag, "--project=does-not-exist.toml"]));
            assert_eq!(report["code"], "cli-option");
            assert_eq!(report["phase"], "arguments");
        }
    }

    #[test]
    fn argument_errors_are_consistent_and_precede_io() {
        for spec in COMMANDS {
            let invalid = args(&["one", "two", "three", "four", "five"]);
            let report = run(spec.name, &invalid);
            assert_eq!(report["phase"], "arguments", "{}", spec.name);
            assert_eq!(report["code"], "cli-usage");
            assert!(report["message"].is_string());
            let report = run(spec.name, &args(&["--unknown=missing"]));
            assert_eq!(report["code"], "cli-option");
            assert_eq!(report["phase"], "arguments");
        }
        for option in [
            "--module=foo",
            "--asset=a=b",
            "--service=P.x=abc",
            "--context=zz",
            "--sha256=bad",
        ] {
            let report = run("prove", &args(&["--project=/missing/zkc.toml", option]));
            assert_eq!(report["phase"], "arguments", "{option}");
            assert_eq!(report["code"], "cli-option", "{option}");
        }
        for name in ["inspect", "inputs init"] {
            assert!(!command(name).unwrap().help().contains("--no-simplify"));
            assert!(!command(name).unwrap().help().contains("--release-storage"));
        }
        assert_eq!(
            run("init", &args(&["--unknown"]))["format"],
            "zkc.project-init/0"
        );
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
        let values = args(&["--results=out", "Example", "--allow-header-only"]);
        assert_eq!(prove.parse(&values).unwrap().positional, ["Example"]);
        let values = args(&["--", "-p"]);
        assert_eq!(
            command("inspect")
                .unwrap()
                .parse(&values)
                .unwrap()
                .positional,
            ["-p"]
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
    fn compile_accepts_optional_selection_and_repeated_sources() {
        let compile = command("compile").unwrap();
        let values = args(&["a::E", "--module=a=a.zkc", "--module=b=b.zkc", "--output=p"]);
        assert!(compile.parse(&values).is_ok());
        assert!(compile.parse(&values[..3]).is_ok());
        assert!(compile.parse(&args(&[])).is_ok());
        assert_eq!(
            compile.parse(&args(&["one", "two"])).err().unwrap().code,
            "cli-usage"
        );
        assert_eq!(
            compile.parse(&args(&["--entry=a::E"])).err().unwrap().code,
            "cli-option"
        );
    }
    #[test]
    fn removed_commands_are_not_aliases() {
        for name in ["run-entry", "produce-native-proof", "validate-native-proof"] {
            assert!(command(name).is_none());
            assert_eq!(run(name, &[])["code"], "unknown-command");
        }
    }
}
