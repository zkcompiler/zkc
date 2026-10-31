//! Command discovery and argument admission for source, Entry and bundle tools.
mod arguments;
mod render;
pub(crate) use arguments::Arguments;
use arguments::{Command, OptionSpec as Opt};
pub use render::human;

const SETUPS: Opt = Opt::new("--setups=AUTHORITY");
const CAPACITY: Opt = Opt::new("--capacity=LIMITS");
const THREADS: Opt = Opt::new("--threads=COUNT").unsigned_range(1, 256);
const AUTHORED: Opt = Opt::new("--allow-authored");
const RESULTS: Opt = Opt::new("--results=FILE");
const INVOCATIONS: Opt = Opt::new("--invocations=FILE");
const BUNDLE_PROOF: &str = "DEPLOYMENT is zkc-compile protocol-proof output. EXPECTED_SHA256 must come from\ntrusted compilation or deployment configuration. INPUTS supplies public bindings\nand one role's invocation values. Authored transcripts require --allow-authored.\n--threads=COUNT selects 1..=256 shared CPU workers (default: 1).";
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
        entry_options!(@inspection Opt::new("--report=DIRECTORY"), Opt::new("--dump=PHASES"), Opt::new("--cache=DIRECTORY"), Opt::new("--profile=NAME"), Opt::new("--no-simplify"),
            Opt::new("--release-storage"), Opt::new("--fuse-vector-reductions"), Opt::new("--fuse-collect-fold"), Opt::new("--no-finite-bulk"),
            Opt::new("--no-calculation-batching"), Opt::new("--oracle-realization=JSON"), $($extra),*)
    };
}
const ENTRY: &str = "Select ENTRY by unique short or qualified name. With no name, execution selects the\nsole Entry of the required kind. Use project discovery, --project or explicit modules.
Generic protocol runs take closed arguments, e.g. 'Schnorr<G>'. Proofs require a proof declaration.
Pinned execution uses --package and --sha256 together and no source options.
Project inputs default to inputs/<entry-stem>/. Proofs default to
build/zkc/<entry-stem>.zkproof; run results use .results.json. Explicit paths win.
Named Entry stems replace :: with dots; generic runs append a full selector digest.
Outside a project, input and proof paths must be explicit unless the input group is empty.
Function arguments use one parameter-named arguments.json map. Static child context
uses --invocations=FILE with exact deployment IDs. Use run --no-results to skip result publication.
--threads=COUNT selects 1..=256 shared CPU workers (default: 1), including with --dry-run.
Dry-run validates inputs without executing numerical work.";
const COMMANDS: &[Command] = &[
    Command {
        name: "test", summary: "Run manifest test recipes through ordinary consumer Entries", positional: "[TEST]",
        options: &[Opt::new("--project=FILE"), Opt::new("--compiler=PATH"), Opt::new("--profile=NAME"), Opt::new("--report=DIRECTORY")],
        description: "Run all root [test.NAME] recipes, or one named recipe. Expected failures match exact diagnostic codes. Compilation and execution use the ordinary checked CLI/Host.",
    },
    Command {
        name: "check",
        summary: "Check source definitions and optionally a selected Entry",
        positional: "[ENTRY]",
        options: &[
            Opt::new("--project=FILE"),
            Opt::new("--module=MODULE=FILE.zkc").repeated(),
            Opt::new("--asset=NAME=FORMAT=FILE").repeated(),
            Opt::new("--report=DIRECTORY"),
            Opt::new("--compiler=PATH"),
        ],
        description:
            "Use the nearest zkc.toml, --project=FILE, or explicit modules/assets.
All definitions are checked; ENTRY also checks closure and Protocol IR correspondence.
Select an Entry by unique short name or qualified module::Name, with closed arguments
for generic runs, e.g. 'Schnorr<G>'. Discovery does not enumerate generic instances.
Use inspect for API, placement and notation inventories.\nChecking does not execute the protocol or establish its security.",
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
            Opt::new("--report=DIRECTORY"), Opt::new("--dump=PHASES"), Opt::new("--cache=DIRECTORY"), Opt::new("--profile=NAME"), Opt::new("--no-simplify"),
            Opt::new("--release-storage"),
            Opt::new("--fuse-vector-reductions"), Opt::new("--fuse-collect-fold"), Opt::new("--no-finite-bulk"),
            Opt::new("--no-calculation-batching"), Opt::new("--oracle-realization=JSON"),
        ],
        description: "Use the nearest zkc.toml, --project=FILE, or explicit modules/assets.\nENTRY is a unique short or qualified name; omit it only when there is one Entry.
Select generic runs with closed arguments, e.g. 'Schnorr<G>'.
Project output defaults to build/zkc/<entry-stem>.zkpkg beside the manifest.
Named Entry stems replace :: with dots; generic runs append a full selector digest.
Explicit modules require --output. Compilation trusts the selected compiler and source. The report supplies the\nexact package SHA-256 for deployment configuration. Modules and assets may repeat.",
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
        summary: "Prepare missing input templates",
        positional: "[ENTRY]",
        options: entry_options!(@inspection Opt::new("--output=DIRECTORY")),
        description: "Prepare all project Entries, or one selected Entry. Explicit --output selects one Entry.
Generic protocols require an explicit selector with closed arguments, e.g. 'Schnorr<G>'.
Package and explicit-module modes require --output. Existing regular files are preserved.
Values, dynamic lengths and variant cases must be filled by the user.
Use run, prove or verify --dry-run to validate inputs without protocol execution.",
    },
    Command {
        name: "inspect",
        summary: "Show a checked Entry interface and input schema",
        positional: "[ENTRY]",
        options: entry_options!(@inspection Opt::new("--view=entry|project|api|placement|notations|toolchain"), Opt::new("--profile=NAME"), Opt::new("--notation-private"), Opt::new("--notation-installation")),
        description: "Inspect the selected Entry by default; other views show project, API, completed callable
placement, notation or toolchain metadata. Notation visibility options require --view=notations.
Select generic runs with closed arguments, e.g. 'Schnorr<G>'.
Source inventories check definitions and optionally a selected Entry; they do not execute it.
Pinned packages support only the Entry view.",
    },
    Command {
        name: "run",
        summary: "Compile and execute an Entry function",
        positional: "[ENTRY]",
        options: entry_options!(
            THREADS,
            Opt::new("--instrument=counts"),
            Opt::new("--dry-run"),
            Opt::new("--input=FILE"),
            INVOCATIONS,
            AUTHORED,
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
            THREADS,
            Opt::new("--instrument=counts"),
            Opt::new("--dry-run"),
            Opt::new("--public=FILE"),
            Opt::new("--witness=FILE"),
            Opt::new("--output=PROOF"),
            Opt::new("--service=ROLE.NAME=COUNT").unsigned().repeated(),
            Opt::new("--key=SLOT=FILE").repeated(),
            Opt::new("--context=HEX").hex(None),
            Opt::new("--transcript-budget=COUNT").unsigned(),
            Opt::new("--external-work=COUNT").unsigned(),
            SETUPS,
            CAPACITY,
            AUTHORED,
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
            THREADS,
            Opt::new("--instrument=counts"),
            Opt::new("--dry-run"),
            Opt::new("--public=FILE"),
            Opt::new("--proof=FILE"),
            Opt::new("--service=ROLE.NAME=COUNT").unsigned().repeated(),
            Opt::new("--key=SLOT=FILE").repeated(),
            Opt::new("--context=HEX").hex(None),
            Opt::new("--transcript-budget=COUNT").unsigned(),
            Opt::new("--external-work=COUNT").unsigned(),
            SETUPS,
            CAPACITY,
            AUTHORED,
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
        name: "bundle run",
        summary: "Execute an authenticated run bundle",
        positional: "BUNDLE EXPECTED_SHA256 INPUTS",
        options: &[SETUPS, CAPACITY, THREADS, Opt::new("--limits=LIMITS")],
        description: "BUNDLE is protocol-bundle output; INPUTS is a zkc.bundle-inputs/0 array.\nEXPECTED_SHA256 comes from trusted compilation or deployment configuration.\nCompleted execution does not interpret protocol acceptance outputs.\n--threads=COUNT selects 1..=256 shared CPU workers (default: 1).",
    },
    Command {
        name: "bundle prove",
        summary: "Produce a proof from a pinned deployment",
        positional: "DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF",
        options: &[SETUPS, Opt::new("--attempt-policy=FILE"), CAPACITY, THREADS, AUTHORED],
        description: BUNDLE_PROOF,
    },
    Command {
        name: "bundle verify",
        summary: "Verify a proof with a pinned deployment",
        positional: "DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF",
        options: &[SETUPS, CAPACITY, THREADS, AUTHORED],
        description: BUNDLE_PROOF,
    },
];
fn command(name: &str) -> Option<&'static Command> {
    COMMANDS.iter().find(|command| command.name == name)
}
fn help() -> String {
    let mut text = "zkc — compile and execute zero-knowledge protocols\n\nUsage: zkc COMMAND [ARGUMENTS]\n\nCommands:\n".to_owned();
    for command in COMMANDS
        .iter()
        .filter(|command| !command.name.contains(' '))
    {
        text.push_str(&format!("  {:<24} {}\n", command.name, command.summary));
    }
    text.push_str("  bundle                   Execute lower-level authenticated bundles (run, prove, verify)\n");
    text.push_str("\nOptions:\n  -h, --help                Show help\n  --version                 Show the package version\n  --json                    Print a structured command report\n\nUse 'zkc COMMAND --help' for arguments; use zkc-compile for direct IR.\nDocumentation: https://github.com/zkcompiler/zkc/tree/main/docs\n");
    text
}

/// Handle discovery without opening inputs or starting execution.
pub fn discover(args: &[String]) -> Option<i32> {
    if args.first().is_some_and(|s| s == "bundle") {
        if args.len() == 1 || args[1] == "--help" || args[1] == "-h" {
            println!(
                "Usage: zkc bundle run|prove|verify [ARGUMENTS]\nUse zkc bundle COMMAND --help for details."
            );
            return Some(if args.len() == 1 { 2 } else { 0 });
        }
        let mut flattened = vec![format!("bundle {}", args[1])];
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
    if name == "bundle" {
        let Some((subcommand, rest)) = args.split_first() else {
            return serde_json::json!({"status":"refused","phase":"arguments","code":"cli-usage"});
        };
        return run(&format!("bundle {subcommand}"), rest);
    }
    let Some(spec) = command(name) else {
        return serde_json::json!({"status":"refused", "phase":"arguments", "code":"unknown-command"});
    };
    let mut args = match spec.parse(args) {
        Ok(args) => args,
        Err(error) => {
            let format = match name {
                "test" => "zkc.project-tests/0",
                "compile" => "zkc.entry-build/0",
                "check" => "zkc.source-check/0",
                "inspect" => "zkc.entry-inspection/0",
                "init" | "new" | "prepare" => "zkc.project-init/0",
                "bundle run" => "zkc.bundle-result/0",
                "bundle prove" | "bundle verify" => "zkc.native-proof-run/0",
                _ => "zkc.entry-result/0",
            };
            return serde_json::json!({"format":format, "status":"refused", "phase":"arguments",
                "code":error.code, "message":error.message});
        }
    };
    // Presentation is shared by all commands; execution adapters only receive
    // options that affect the requested operation.
    args.options.retain(|(key, _)| *key != "--json");
    if args
        .options
        .iter()
        .any(|(name, _)| matches!(*name, "--notation-private" | "--notation-installation"))
        && args.value("--view") != Some("notations")
    {
        return serde_json::json!({"format":"zkc.tool-inspection/0", "status":"refused",
            "phase":"arguments", "code":"cli-option",
            "message":"notation visibility options require --view=notations"});
    }
    if args.has("--dry-run") && args.has("--instrument") {
        return serde_json::json!({"status":"refused", "phase":"arguments", "code":"cli-option",
            "message":"--dry-run does not execute; remove --instrument"});
    }
    if let Some(instrument) = args.value("--instrument")
        && (instrument != "counts" || !zkc::EXECUTION_COUNTS_ENABLED)
    {
        return serde_json::json!({"status":"refused","phase":"arguments","code":"instrument-unavailable"});
    }
    // Include worker readiness and report-directory preparation in the command
    // observation. Argument parsing precedes this boundary; publication follows it.
    let started = std::time::Instant::now();
    let cpu = if matches!(
        name,
        "run" | "prove" | "verify" | "bundle run" | "bundle prove" | "bundle verify"
    ) {
        let result = match args.value("--threads") {
            Some(count) => {
                zkc::execution::CpuExecution::new(count.parse().expect("validated threads"))
            }
            None => zkc::execution::CpuExecution::serial(),
        };
        match result {
            Ok(cpu) => Some(cpu),
            Err(error) => {
                return serde_json::json!({"status":"refused","phase":"arguments","code":error.to_string()});
            }
        }
    } else {
        None
    };
    let directory = match args
        .value("--report")
        .map(crate::project::observation::ReportDirectory::create)
        .transpose()
    {
        Ok(directory) => directory,
        Err(code) => {
            return serde_json::json!({"status":"refused","phase":"observation","code":code});
        }
    };
    let dispatch = || match name {
        "test" => crate::project::testing::run(&args),
        "inspect" if args.value("--view").is_some_and(|view| view != "entry") => {
            crate::project::cli::inspect(&args)
        }
        "compile" | "check" => crate::project::cli::run(name, &args),
        "bundle run" => crate::run::cli::run(&args, cpu.as_ref().expect("execution command")),
        "bundle prove" | "bundle verify" => crate::proof::cli::run(
            name == "bundle prove",
            &args,
            cpu.as_ref().expect("execution command"),
        ),
        _ => crate::entry::cli::run(name, &args, cpu.as_ref()),
    };
    // Keep validation, file effects and VM control on the caller while imports
    // and numerical leaves can find the command's explicitly owned context.
    let mut report = match &cpu {
        Some(cpu) => cpu.enter(dispatch),
        None => dispatch(),
    };
    if let Some(cpu) = cpu {
        report["cpu"] = serde_json::json!({"workers":cpu.workers()});
    }
    if directory.is_some() || args.has("--instrument") {
        report["command_microseconds"] = serde_json::json!(started.elapsed().as_micros());
        report["measurement"] = serde_json::json!({"clock":"wall","inclusive":true,"instrument":args.value("--instrument"),"counts_build":zkc::EXECUTION_COUNTS_ENABLED});
    }
    if let Some(directory) = directory
        && let Err(code) = directory.publish(&mut report)
    {
        report["report_error"] = serde_json::json!(code);
    }
    report
}
/// Successful exit requires the requested operation and all requested publications.
pub fn succeeded(report: &serde_json::Value) -> bool {
    if report.get("report_error").is_some() {
        return false;
    }
    if report["format"] == "zkc.bundle-result/0" {
        report["status"] == "executed" && report["outcome"][0] == "completed"
    } else {
        matches!(
            report["status"].as_str(),
            Some(
                "tested"
                    | "checked"
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
    fn threads_surface_is_exact_bounded_and_available_for_execution_dry_runs() {
        let execution = [
            "run",
            "prove",
            "verify",
            "bundle run",
            "bundle prove",
            "bundle verify",
        ];
        for spec in COMMANDS {
            let positional = match spec.name {
                "bundle run" => args(&["bundle", "pin", "inputs"]),
                "bundle prove" | "bundle verify" => args(&["deployment", "pin", "inputs", "proof"]),
                _ => vec![],
            };
            if !execution.contains(&spec.name) {
                assert!(!spec.help().contains("--threads"), "{}", spec.name);
                assert_eq!(
                    run(spec.name, &args(&["--threads=2"]))["code"],
                    "cli-option"
                );
                continue;
            }
            assert!(spec.help().contains("--threads=COUNT"));
            assert!(spec.help().contains("1..=256"));
            assert!(spec.help().contains("default: 1"));
            for count in ["1", "2", "256"] {
                let mut values = positional.clone();
                values.push(format!("--threads={count}"));
                let parsed = spec.parse(&values).unwrap();
                assert_eq!(parsed.value("--threads"), Some(count));
            }
            for invalid in [
                vec!["--threads=0"],
                vec!["--threads=257"],
                vec!["--threads=18446744073709551616"],
                vec!["--threads=-1"],
                vec!["--threads=+1"],
                vec!["--threads=1.0"],
                vec!["--threads= 2"],
                vec!["--threads=auto"],
                vec!["--threads="],
                vec!["--threads"],
                vec!["--threads", "2"],
                vec!["--threads=1", "--threads=2"],
                vec!["--workers=2"],
                vec!["--thread-count=2"],
                vec!["-j=2"],
            ] {
                let mut values = positional.clone();
                values.extend(invalid.into_iter().map(String::from));
                let report = run(spec.name, &values);
                assert_eq!(
                    report["code"], "cli-option",
                    "{}: {values:?}: {report}",
                    spec.name
                );
                assert_eq!(report["phase"], "arguments");
                assert!(report.get("cpu").is_none());
            }
        }
        for name in ["run", "prove", "verify"] {
            let values = args(&["--dry-run", "--threads=2"]);
            let parsed = command(name).unwrap().parse(&values).unwrap();
            assert!(parsed.has("--dry-run"));
            assert_eq!(parsed.value("--threads"), Some("2"));
        }
    }

    #[test]
    fn cpu_worker_report_is_the_configured_context_even_on_execution_refusal() {
        for name in ["run", "prove", "verify"] {
            for (flag, workers) in [(None, 1), (Some("--threads=2"), 2)] {
                let mut values = args(&["--dry-run", "--project=/missing-cpu-test-project"]);
                values.extend(flag.map(String::from));
                let report = run(name, &values);
                assert_eq!(report["cpu"]["workers"], workers, "{report}");
                assert!(human(&report).contains(&format!("CPU workers: {workers}\n")));
            }
        }
    }

    #[test]
    fn function_failure_rendering_uses_each_childs_source_roles() {
        let report = serde_json::json!({"format":"zkc.entry-result/0","status":"refused",
        "code":"entry-host-run-failed","invocation_role_names":{
            "first":{"role00000000":"証明者"},"second":{"role00000000":"検証者"}},
        "execution":{"failure":{"code":"entry-host-run-failed"},"calls":[
            {"target":"first","native":{"roles":[{"role":"role00000000","before":["stopped","require"],"after":["returned"]}]}},
            {"target":"second","native":{"stop":{"role":"role00000000","kind":"require"}}}
        ]}});
        let text = human(&report);
        assert!(text.contains("Invocation first:\nStopped 証明者:"));
        assert!(text.contains("Invocation second:\nStopped 検証者:"));
        assert!(!text.contains("Stopped role00000000:"));
    }

    #[test]
    fn function_inputs_are_single_files_and_child_authority_is_explicit() {
        let spec = command("run").unwrap();
        let values = args(&["--input=arguments.json", "--invocations=context.json"]);
        let parsed = spec.parse(&values).unwrap();
        assert_eq!(parsed.value("--input"), Some("arguments.json"));
        assert_eq!(parsed.value("--invocations"), Some("context.json"));
        let repeated = args(&["--input=a.json", "--input=b.json"]);
        assert_eq!(spec.parse(&repeated).err().unwrap().code, "cli-option");
        assert!(spec.help().contains("--input=FILE"));
        assert!(!spec.help().contains("--input=ROLE=FILE"));
        for removed in [
            "--session=x",
            "--service=P.rng=1",
            "--key=slot=file",
            "--setups=file",
        ] {
            assert_eq!(run("run", &args(&[removed]))["code"], "cli-option");
        }
        for name in ["prove", "verify"] {
            assert_eq!(
                run(name, &args(&["--invocations=context.json"]))["code"],
                "cli-option"
            );
        }
        for flag in [
            "--public=x",
            "--witness=x",
            "--session=x",
            "--service=P.rng=1",
        ] {
            let report = run("run", &args(&["--dry-run", flag, "--project=/missing"]));
            assert_eq!(report["code"], "cli-option");
            assert_eq!(report["phase"], "arguments");
        }
    }

    #[test]
    fn inventory_flags_belong_to_inspect_and_require_the_notation_view() {
        let inspect = command("inspect").unwrap();
        let values = args(&[
            "--view=notations",
            "--notation-private",
            "--notation-installation",
        ]);
        assert_eq!(inspect.parse(&values).unwrap().options.len(), 3);
        for flag in [
            "--api",
            "--declarations",
            "--notations",
            "--notation-private",
            "--notation-installation",
        ] {
            assert_eq!(
                run("check", &args(&[flag, "--project=/missing"]))["code"],
                "cli-option"
            );
            assert_eq!(run("compile", &args(&[flag]))["code"], "cli-option");
        }
        for flag in ["--notation-private", "--notation-installation"] {
            for options in [
                args(&[flag, "--project=/missing"]),
                args(&["--view=api", flag, "--project=/missing"]),
            ] {
                let report = run("inspect", &options);
                assert_eq!(report["code"], "cli-option");
                assert_eq!(report["phase"], "arguments");
            }
            assert_eq!(
                inspect.parse(&args(&[flag, flag])).err().unwrap().code,
                "cli-option"
            );
            assert_eq!(
                inspect.parse(&[format!("{flag}=true")]).err().unwrap().code,
                "cli-option"
            );
        }
    }
    #[test]
    fn dry_run_uses_each_operations_options_and_cannot_collect_execution_counts() {
        for name in ["run", "prove", "verify"] {
            let spec = command(name).unwrap();
            assert!(spec.parse(&args(&["--dry-run"])).unwrap().has("--dry-run"));
            for values in [
                args(&["--dry-run=true"]),
                args(&["--dry-run", "--dry-run"]),
                args(&["--operation=run"]),
                args(&["--dry-run", "--instrument=counts", "--project=/missing"]),
            ] {
                let report = run(name, &values);
                assert_eq!(report["code"], "cli-option", "{name}: {report}");
                assert_eq!(report["phase"], "arguments");
            }
        }
        assert_eq!(
            run("verify", &args(&["--dry-run", "--witness=/missing"]))["code"],
            "cli-option"
        );
        assert_eq!(
            run(
                "run",
                &args(&["--dry-run", "--no-results", "--results=/missing"])
            )["code"],
            "cli-option"
        );
    }

    #[test]
    fn argument_errors_are_consistent_and_precede_io() {
        assert_eq!(
            run("test", &args(&["--unknown"]))["format"],
            "zkc.project-tests/0"
        );
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
        for name in ["inspect", "prepare"] {
            assert!(!command(name).unwrap().help().contains("--no-simplify"));
            assert!(!command(name).unwrap().help().contains("--release-storage"));
            assert!(
                !command(name)
                    .unwrap()
                    .help()
                    .contains("--fuse-vector-reductions")
            );
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
            vec!["--allow-authored="],
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
        for name in ["verify", "bundle verify"] {
            assert!(!command(name).unwrap().help().contains("--attempt"));
            assert_eq!(
                run(name, &args(&["p", "h", "i", "o", "--attempts=3"]))["code"],
                "cli-option"
            );
        }
        let values = args(&["--results=out", "Example", "--allow-authored"]);
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
    fn collect_fold_flag_is_unique_valueless_and_requires_source_compilation() {
        for name in ["compile", "run", "prove", "verify", "bindings"] {
            let spec = command(name).unwrap();
            assert!(spec.help().contains("--fuse-collect-fold"), "{name}");
            let values = args(&["--fuse-collect-fold"]);
            assert!(spec.parse(&values).unwrap().has("--fuse-collect-fold"));
            for values in [
                args(&["--fuse-collect-fold=true"]),
                args(&["--fuse-collect-fold=false"]),
                args(&["--fuse-collect-fold="]),
                args(&["--fuse-collect-fold", "--fuse-collect-fold"]),
            ] {
                assert_eq!(
                    spec.parse(&values).err().unwrap().code,
                    "cli-option",
                    "{name}"
                );
            }
            if name != "compile" {
                let report = run(
                    name,
                    &[
                        "--fuse-collect-fold".into(),
                        "--package=/missing/package.zkpkg".into(),
                        format!("--sha256={}", "0".repeat(64)),
                    ],
                );
                assert_eq!(report["code"], "cli-usage", "{name}");
                assert_eq!(report["phase"], "arguments", "{name}");
            }
        }
        for name in ["check", "inspect", "prepare"] {
            let spec = command(name).unwrap();
            assert!(!spec.help().contains("--fuse-collect-fold"));
            assert_eq!(
                spec.parse(&args(&["--fuse-collect-fold"]))
                    .err()
                    .unwrap()
                    .code,
                "cli-option"
            );
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
        for name in [
            "run-entry",
            "produce-native-proof",
            "validate-native-proof",
            "inputs",
            "inputs init",
            "inputs check",
            "run-bundle",
            "prove-bundle",
            "verify-bundle",
        ] {
            assert!(command(name).is_none());
            assert_eq!(run(name, &[])["code"], "unknown-command");
        }
    }
    #[test]
    fn oracle_selection_is_unique_and_only_available_with_source_compilation() {
        let text = zkc::entry::OracleSelection::default()
            .canonical_json()
            .unwrap();
        let flag = format!("--oracle-realization={text}");
        for name in ["compile", "run", "prove", "verify", "bindings"] {
            let spec = command(name).unwrap();
            assert_eq!(
                spec.parse(&[flag.clone()])
                    .unwrap()
                    .value("--oracle-realization"),
                Some(text.as_str())
            );
            for invalid in [
                vec![flag.clone(), flag.clone()],
                args(&["--oracle-realization"]),
                args(&["--oracle-realization="]),
            ] {
                assert_eq!(spec.parse(&invalid).err().unwrap().code, "cli-option");
            }
            if name != "compile" {
                let report = run(
                    name,
                    &[
                        flag.clone(),
                        "--package=/missing.zkpkg".into(),
                        format!("--sha256={}", "0".repeat(64)),
                    ],
                );
                assert_eq!(report["code"], "cli-usage", "{name}");
                assert_eq!(report["phase"], "arguments", "{name}");
            }
        }
        for name in [
            "check",
            "inspect",
            "prepare",
            "bundle run",
            "bundle prove",
            "bundle verify",
        ] {
            assert_eq!(
                command(name)
                    .unwrap()
                    .parse(&[flag.clone()])
                    .err()
                    .unwrap()
                    .code,
                "cli-option",
                "{name}"
            );
        }
    }
}
