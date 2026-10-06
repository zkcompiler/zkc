//! Human-facing discovery, kept separate from machine-readable execution reports.

const HELP: &str = "zkc — execute checked protocol participants and proof artifacts

Usage: zkc COMMAND [ARGUMENTS]

Commands:
  run-bundle                Execute an authenticated native run bundle
  run-protocol              Execute an interactive participant plan
  produce-artifact          Write a proof artifact from producer inputs
  validate-artifact         Verify a proof artifact against validator inputs
  produce-native-proof      Produce a proof from a pinned native deployment
  validate-native-proof     Verify a proof with a pinned native deployment
  inspect-artifact-identity Inspect source and construction identities
  run                       Execute the finite table reference path
  run-physical              Execute a physical table plan

Options:
  -h, --help                Show this help
  --version                 Show the package version

Use 'zkc COMMAND --help' for arguments. Compile .pir sources with zkc-compile.
Start in a prepared checkout with 'just demo'; see docs/getting-started.md.
";

fn command_help(command: &str) -> Option<&'static str> {
    match command {
        "run-bundle" => Some(
            "Usage: zkc run-bundle BUNDLE EXPECTED_SHA256 INPUTS [--setups=AUTHORITY] [--capacity=LIMITS] [--limits=LIMITS]\n\n\
             BUNDLE is protocol-bundle output; INPUTS is a zkc.bundle-inputs/1 array.\n\
             EXPECTED_SHA256 must come from trusted compilation or deployment configuration.\n\
             All roles are prepared before execution resources are issued.\n\
             Completed execution does not interpret protocol acceptance outputs.\n",
        ),
        "run-protocol" => Some(
            "Usage: zkc run-protocol SOURCE PARTICIPANTS INPUTS CHECKER [--limits=LIMITS]\n\n\
             SOURCE is explicit common JSON from zkc-compile protocol-source.\n\
             PARTICIPANTS is JSON from protocol-compile; INPUTS is a zkc.run/2 input array.\n\
             CHECKER is the independent Lean interactive-protocol executable.\n",
        ),
        "produce-artifact" | "validate-artifact" => Some(
            "Usage: zkc produce-artifact|validate-artifact SOURCE DESCRIPTOR CONSTRUCTION PARTICIPANTS INPUTS COMPILER_CHECKER LEAN_CHECKER PROOF TRANSCRIPT_BUDGET [--trace=full|none]\n\n\
             SOURCE and DESCRIPTOR are original explicit JSON; CONSTRUCTION is\n\
             protocol-construct output. PARTICIPANTS compiles its common program.\n\
             INPUTS supplies the public configuration and this participant's inputs.\n\
             COMPILER_CHECKER is zkc-compile; LEAN_CHECKER is interactive-protocol.\n\
             PROOF is written by the producer and read by the validator.\n\
             TRANSCRIPT_BUDGET bounds transcript transitions.\n\
             Trace options select report detail; producer observation stays disabled.\n",
        ),
        "produce-native-proof" | "validate-native-proof" => Some(
            "Usage: zkc produce-native-proof|validate-native-proof DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF [--key-id=EXPECTED_KEY_ID | --setups=AUTHORITY] [--attempts=POLICY] [--capacity=LIMITS]\n\n\
             DEPLOYMENT is zkc-compile protocol-proof output.\n\
             EXPECTED_SHA256 authenticates those exact file bytes and must come\n\
             from trusted compilation or deployment configuration.\n\
             INPUTS supplies public bindings and one role's invocation values.\n\
             PROOF is atomically written by the producer and read by the validator.\n",
        ),
        "inspect-artifact-identity" => Some(
            "Usage: zkc inspect-artifact-identity SOURCE DESCRIPTOR [CONFIGURATION]\n\n\
             Inspect explicit source and construction JSON without producing a proof.\n\
             CONFIGURATION optionally supplies public-configuration JSON.\n",
        ),
        "run" | "run-physical" => Some(
            "Usage: zkc run|run-physical SOURCE PLAN INPUTS CHECKER [--phase PROFILE CERTIFICATE | --endpoint PROFILE CERTIFICATE] [--storage packed|segmented]\n\n\
             Execute the finite table path using its corresponding Lean checker.\n\
             For native mathematical bundles use run-bundle; source/Lean participants use run-protocol.\n",
        ),
        _ => None,
    }
}

/// Handle discovery without opening inputs or invoking any checker.
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
