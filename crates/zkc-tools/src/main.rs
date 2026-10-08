mod cli;

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if let Some(status) = cli::discover(&args) {
        std::process::exit(status);
    }
    if args.first().is_some_and(|arg| {
        matches!(
            arg.as_str(),
            "compile" | "run-entry" | "prove" | "verify" | "bindings"
        )
    }) {
        let report = zkc_tools::entry::cli::run(&args[0], &args[1..]);
        println!("{report}");
        if !zkc_tools::entry::cli::succeeded(&report) {
            std::process::exit(1);
        }
        return;
    }
    if args
        .first()
        .is_some_and(|arg| arg == "produce-native-proof" || arg == "validate-native-proof")
    {
        let report = zkc_tools::proof::run(args[0] == "produce-native-proof", &args[1..]);
        println!("{report}");
        if report["status"] == "refused" {
            std::process::exit(1);
        }
        return;
    }
    if args.first().is_some_and(|arg| arg == "run-bundle") {
        let report = zkc_tools::run::run_cli(&args[1..]);
        let completed = report["status"] == "executed" && report["outcome"][0] == "completed";
        println!("{report}");
        if !completed {
            std::process::exit(1);
        }
        return;
    }
    unreachable!("discovery rejects unknown commands");
}
