use serde_json::json;
use zkc_tools::table::run;

mod cli;

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if let Some(status) = cli::discover(&args) {
        std::process::exit(status);
    }
    if args
        .first()
        .is_some_and(|arg| arg == "inspect-artifact-identity")
    {
        match zkc_tools::artifact::inspect_identity(&args[1..]) {
            Ok(report) => println!("{report}"),
            Err(error) => {
                println!("{}", json!({"status":"refused","code":error}));
                std::process::exit(1);
            }
        }
        return;
    }
    if args
        .first()
        .is_some_and(|arg| arg == "produce-artifact" || arg == "validate-artifact")
    {
        let report = zkc_tools::artifact::run(args[0] == "produce-artifact", &args[1..]);
        println!("{report}");
        if report["status"] == "refused" {
            std::process::exit(1);
        }
        return;
    }
    if args.first().is_some_and(|arg| arg == "run-protocol") {
        match zkc_tools::protocol::run(&args[1..]) {
            Ok(report) => println!("{report}"),
            Err(error) => {
                println!("{}", json!({"status":"refused","code":error}));
                std::process::exit(1);
            }
        }
        return;
    }
    match run(&args) {
        Ok(report) => println!("{report}"),
        Err(error) => {
            println!("{}", json!({"status":"refused","code":error.0}));
            std::process::exit(1);
        }
    }
}
