fn main() {
    let mut args = std::env::args().skip(1).collect::<Vec<_>>();
    let global_json = args.first().is_some_and(|s| s == "--json");
    if global_json {
        args.remove(0);
    }
    if let Some(status) = zkc_tools::cli::discover(&args) {
        std::process::exit(status);
    }
    if global_json {
        let position = args.iter().position(|s| s == "--").unwrap_or(args.len());
        if !args[..position].iter().any(|s| s == "--json") {
            args.insert(position, "--json".into());
        }
    }
    let report = zkc_tools::cli::run(&args[0], &args[1..]);
    let json = args
        .iter()
        .skip(1)
        .take_while(|s| s.as_str() != "--")
        .any(|s| s == "--json");
    if json {
        println!("{report}");
    } else if zkc_tools::cli::succeeded(&report) {
        print!("{}", zkc_tools::cli::human(&report));
    } else {
        eprint!("{}", zkc_tools::cli::human(&report));
    }
    if !zkc_tools::cli::succeeded(&report) {
        std::process::exit(1);
    }
}
