fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if let Some(status) = zkc_tools::cli::discover(&args) {
        std::process::exit(status);
    }
    let report = zkc_tools::cli::run(&args[0], &args[1..]);
    println!("{report}");
    if !zkc_tools::cli::succeeded(&report) {
        std::process::exit(1);
    }
}
