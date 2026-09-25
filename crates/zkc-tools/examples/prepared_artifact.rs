//! Repeated fresh executions after immutable artifact and caller-claim admission.
#[path = "support/prepared.rs"]
mod prepared;

fn main() {
    if let Err(error) = prepared::run(|_| serde_json::Value::Null) {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
