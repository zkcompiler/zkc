//! Reusable Host execution mechanics consuming VM actions. Applications own
//! artifact authentication, setup and public inputs, acceptance and publication.
pub mod joint;
pub mod proof;
pub mod wire;

#[cfg(test)]
#[path = "../../tests/support/host.rs"]
mod test_backend;
