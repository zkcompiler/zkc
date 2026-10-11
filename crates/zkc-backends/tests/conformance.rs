//! Conformance backend contracts.
mod common;
#[path = "common/fixture.rs"]
mod fixture;
mod support;

#[path = "conformance/dleq.rs"]
mod dleq;
#[path = "conformance/external_transcript.rs"]
mod external_transcript;
#[path = "conformance/real_curve.rs"]
mod real_curve;
#[path = "conformance/service_support.rs"]
mod service_support;
