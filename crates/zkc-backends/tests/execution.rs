//! Execution backend contracts.
mod common;
#[path = "common/fixture.rs"]
mod fixture;
mod support;

#[path = "execution/authoring.rs"]
mod authoring;
#[path = "execution/checked_access.rs"]
mod checked_access;
#[path = "execution/entry_policy.rs"]
mod entry_policy;
#[path = "execution/kernels.rs"]
mod kernels;
#[path = "execution/local_control.rs"]
mod local_control;
#[path = "execution/native_boolean.rs"]
mod native_boolean;
#[path = "execution/native_composition.rs"]
mod native_composition;
#[path = "execution/oracle_access.rs"]
mod oracle_access;
