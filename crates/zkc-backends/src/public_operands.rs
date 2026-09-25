//! Additional leakage premise for explicitly selected public-operand kernels.
use crate::{Result, refused};
use std::collections::BTreeSet;

pub(crate) const MSM_IMPLEMENTATION: &str = "dalek-vartime/curve.msm";

/// Installed implementation contract, additional to its mathematical signature.
/// Call only after ordinary binding admission; unknown implementations are not
/// installed by this predicate. No role name implicitly satisfies the premise.
pub fn requires_public_operands(implementation: &str) -> bool {
    implementation == MSM_IMPLEMENTATION
}

/// Caller assertion that every operand visible to each named execution role is
/// public, including inputs, received messages, derived values and resource
/// outputs. This is a trust premise, not a secrecy proof. Scope one backend to
/// its entry/session using EntryPolicy. At most 64 exact role names, 256 bytes
/// each; no wildcards. Default authorizes none, including a role named `V`.
#[derive(Clone, Debug, Default)]
pub struct PublicRolePolicy {
    roles: BTreeSet<String>,
}
impl PublicRolePolicy {
    pub fn new(roles: impl IntoIterator<Item = String>) -> Result<Self> {
        let mut selected = BTreeSet::new();
        for (index, role) in roles.into_iter().enumerate() {
            if index >= 64 || role.is_empty() || role.len() > 256 {
                return Err(refused("public-role-policy"));
            }
            selected.insert(role);
        }
        Ok(Self { roles: selected })
    }
    pub(crate) fn permits(&self, role: &str) -> bool {
        self.roles.contains(role)
    }
}
