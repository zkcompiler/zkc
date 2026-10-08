//! Translate authenticated Entry choices to each native Host's authority map.
use super::{
    Interface,
    interface::raw::{Kind, Port},
};
use crate::{artifact::native, protocol::run};
use std::collections::BTreeMap;
use zkc_runtime::interactive::Type;

type Result<T> = std::result::Result<T, String>;
/// Application-owned expected verifier-key identities, indexed by source setup
/// slot. Neither the package nor invocation material supplies these identities.
#[derive(Clone, Debug, Default)]
pub struct SetupAuthority {
    pub keys: BTreeMap<String, [u8; 32]>,
}
fn check(interface: &Interface, authority: &SetupAuthority) -> Result<()> {
    if authority.keys.len() != interface.setups.len()
        || interface
            .setups
            .iter()
            .any(|slot| !authority.keys.contains_key(&slot.name))
    {
        return Err("entry-setup-authority".into());
    }
    Ok(())
}
pub(super) fn run_authority(
    interface: &Interface,
    authority: SetupAuthority,
) -> Result<run::SetupAuthority> {
    check(interface, &authority)?;
    let slots: BTreeMap<_, _> = interface
        .setups
        .iter()
        .flat_map(|slot| slot.inputs.iter().map(move |i| (*i, slot.name.as_str())))
        .collect();
    let mut inputs = BTreeMap::new();
    let protocol = interface.selected_protocol();
    for role in &protocol.roles {
        let native = protocol
            .inputs
            .iter()
            .filter(|p| p.roles.contains(role))
            .flat_map(|p| &p.native);
        for (local, original) in native.enumerate() {
            if let Some(slot) = slots.get(&(*original as usize)) {
                inputs.insert((role.clone(), local), (*slot).to_owned());
            }
        }
    }
    Ok(run::SetupAuthority {
        keys: authority.keys,
        inputs,
    })
}
pub(super) fn proof_authority(
    interface: &Interface,
    authority: SetupAuthority,
) -> Result<native::SetupAuthority> {
    check(interface, &authority)?;
    let mut result = native::SetupAuthority::default();
    for slot in &interface.setups {
        let representative = *slot.verifier_keys.first().ok_or("entry-setup-key")?;
        for &key in &slot.verifier_keys {
            result.keys.insert(key, authority.keys[&slot.name]);
        }
        for &input in slot.inputs.difference(&slot.verifier_keys) {
            result.inputs.insert(input, representative);
        }
    }
    Ok(result)
}
pub(super) fn key_kind(interface: &Interface, port: &Port) -> Option<Type> {
    if port.schema.kind != Kind::Builtin || port.schema.custody || port.schema.leaves.len() != 1 {
        return None;
    }
    if !interface
        .setups
        .iter()
        .any(|slot| slot.inputs.contains(&(port.native[0] as usize)))
    {
        return None;
    }
    let kind = interface.logical_type(&port.schema.leaves[0])?.kind();
    matches!(kind, Type::ProverKey | Type::VerifierKey).then_some(kind)
}
pub(super) fn check_material(
    interface: &Interface,
    material: &BTreeMap<String, Vec<u8>>,
    capacity: native::NativeCapacity,
) -> Result<()> {
    if material.len() != interface.setups.len() {
        return Err("entry-setup-material".into());
    }
    let mut bytes = 0usize;
    for slot in &interface.setups {
        let key = material.get(&slot.name).ok_or("entry-setup-material")?;
        capacity.check_wire(key.len())?;
        // Proof creates one public copy per VK port; run retains one per slot.
        let copies = if interface.is_proof() {
            slot.verifier_keys.len()
        } else {
            1
        };
        bytes = bytes
            .checked_add(key.len().checked_mul(copies).ok_or("entry-setup-limit")?)
            .ok_or("entry-setup-limit")?;
        if bytes > capacity.values.live_bytes.min(capacity.values.total_bytes) {
            return Err("entry-setup-limit".into());
        }
    }
    Ok(())
}
pub(super) fn public_keys<'a>(
    interface: &Interface,
    material: &'a BTreeMap<String, Vec<u8>>,
    capacity: native::NativeCapacity,
) -> Result<BTreeMap<u32, &'a [u8]>> {
    check_material(interface, material, capacity)?;
    Ok(interface
        .setups
        .iter()
        .flat_map(|slot| {
            let key = material[&slot.name].as_slice();
            slot.verifier_keys.iter().map(move |&i| (i as u32, key))
        })
        .collect())
}
