//! Application-owned authorization, indexed by original common-program ports.
use super::*;

/// Configuration supplied independently of deployment inputs and proof bytes.
/// `keys` pins every public verifier-key input. `inputs` selects the key port
/// for every other setup-bearing input, including unused prover-key inputs.
#[derive(Clone, Debug, Default)]
pub struct SetupAuthority {
    pub keys: BTreeMap<usize, [u8; 32]>,
    pub inputs: BTreeMap<usize, usize>,
}
impl SetupAuthority {
    pub fn parse(bytes: &[u8]) -> Result<Self> {
        let value = parse(bytes, 64 * 1024)?;
        let row = array(&value, 3)?;
        if text(&row[0])? != "zkc.native-setup-authority/1" {
            return Err("native-proof-key-authority".into());
        }
        let mut result = Self::default();
        for row in list(&row[1])? {
            let row = array(row, 2)?;
            let port = index(&row[0])?;
            digest(text(&row[1])?)?;
            let id = unhex(&row[1])?
                .try_into()
                .map_err(|_| "native-proof-key-authority")?;
            if result.keys.insert(port, id).is_some() {
                return Err("native-proof-key-authority".into());
            }
        }
        for row in list(&row[2])? {
            let row = array(row, 2)?;
            if result
                .inputs
                .insert(index(&row[0])?, index(&row[1])?)
                .is_some()
            {
                return Err("native-proof-key-authority".into());
            }
        }
        Ok(result)
    }
    pub(super) fn check(&self, public: &[Port], maps: &BTreeMap<String, RoleMap>) -> Result<()> {
        let keys: Vec<_> = public
            .iter()
            .filter(|p| p.logical.kind() == Type::VerifierKey)
            .map(|p| p.original)
            .collect();
        let inputs: std::collections::BTreeSet<_> = maps
            .values()
            .flat_map(|m| &m.data)
            .filter(|p| needs_input_setup(&p.logical))
            .map(|p| p.original)
            .collect();
        if keys.len() > 64
            || self.keys.keys().copied().collect::<Vec<_>>() != keys
            || self
                .inputs
                .keys()
                .copied()
                .collect::<std::collections::BTreeSet<_>>()
                != inputs
            || self.inputs.values().any(|key| !self.keys.contains_key(key))
        {
            return Err("native-proof-key-authority".into());
        }
        Ok(())
    }
}
pub(super) use crate::host::setups::needs_input_setup;
