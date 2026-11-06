//! Physical-type judgments use the caller's admission allowance. All inputs are
//! formed immutable descriptors from Program admission; this module grants no
//! new representation, wire, or construction-state permissions.
use super::*;

pub(super) trait AdmissionWork {
    fn charge(&mut self, cost: usize) -> Result<()>;
}
impl AdmissionWork for ProofWork {
    fn charge(&mut self, cost: usize) -> Result<()> {
        ProofWork::charge(self, cost)
    }
}
impl AdmissionWork for usize {
    fn charge(&mut self, cost: usize) -> Result<()> {
        match self.checked_sub(cost) {
            Some(remaining) => *self = remaining,
            None => {
                *self = 0;
                return Err(refuse("native-proof-codec-limit"));
            }
        }
        Ok(())
    }
}

// BTree lookup/insertion compares at most a bounded number of keys per level.
// Charge the candidate's bytes before either operation, including cache hits.
pub(super) fn lookup_work(name: &str, entries: usize) -> usize {
    12 * (name.len() + 1) * (1 + (entries + 1).ilog2() as usize)
}

// Charge every logical occurrence before visiting its metadata. This also
// covers comparisons of complete nominal variants and structural arguments.
pub(super) fn logical_work(
    logical: &super::super::LogicalType,
    work: &mut impl AdmissionWork,
) -> Result<()> {
    work.charge(1)?;
    if let Some(descriptor) = logical.variant_descriptor() {
        work.charge(descriptor.spelling().len() + descriptor.alternatives().len())?;
        for arm in descriptor.alternatives() {
            work.charge(arm.label().len() + arm.payload().len())?;
            for child in arm.payload() {
                logical_work(child, work)?;
            }
        }
    } else if let Some(structure) = logical.structural() {
        work.charge(structure.arguments().len())?;
        for argument in structure.arguments() {
            work.charge(1)?;
            if let super::super::TypeArgument::Type(child) = argument {
                logical_work(child, work)?;
            }
        }
    }
    Ok(())
}

pub(super) fn comparison_work(ty: &PhysicalType, work: &mut impl AdmissionWork) -> Result<()> {
    work.charge(1)?;
    logical_work(ty.logical(), work)?;
    for child in ty.children().unwrap_or_default() {
        comparison_work(child, work)?;
    }
    Ok(())
}

pub(super) fn type_list_work(types: &[PhysicalType], work: &mut impl AdmissionWork) -> Result<()> {
    work.charge(types.len())?;
    for ty in types {
        comparison_work(ty, work)?;
    }
    Ok(())
}

// Do not construct a fresh default layout. Program admission already checked
// logical erasure, aggregate shape and bounds. Equality with the default is
// exactly the default representation at every node of that checked layout.
fn default_layout(ty: &PhysicalType, work: &mut impl AdmissionWork) -> Result<bool> {
    work.charge(1 + zkc_catalog::INSTALLATION.applied_representations.len())?;
    logical_work(ty.logical(), work)?;
    if PhysicalType::default_representation(ty.logical()).ok() != Some(ty.representation()) {
        return Ok(false);
    }
    for child in ty.children().unwrap_or_default() {
        if !default_layout(child, work)? {
            return Ok(false);
        }
    }
    Ok(true)
}

// Contracts::permits_wire validates ownership, consults bounded ordered tables,
// and recursively checks complete child layouts. Reserve its recursive work
// before entering it. The factor covers table-key comparisons (at most 4096
// entries), layout/default construction in leaf frame checks, and repeated
// structural walks at each of the at most nine admitted type levels. This is
// structural work, not a bound on arbitrary trusted ContractSupport callbacks.
fn wire_work(ty: &PhysicalType, work: &mut impl AdmissionWork) -> Result<()> {
    work.charge(256)?;
    // Use a charging adapter so metadata is debited before its inspection,
    // rather than counting an uncharged traversal and debiting afterwards.
    struct Reserve<'a, W>(&'a mut W);
    impl<W: AdmissionWork> AdmissionWork for Reserve<'_, W> {
        fn charge(&mut self, cost: usize) -> Result<()> {
            self.0.charge(cost.saturating_mul(256))
        }
    }
    comparison_work(ty, &mut Reserve(work))
}

pub(super) fn wire_data(
    ty: &PhysicalType,
    contracts: &super::super::Contracts,
    work: &mut impl AdmissionWork,
) -> Result<bool> {
    wire_work(ty, work)?;
    Ok(contracts.permits_wire(ty, super::super::WireCodec::Native))
}

pub(super) fn verifier_data(
    ty: &PhysicalType,
    contracts: &super::super::Contracts,
    work: &mut impl AdmissionWork,
) -> Result<bool> {
    if !default_layout(ty, work)? {
        return wire_data(ty, contracts, work);
    }
    if matches!(ty.kind(), Type::Shake128State | Type::QuotientMatrix) {
        return Ok(true);
    }
    if ty.kind() == Type::Sequence || ty.kind() == Type::Variant {
        for child in ty.children().unwrap_or_default() {
            if !verifier_data(child, contracts, work)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    work.charge(1)?;
    // The default-layout judgment above replaces the second default_for in
    // verifier-key/data-frame checks. These alternatives have the same Boolean
    // permission as the original disjunction and avoid needless catalog walks.
    if ty.is_serializable()
        || ty.has_native_array_frame()
        || ty.kind() == Type::VerifierKey
            && ty.logical().spelling() == "verifier_key:multilinear.kzg.bls12-381/0"
        || matches!(
            ty.kind(),
            Type::Sequence
                | Type::Variant
                | Type::Vector
                | Type::Groups
                | Type::Indices
                | Type::Bytes
                | Type::Matrix
        ) && ty.logical().is_native_message_data()
    {
        return Ok(true);
    }
    wire_data(ty, contracts, work)
}

pub(super) fn permitted(
    ty: &PhysicalType,
    state: &[PhysicalType],
    contracts: &super::super::Contracts,
    work: &mut impl AdmissionWork,
) -> Result<bool> {
    if verifier_data(ty, contracts, work)? {
        return Ok(true);
    }
    for slot in state {
        comparison_work(ty, work)?;
        comparison_work(slot, work)?;
        if slot == ty {
            return Ok(true);
        }
    }
    Ok(ty.kind() == Type::ResourceUnit && default_layout(ty, work)?)
}

// LocalInstruction::walk materializes a flattened vector. Reserve each visited
// slot and its stack/vector handling before that allocation, including dormant
// arms; no caller obtains a fresh allowance here.
pub(super) fn body_work(body: &[LocalInstruction], work: &mut impl AdmissionWork) -> Result<()> {
    fn visit(body: &[LocalInstruction], work: &mut impl AdmissionWork, depth: usize) -> Result<()> {
        for op in body {
            work.charge(4 * (depth + 1))?;
            match op {
                LocalInstruction::Conditional {
                    then_body,
                    else_body,
                    ..
                } => {
                    visit(then_body, work, depth + 1)?;
                    visit(else_body, work, depth + 1)?;
                }
                LocalInstruction::Match { arms, .. } => {
                    work.charge(arms.len())?;
                    for arm in arms {
                        visit(&arm.body, work, depth + 1)?;
                    }
                }
                LocalInstruction::For { body, .. } => {
                    visit(body, work, depth + 1)?;
                }
                _ => {}
            }
        }
        Ok(())
    }
    visit(body, work, 0)
}
