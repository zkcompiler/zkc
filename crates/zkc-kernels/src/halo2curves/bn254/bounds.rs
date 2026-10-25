//! Public-shape payload and scheduling bounds for the pinned provider.
//!
//! These bounds are independent of scalar bit lengths and identity patterns.
//! They exclude input/output retention, allocator metadata, thread stacks and
//! CPU-pool ownership. Provider-private Vec allocation is infallible: admission
//! is not allocator-failure recovery. Re-audit on any provider or toolchain
//! allocation-policy change.
use super::{Error, G1Element, G2Element, ScalarElement, payload};
use halo2curves_axiom::{
    CurveAffine,
    bn256::{Fq2, G2Prepared},
};
use std::alloc::Layout;

fn add(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_add(b)
        .filter(|n| *n <= isize::MAX as usize)
        .ok_or(Error::CapacityOverflow)
}

fn mul(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_mul(b)
        .filter(|n| *n <= isize::MAX as usize)
        .ok_or(Error::CapacityOverflow)
}

/// msm_serial casts n to u32 before taking ln; reject lengths that truncate.
fn msm_shape(len: usize) -> Result<(usize, usize, usize), Error> {
    let n = u32::try_from(len).map_err(|_| Error::CapacityOverflow)?;
    let window = if n < 4 {
        1
    } else if n < 32 {
        3
    } else {
        f64::from(n).ln().ceil() as usize
    };
    let buckets = 1usize
        .checked_shl((window - 1) as u32)
        .ok_or(Error::CapacityOverflow)?;
    // Upstream rounds the actual maximum scalar byte length up to bits, then
    // adds a Booth window. Admit every one of the possible 256 public bits.
    Ok((window, buckets, 256 / window + 1))
}

fn bucket_bytes<C: CurveAffine>() -> Result<usize, Error> {
    // Upstream's local enum has None, Affine(C), Projective(C::Curve).
    // Bound the complete enum by a full usize discriminant followed by the
    // largest payload, with both inter-field and trailing alignment padding.
    // Counting just projective coordinates would omit the enum discriminant.
    let alignment = align_of::<C>().max(align_of::<C::CurveExt>());
    let width = size_of::<C>().max(size_of::<C::CurveExt>());
    let payload = Layout::from_size_align(width, alignment).map_err(|_| Error::CapacityOverflow)?;
    let (layout, _) = Layout::new::<usize>()
        .extend(payload)
        .map_err(|_| Error::CapacityOverflow)?;
    Ok(layout.pad_to_align().size())
}

/// Conservative G2-sized bound for either group, including slice-adapter
/// scalar/base staging. Bulk MSM omits staging but may use this same bound.
/// The live serial scratch is one scalar representation vector, a 32-byte OR
/// mask, and one complete aligned bucket enum vector at a time.
pub fn msm_workspace_bytes(len: usize) -> Result<usize, Error> {
    let (_, buckets, _) = msm_shape(len)?;
    if len == 0 {
        return Ok(0);
    }
    let staging = add(payload::<ScalarElement>(len)?, payload::<G2Element>(len)?)?;
    let reprs = payload::<[u8; 32]>(len)?;
    let bucket_width = bucket_bytes::<G1Element>()?.max(bucket_bytes::<G2Element>()?);
    add(add(staging, reprs)?, add(32, mul(buckets, bucket_width)?)?)
}

/// Scheduling score: scalar-byte scanning plus the worst-case number of group
/// additions/doublings in serial Pippenger. An addition/doubling counts as one
/// scheduling unit regardless of group. This is not a time or field-op bound.
pub fn msm_work(len: usize) -> Result<u64, Error> {
    let (window, buckets, windows) = msm_shape(len)?;
    let n = u64::try_from(len).map_err(|_| Error::CapacityOverflow)?;
    if len == 0 {
        return Ok(0);
    }
    n.checked_mul(32)
        .and_then(|scan| {
            n.checked_add(2 * buckets as u64)?
                .checked_add(window as u64)?
                .checked_mul(windows as u64)?
                .checked_add(scan)?
                .checked_add(1)
        })
        .ok_or(Error::CapacityOverflow)
}

pub(super) const PREPARATION_COEFFICIENTS: usize = 91;

/// Preparation and Miller payload, including conservative Vec capacity growth
/// and old/new allocation overlap. Preparation is serial, invocation-local,
/// and retains no cache. The bound assumes Rust's current doubling Vec growth.
pub fn pairing_workspace_bytes(len: usize) -> Result<usize, Error> {
    if len == 0 {
        return Ok(0);
    }
    // 91 coefficient triples grow to capacity 128. A 64 -> 128 realloc may
    // temporarily retain both allocations. 2*128 per pair covers that overlap
    // even though preparations are sequential and earlier pairs retain 128.
    let coefficient_capacity = PREPARATION_COEFFICIENTS.next_power_of_two();
    let coefficients = mul(
        len,
        mul(2 * coefficient_capacity, size_of::<(Fq2, Fq2, Fq2)>())?,
    )?;
    let staging = add(payload::<G1Element>(len)?, payload::<G2Prepared>(len)?)?;
    let terms = payload::<(&G1Element, &G2Prepared)>(len)?;
    // multi_miller_loop grows Vec<(&G1Affine, slice::Iter<Triple>)> by pushing
    // nonidentity terms. Bound both retained capacity and growth overlap by
    // twice max(4, next_power_of_two(public length)).
    let capacity = len
        .checked_next_power_of_two()
        .ok_or(Error::CapacityOverflow)?
        .max(4);
    let pairs = mul(
        2,
        payload::<(&G1Element, std::slice::Iter<'_, (Fq2, Fq2, Fq2)>)>(capacity)?,
    )?;
    add(coefficients, add(staging, add(terms, pairs)?)?)
}

/// Public scheduling score: preparation coefficient steps and Miller line
/// evaluations (91 each per pair), plus a fixed final-exponentiation allowance
/// of 8192 units. These units are not CPU-time or base-field-operation estimates.
pub fn pairing_work(len: usize) -> Result<u64, Error> {
    if len == 0 {
        return Ok(0);
    }
    u64::try_from(len)
        .ok()
        .and_then(|n| n.checked_mul((2 * PREPARATION_COEFFICIENTS) as u64))
        .and_then(|n| n.checked_add(8192))
        .ok_or(Error::CapacityOverflow)
}
