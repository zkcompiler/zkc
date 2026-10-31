//! Finite numerical search over the defined two-stage Keccak chain.
//!
//! Witness envelopes and request labels are explicit borrowed bytes. This API
//! installs no grinding wire or live resource operation. A match is numerical
//! evidence only: the caller must recheck live authority and recompute the
//! adopted request before publishing an answer or successor.
use super::{
    ABSORB_TAG, KeccakChain, MESSAGE, REQUEST_TAG, digest, write_frame_header, write_request,
};
use crate::numerical::{self, Call, StorageReservation};
use p3_keccak::Keccak256Hash;
use p3_symmetric::CryptographicHasher;

type Digest = [u8; 32];
const LANES: usize = <Keccak256Hash as CryptographicHasher<u8, Digest>>::LANES;
const STAGING_BYTES: usize = 32 * 1024;

/// The candidate witness is `prefix || nonce:u64le || suffix`. The request's
/// final length is bound even though search computes only its first hash block.
pub struct NonceInput<'a> {
    pub chain: &'a KeccakChain,
    pub witness_label: &'a [u8],
    pub prefix: &'a [u8],
    pub suffix: &'a [u8],
    pub request_label: &'a [u8],
    pub total_output_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZeroBits {
    /// Trailing zero bits of the first eight digest bytes interpreted as LE64.
    LowLe(u8),
    /// Leading zero bits of the first eight digest bytes interpreted as BE64.
    LeadingBe(u8),
}
impl ZeroBits {
    fn bits(self) -> u8 {
        match self {
            Self::LowLe(bits) | Self::LeadingBe(bits) => bits,
        }
    }
    fn accepts(self, digest: &Digest) -> bool {
        let bytes = digest[..8].try_into().expect("fixed digest prefix");
        let zeros = match self {
            Self::LowLe(_) => u64::from_le_bytes(bytes).trailing_zeros(),
            Self::LeadingBe(_) => u64::from_be_bytes(bytes).leading_zeros(),
        };
        zeros >= u32::from(self.bits())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Gate,
    Range,
    Length,
    Numerical(numerical::Error),
}
impl From<numerical::Error> for Error {
    fn from(value: numerical::Error) -> Self {
        Self::Numerical(value)
    }
}

/// Per-search charges, excluding earlier users of the same Call. Work counts
/// permutation lanes, including SIMD padding. It is not a cycle estimate or a
/// formal oracle-query count. Peak memory is additional managed reservation,
/// excluding borrowed inputs, provider stack and allocator overhead.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Receipt {
    /// Distinct in-range candidates whose two hash stages completed.
    pub evaluated: u64,
    /// Duplicate candidate lanes evaluated solely to fill SIMD batches.
    pub padded_candidates: u64,
    pub executed_permutation_lanes: u64,
    /// Accepted work; can exceed execution after a scratch allocation failure.
    pub admitted_work: u64,
    /// Consecutive candidates from `first` known to fail, excluding the winner.
    pub failing_prefix: u64,
    /// Real candidates after the winner in its fully evaluated batch.
    pub evaluated_after_match: u64,
    /// Selected physical lane width, or zero when no hashing plan was selected.
    pub lanes: usize,
    pub peak_memory: usize,
    /// Retained scalar payload, eight on a hit and zero otherwise.
    pub output_bytes: usize,
}

/// A receipt accompanies every normal success and refusal, including an
/// allocation failure after accepted work but before any executed permutation.
#[derive(Debug, PartialEq, Eq)]
pub struct Report {
    pub outcome: Result<Option<u64>, Error>,
    pub receipt: Receipt,
}

struct Plan {
    absorb_bytes: usize,
    request_bytes: usize,
    witness_bytes: u64,
    capacity: usize,
    lanes: usize,
    workspace_bytes: usize,
    work: u64,
}
impl Plan {
    fn new(input: &NonceInput<'_>, attempts: u64) -> Result<Self, Error> {
        let length = |parts: &[usize]| {
            parts
                .iter()
                .try_fold(0usize, |sum, value| sum.checked_add(*value))
                .filter(|value| *value <= isize::MAX as usize)
                .ok_or(Error::Length)
        };
        let witness = length(&[input.prefix.len(), 8, input.suffix.len()])?;
        let absorb_bytes = length(&[ABSORB_TAG.len(), 32, 17, input.witness_label.len(), witness])?;
        let request_bytes = length(&[REQUEST_TAG.len(), 32, 17, input.request_label.len(), 8, 8])?;
        let witness_bytes = u64::try_from(witness).map_err(|_| Error::Length)?;
        let capacity = attempts.min(LANES as u64) as usize;
        let staging = absorb_bytes.max(request_bytes).checked_mul(capacity);
        let batched = LANES > 1 && capacity > 1 && staging.is_some_and(|n| n <= STAGING_BYTES);
        let (capacity, lanes, workspace_bytes) = if batched {
            (capacity, LANES, staging.unwrap() + 32 * capacity)
        } else {
            (1, 1, 64)
        };
        let permutations = (absorb_bytes / 136 + 1) as u64 + (request_bytes / 136 + 1) as u64;
        let work = permutations
            .checked_mul(lanes as u64)
            .ok_or(Error::Length)?;
        Ok(Self {
            absorb_bytes,
            request_bytes,
            witness_bytes,
            capacity,
            lanes,
            workspace_bytes,
            work,
        })
    }
}

struct Workspace<'a> {
    // Storage is destroyed before its reservation.
    messages: Vec<u8>,
    digests: Vec<Digest>,
    _reservation: StorageReservation<'a>,
}
impl<'a> Workspace<'a> {
    fn new(call: &'a Call, plan: &Plan, receipt: &mut Receipt) -> Result<Self, Error> {
        let reservation = call.reserve_workspace::<u8>(plan.workspace_bytes)?;
        receipt.peak_memory = 8 + plan.workspace_bytes;
        let (messages, digests) = if plan.lanes > 1 {
            let bytes = plan.absorb_bytes.max(plan.request_bytes) * plan.capacity;
            let mut messages =
                crate::allocation::reserve(bytes).map_err(|_| numerical::Error::Allocation)?;
            messages.resize(bytes, 0);
            let mut digests = crate::allocation::reserve(plan.capacity)
                .map_err(|_| numerical::Error::Allocation)?;
            digests.resize(plan.capacity, [0; 32]);
            (messages, digests)
        } else {
            (Vec::new(), Vec::new())
        };
        Ok(Self {
            messages,
            digests,
            _reservation: reservation,
        })
    }

    fn evaluate(
        &mut self,
        input: &NonceInput<'_>,
        plan: &Plan,
        first: u64,
        count: usize,
        gate: ZeroBits,
    ) -> Option<usize> {
        if plan.lanes == 1 {
            let state = digest(|write| write_absorption(write, input, plan, first));
            let value = digest(|write| {
                write_request(
                    write,
                    &state,
                    input.request_label,
                    input.total_output_bytes,
                    0,
                )
            });
            return gate.accepts(&value).then_some(0);
        }
        for (offset, message) in self.messages[..count * plan.absorb_bytes]
            .chunks_exact_mut(plan.absorb_bytes)
            .enumerate()
        {
            fill(message, |write| {
                write_absorption(write, input, plan, first + offset as u64)
            });
        }
        Keccak256Hash.hash_many(
            &self.messages[..count * plan.absorb_bytes],
            &mut self.digests[..count],
        );
        for (message, state) in self.messages[..count * plan.request_bytes]
            .chunks_exact_mut(plan.request_bytes)
            .zip(&self.digests)
        {
            fill(message, |write| {
                write_request(
                    write,
                    state,
                    input.request_label,
                    input.total_output_bytes,
                    0,
                )
            });
        }
        Keccak256Hash.hash_many(
            &self.messages[..count * plan.request_bytes],
            &mut self.digests[..count],
        );
        self.digests[..count]
            .iter()
            .position(|value| gate.accepts(value))
    }
}

fn fill(output: &mut [u8], write: impl FnOnce(&mut dyn FnMut(&[u8]))) {
    let mut position = 0;
    write(&mut |bytes| {
        output[position..position + bytes.len()].copy_from_slice(bytes);
        position += bytes.len();
    });
    debug_assert_eq!(position, output.len());
}

fn write_absorption(mut write: impl FnMut(&[u8]), input: &NonceInput<'_>, plan: &Plan, nonce: u64) {
    write(ABSORB_TAG);
    write(input.chain.state());
    write_frame_header(&mut write, MESSAGE, input.witness_label, plan.witness_bytes);
    write(input.prefix);
    write(&nonce.to_le_bytes());
    write(input.suffix);
}

/// Search an increasing, checked interval. Empty ranges return no match. A zero
/// gate returns `first` only for a nonempty range, with no hashing; it is not a
/// protocol-level canonical-zero elision. Validate even empty and zero-gate
/// requests. Positive gates require at least eight declared answer bytes.
///
/// Select bounded SIMD staging or scalar streaming before execution. Charge each
/// complete two-stage batch before hashing; a refused batch does not fall back
/// to a narrower width. Thus a work allowance need not stop at the same candidate
/// frontier across machines with different lane widths. Scratch and an unreturned
/// nonce reservation are released on every exit; accepted work remains spent.
pub fn search_nonce(
    call: &Call,
    input: &NonceInput<'_>,
    first: u64,
    attempts: u64,
    gate: ZeroBits,
) -> Report {
    let mut receipt = Receipt::default();
    let outcome = search(call, input, first, attempts, gate, &mut receipt);
    Report { outcome, receipt }
}

fn search(
    call: &Call,
    input: &NonceInput<'_>,
    first: u64,
    attempts: u64,
    gate: ZeroBits,
    receipt: &mut Receipt,
) -> Result<Option<u64>, Error> {
    if gate.bits() > 64 {
        return Err(Error::Gate);
    }
    if attempts != 0 && first.checked_add(attempts - 1).is_none() {
        return Err(Error::Range);
    }
    if gate.bits() != 0 && input.total_output_bytes < 8 {
        return Err(Error::Length);
    }
    let plan = Plan::new(input, attempts)?;
    if attempts == 0 {
        return Ok(None);
    }
    let output = call.scalar(8)?;
    receipt.peak_memory = 8;
    if gate.bits() == 0 {
        receipt.output_bytes = 8;
        return output.finish(|| Ok(Some(first)));
    }
    receipt.lanes = plan.lanes;
    let mut workspace = None;
    while receipt.evaluated < attempts {
        let count = (attempts - receipt.evaluated).min(plan.capacity as u64) as usize;
        let evaluated = receipt
            .evaluated
            .checked_add(count as u64)
            .ok_or(numerical::Error::Work)?;
        let padded = receipt
            .padded_candidates
            .checked_add((plan.lanes - count) as u64)
            .ok_or(numerical::Error::Work)?;
        let charged = receipt
            .admitted_work
            .checked_add(plan.work)
            .ok_or(numerical::Error::Work)?;
        call.work(plan.work)?;
        receipt.admitted_work = charged;
        let workspace = match &mut workspace {
            Some(workspace) => workspace,
            None => workspace.insert(Workspace::new(call, &plan, receipt)?),
        };
        let before = receipt.evaluated;
        let found = workspace.evaluate(input, &plan, first + before, count, gate);
        receipt.evaluated = evaluated;
        receipt.padded_candidates = padded;
        receipt.executed_permutation_lanes = charged;
        if let Some(offset) = found {
            receipt.failing_prefix = before + offset as u64;
            receipt.evaluated_after_match = (count - offset - 1) as u64;
            receipt.output_bytes = 8;
            return output.finish(|| Ok(Some(first + before + offset as u64)));
        }
        receipt.failing_prefix = evaluated;
    }
    Ok(None)
}

#[cfg(test)]
mod tests;
