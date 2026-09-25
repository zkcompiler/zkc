//! State transitions adapted from openvm-org/stark-backend v2.0.1, revision
//! 362c7ad8c6b042b320471a137e3eadec7ec69a44, MIT/Apache-2.0:
//! crates/stark-backend/src/transcript/{duplex_sponge,traits}.rs and
//! crates/stark-sdk/src/config/baby_bear_poseidon2.rs. Source hashes and licenses
//! are in provenance.json and UPSTREAM-LICENSE-*. Crypto is p3-baby-bear =0.4.3;
//! there is no claim of interchangeability with workspace Plonky3 0.5.1.
use super::{Error, Result, Transition, Work};
use p3_baby_bear_043::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_field_043::{PrimeCharacteristicRing, PrimeField32};
use p3_symmetric_043::Permutation;

pub const MODULUS: u32 = 2_013_265_921;
pub const WIDTH: usize = 16;
pub const RATE: usize = 8;

pub fn validate_field(value: u32) -> Result<()> {
    if value < MODULUS {
        Ok(())
    } else {
        Err(Error::NonCanonicalField)
    }
}
pub fn validate_bits(bits: u32) -> Result<()> {
    // Exactly the upstream requirements: bits < 32 and 2^bits < p.
    if bits <= 30 {
        Ok(())
    } else {
        Err(Error::InvalidBitWidth)
    }
}
/// Conversion alone has no transcript effects. OpenVM uses masking, not a
/// uniform/rejection sampler. Zero bits still consumes a sample at the caller.
pub fn challenge_bits(value: u32, bits: u32) -> Result<u32> {
    validate_field(value)?;
    validate_bits(bits)?;
    Ok(value & ((1u32 << bits) - 1))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Snapshot {
    pub state: [u32; WIDTH],
    pub absorb_index: usize,
    pub sample_index: usize,
}

#[derive(Clone, Debug)]
pub struct Duplex {
    state: [BabyBear; WIDTH],
    absorb_index: usize,
    sample_index: usize,
    permutation: Poseidon2BabyBear<WIDTH>,
}
impl Default for Duplex {
    fn default() -> Self {
        Self::new()
    }
}
impl Duplex {
    /// All-zero native state, no hidden prefix and no initial permutation.
    pub fn new() -> Self {
        Self {
            state: [BabyBear::ZERO; WIDTH],
            absorb_index: 0,
            sample_index: 0,
            permutation: default_babybear_poseidon2_16(),
        }
    }
    /// Import an explicit data state at the pinned primitive boundary. This
    /// validates representation, not reachability from an admitted protocol.
    pub fn from_snapshot(snapshot: Snapshot) -> Result<Self> {
        if snapshot.absorb_index >= RATE || snapshot.sample_index > RATE {
            return Err(Error::MalformedReplay);
        }
        for value in snapshot.state {
            validate_field(value)?;
        }
        Ok(Self {
            state: snapshot.state.map(BabyBear::from_u32),
            absorb_index: snapshot.absorb_index,
            sample_index: snapshot.sample_index,
            permutation: default_babybear_poseidon2_16(),
        })
    }

    pub fn snapshot(&self) -> Snapshot {
        Snapshot {
            state: self.state.map(|x| x.as_canonical_u32()),
            absorb_index: self.absorb_index,
            sample_index: self.sample_index,
        }
    }
    pub fn observe_work(&self, count: usize) -> Result<Work> {
        let total = self
            .absorb_index
            .checked_add(count)
            .ok_or(Error::SizeOverflow)?;
        Ok(Work {
            permutations: u64::try_from(total / RATE).map_err(|_| Error::SizeOverflow)?,
            observes: u64::try_from(count).map_err(|_| Error::SizeOverflow)?,
            ..Work::default()
        })
    }
    pub fn sample_work(&self, count: usize) -> Result<Work> {
        if count == 0 {
            return Ok(Work::default());
        }
        let (initial, available) = if self.absorb_index != 0 || self.sample_index == 0 {
            (1, RATE)
        } else {
            (0, self.sample_index)
        };
        let remaining = count.saturating_sub(available);
        let perms = remaining / RATE + usize::from(remaining % RATE != 0) + initial;
        Ok(Work {
            permutations: u64::try_from(perms).map_err(|_| Error::SizeOverflow)?,
            samples: u64::try_from(count).map_err(|_| Error::SizeOverflow)?,
            ..Work::default()
        })
    }
    /// Validate the complete slice before mutation. Empty observation is a no-op.
    pub fn observe(&mut self, values: &[u32]) -> Result<Work> {
        for &value in values {
            validate_field(value)?;
        }
        let work = self.observe_work(values.len())?;
        for &value in values {
            self.state[self.absorb_index] = BabyBear::from_u32(value);
            self.absorb_index += 1;
            if self.absorb_index == RATE {
                self.permutation.permute_mut(&mut self.state);
                self.absorb_index = 0;
                self.sample_index = RATE;
            }
        }
        Ok(work)
    }
    pub fn sample(&mut self) -> Transition<u32> {
        let permutes = self.absorb_index != 0 || self.sample_index == 0;
        if permutes {
            self.permutation.permute_mut(&mut self.state);
            self.absorb_index = 0;
            self.sample_index = RATE;
        }
        self.sample_index -= 1;
        Transition {
            value: self.state[self.sample_index].as_canonical_u32(),
            work: Work {
                permutations: u64::from(permutes),
                samples: 1,
                ..Work::default()
            },
        }
    }
    /// Four consecutive samples in BinomialExtensionField<BabyBear,4> basis order.
    /// This returns coefficients; no extension arithmetic is implemented here.
    pub fn sample_ext(&mut self) -> Transition<[u32; 4]> {
        let mut work = Work::default();
        let value = std::array::from_fn(|_| {
            let next = self.sample();
            work.samples += next.work.samples;
            work.permutations += next.work.permutations;
            next.value
        });
        Transition { value, work }
    }
    pub fn sample_bits(&mut self, bits: u32) -> Result<Transition<u32>> {
        validate_bits(bits)?;
        let sample = self.sample();
        Ok(Transition {
            value: challenge_bits(sample.value, bits)?,
            work: sample.work,
        })
    }
    /// Preflight for a direct witness check, excluding clone/search costs.
    pub fn witness_work(&self, bits: u32) -> Result<Work> {
        validate_bits(bits)?;
        Ok(if bits == 0 {
            Work::default()
        } else {
            Work {
                observes: 1,
                samples: 1,
                permutations: 1,
                ..Work::default()
            }
        })
    }
    /// A failed *direct* check retains its observe/sample effects, as upstream.
    /// At zero bits, any canonical witness succeeds without transcript effects.
    pub fn check_witness(&mut self, bits: u32, witness: u32) -> Result<Transition<bool>> {
        validate_bits(bits)?;
        validate_field(witness)?;
        if bits == 0 {
            return Ok(Transition {
                value: true,
                work: Work::default(),
            });
        }
        let observe = self.observe(&[witness])?;
        let sample = self.sample_bits(bits)?;
        Ok(Transition {
            value: sample.value == 0,
            work: observe.checked_add(sample.work)?,
        })
    }
    /// A search trial checks a clone. Its returned work is still real consumed
    /// work; its transcript events belong to the trial, not to the live trace.
    pub fn trial_witness(&self, bits: u32, witness: u32) -> Result<Transition<bool>> {
        self.clone().check_witness(bits, witness)
    }
}
