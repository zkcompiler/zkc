//! A KoalaBear `StarkProtocolConfig` for the pinned upstream key generation
//! and debug checkers.
//!
//! The pinned `openvm-stark-sdk` ships BabyBear and BN254 configurations
//! only. `StarkProtocolConfig` is a set of associated types plus the system
//! parameters and a Merkle hasher; this instantiation mirrors
//! `crates/stark-sdk/src/config/baby_bear_poseidon2.rs` with the Poseidon2
//! permutation Plonky3 0.4.3 provides for KoalaBear. It is used for
//! `MultiStarkKeygenBuilder` (verifying-key DAG, trace-height constraints) and
//! `DebugConstraintBuilder`; no proof is produced and no security parameter
//! choice is claimed sound.

use crate::field::F;
use openvm_stark_backend::WhirProximityStrategy;
use openvm_stark_backend::hasher::Hasher;
use openvm_stark_backend::interaction::LogUpSecurityParameters;
use openvm_stark_backend::{StarkProtocolConfig, SystemParams};
use p3_field::PrimeField32;
use p3_field::extension::BinomialExtensionField;
use p3_koala_bear::{Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

const WIDTH: usize = 16;
const RATE: usize = 8;
pub const DIGEST_SIZE: usize = 8;

type Perm = Poseidon2KoalaBear<WIDTH>;
type Hash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_SIZE>;
type Compress = TruncatedPermutation<Perm, 2, DIGEST_SIZE, WIDTH>;
pub type Digest = [F; DIGEST_SIZE];
pub type Ext = BinomialExtensionField<F, 4>;

/// The skip parameter the verifier would use for effective heights
/// `2^max(log_height, l_skip)`; the SDK application default.
pub const L_SKIP: usize = 4;
/// Upstream application configurations enforce constraint degree three.
pub const MAX_CONSTRAINT_DEGREE: usize = 3;
/// Message length bound of the LogUp parameters, including the bus index.
pub const LOG_MAX_MESSAGE_LENGTH: u32 = 7;

#[derive(Clone)]
pub struct KoalaBearRelationConfig {
    params: SystemParams,
    hasher: Hasher<F, Digest, Hash, Compress>,
}

impl StarkProtocolConfig for KoalaBearRelationConfig {
    type F = F;
    type EF = Ext;
    type Digest = Digest;
    type Hasher = Hasher<F, Digest, Hash, Compress>;

    fn params(&self) -> &SystemParams {
        &self.params
    }

    fn hasher(&self) -> &Self::Hasher {
        &self.hasher
    }
}

/// LogUp parameters with the field-dependent interaction-count threshold the
/// upstream SDK uses (`F::ORDER_U32`) and the SDK's message-length bound. The
/// proof-of-work bits are irrelevant to key generation and debug checking.
pub fn logup_parameters() -> LogUpSecurityParameters {
    LogUpSecurityParameters {
        max_interaction_count: F::ORDER_U32,
        log_max_message_length: LOG_MAX_MESSAGE_LENGTH,
        pow_bits: 0,
    }
}

/// System parameters shaped like the SDK application preset
/// (`app_params_with_100_bits_security`): `log_blowup 1`, `l_skip 4`,
/// `w_stack 2048`, unique decoding, constraint degree three. Only `l_skip`,
/// `max_constraint_degree` and the LogUp bounds reach key generation.
pub fn system_parameters() -> SystemParams {
    SystemParams::new(
        1,
        L_SKIP,
        16,
        2048,
        10,
        5,
        15,
        WhirProximityStrategy::UniqueDecoding,
        100,
        logup_parameters(),
        MAX_CONSTRAINT_DEGREE,
        20,
        4,
    )
}

pub fn config() -> KoalaBearRelationConfig {
    let perm = default_koalabear_poseidon2_16();
    KoalaBearRelationConfig {
        params: system_parameters(),
        hasher: Hasher::new(
            PaddingFreeSponge::new(perm.clone()),
            TruncatedPermutation::new(perm),
        ),
    }
}
