//! Namespaced choice providers with separate logical and physical budgets.
//!
//! The Monero sampler follows `crypto::random32_unbiased` at Monero commit
//! 4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5 (`src/crypto/crypto.cpp`): reject
//! integers at least 15*l, reduce modulo l, then reject zero. Reduction is
//! supplied by curve25519-dalek. A logical accepted scalar is not a raw draw.

use crate::{Result, exhausted, refused};
use curve25519_dalek::scalar::Scalar;
use rand::RngCore;
use std::collections::BTreeMap;

/// Host-selected identity; transcript domains and protocol labels are separate.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Namespace {
    role: String,
    purpose: String,
}

impl Namespace {
    pub fn new(role: &str, purpose: &str) -> Result<Self> {
        let valid = |s: &str| {
            !s.is_empty()
                && s.len() <= 128
                && s.bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b"_.-".contains(&b))
        };
        if !valid(role) || !valid(purpose) {
            return Err(refused("choice-namespace"));
        }
        Ok(Self {
            role: role.into(),
            purpose: purpose.into(),
        })
    }

    pub fn role(&self) -> &str {
        &self.role
    }
    pub fn purpose(&self) -> &str {
        &self.purpose
    }
}

/// Provider calls receive their namespace explicitly. A tape provider must
/// select the corresponding tape; it must not silently concatenate namespaces.
pub trait Source {
    fn draw(&mut self, namespace: &Namespace) -> Result<[u8; 32]>;
}

/// Fresh operating-system entropy. Reproducible tapes are explicitly supplied
/// alternative providers, not silently substituted production randomness.
pub struct OsSource;
impl Source for OsSource {
    fn draw(&mut self, _: &Namespace) -> Result<[u8; 32]> {
        let mut bytes = [0; 32];
        rand::rngs::OsRng
            .try_fill_bytes(&mut bytes)
            .map_err(|_| exhausted("choice-entropy"))?;
        Ok(bytes)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub logical: u64,
    pub raw: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Usage {
    /// Includes a logical request refused for an exhausted logical budget.
    pub logical_requests: u64,
    /// Actual provider invocations, including a provider that returns failure.
    pub raw_requests: u64,
    pub raw_completed: u64,
    pub accepted: u64,
}

struct Stream {
    remaining: Limits,
    usage: Usage,
}

/// Owns the persistent provider and counters across protocol attempts.
pub struct Sampler<S> {
    source: S,
    streams: BTreeMap<Namespace, Stream>,
}

impl<S: Source> Sampler<S> {
    pub fn new(source: S, streams: impl IntoIterator<Item = (Namespace, Limits)>) -> Result<Self> {
        let mut installed = BTreeMap::new();
        for (key, remaining) in streams {
            if installed.len() == 1024
                || installed
                    .insert(
                        key,
                        Stream {
                            remaining,
                            usage: Usage::default(),
                        },
                    )
                    .is_some()
            {
                return Err(refused("choice-streams"));
            }
        }
        Ok(Self {
            source,
            streams: installed,
        })
    }

    pub fn usage(&self, namespace: &Namespace) -> Result<Usage> {
        self.streams
            .get(namespace)
            .map(|s| s.usage)
            .ok_or_else(|| refused("choice-namespace"))
    }

    pub fn source(&self) -> &S {
        &self.source
    }

    pub fn monero_nonzero_scalar(&mut self, namespace: &Namespace) -> Result<Scalar> {
        let stream = self
            .streams
            .get_mut(namespace)
            .ok_or_else(|| refused("choice-namespace"))?;
        // One count per call: a u64 does not overflow.
        stream.usage.logical_requests += 1;
        if stream.remaining.logical == 0 {
            return Err(exhausted("choice-logical-budget"));
        }
        stream.remaining.logical -= 1;
        loop {
            if stream.remaining.raw == 0 {
                return Err(exhausted("choice-raw-budget"));
            }
            stream.remaining.raw -= 1;
            stream.usage.raw_requests += 1; // At most the initial raw budget.
            let bytes = self.source.draw(namespace)?;
            stream.usage.raw_completed += 1; // At most raw_requests.
            if bytes.iter().rev().cmp(LIMIT.iter().rev()).is_ge() {
                continue;
            }
            let scalar = Scalar::from_bytes_mod_order(bytes);
            if scalar == Scalar::ZERO {
                continue;
            }
            stream.usage.accepted += 1; // At most logical_requests.
            return Ok(scalar);
        }
    }
}

// Exactly 15 times the Edwards25519 prime-subgroup order, in little endian.
const LIMIT: [u8; 32] = [
    0xe3, 0x6a, 0x67, 0x72, 0x8b, 0xce, 0x13, 0x29, 0x8f, 0x30, 0x82, 0x8c, 0x0b, 0xa4, 0x10, 0x39,
    0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xf0,
];
