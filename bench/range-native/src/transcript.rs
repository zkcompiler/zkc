use crate::{Dimensions, Error, Result, Statement};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use merlin::Transcript;

pub const APP_DOMAIN: &[u8] = b"zkc-goal3-range-native-v1";
/// This prefix is shared with the independently invoked upstream baseline.
pub fn application_transcript(context: &[u8]) -> Transcript {
    let mut t = Transcript::new(APP_DOMAIN);
    t.append_message(b"application-context", context);
    t
}

/// Every designated challenge is rejected at zero. No retries or resampling.
pub fn require_nonzero(label: &'static str, value: Scalar) -> Result<Scalar> {
    if value == Scalar::ZERO {
        Err(Error::ZeroChallenge(label))
    } else {
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub operation: &'static str,
    pub label: &'static str,
    pub bytes: Vec<u8>,
    pub reduced: Option<[u8; 32]>,
}

pub(crate) struct Flight {
    pub raw: Transcript,
    pub events: Vec<Event>,
    #[cfg(test)]
    pub inject: Option<(&'static str, Scalar)>,
}
impl Flight {
    pub fn new(context: &[u8]) -> Self {
        Self {
            raw: application_transcript(context),
            events: Vec::new(),
            #[cfg(test)]
            inject: None,
        }
    }
    pub fn append(&mut self, label: &'static str, bytes: &[u8]) {
        self.raw.append_message(label.as_bytes(), bytes);
        self.events.push(Event {
            operation: "append",
            label,
            bytes: bytes.to_vec(),
            reduced: None,
        });
    }
    pub fn point(&mut self, label: &'static str, p: RistrettoPoint) -> Result<()> {
        let bytes = p.compress().to_bytes();
        crate::decode_point(bytes, true)?;
        self.append(label, &bytes);
        Ok(())
    }
    pub fn scalar(&mut self, label: &'static str, x: Scalar) {
        self.append(label, x.as_bytes());
    }
    pub fn challenge(&mut self, label: &'static str) -> Result<Scalar> {
        let mut bytes = [0; 64];
        self.raw.challenge_bytes(label.as_bytes(), &mut bytes);
        let value = Scalar::from_bytes_mod_order_wide(&bytes);
        #[cfg(test)]
        let value = match self.inject {
            Some((l, v)) if l == label => v,
            _ => value,
        };
        self.events.push(Event {
            operation: "challenge",
            label,
            bytes: bytes.to_vec(),
            reduced: Some(value.to_bytes()),
        });
        require_nonzero(label, value)
    }
    pub fn range_domain(&mut self, d: Dimensions, statement: &Statement) {
        self.append("dom-sep", b"rangeproof v1");
        self.append("n", &(d.n as u64).to_le_bytes());
        self.append("m", &(d.m as u64).to_le_bytes());
        for v in &statement.commitments {
            self.append("V", v);
        }
    }
    pub fn ipa_domain(&mut self, total: usize) {
        self.append("dom-sep", b"ipp v1");
        self.append("n", &(total as u64).to_le_bytes());
    }
    pub fn fingerprint(&self) -> [u8; 32] {
        let mut t = self.raw.clone();
        let mut out = [0; 32];
        t.challenge_bytes(b"research-end-state", &mut out);
        out
    }
}
