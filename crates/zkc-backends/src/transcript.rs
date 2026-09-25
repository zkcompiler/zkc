//! Suite-specific byte state. The capability store owns this non-Clone wrapper.
//! Framing is zkc's versioned construction; upstream supplies the duplex and
//! permutation. This is not spongefish's default SHAKE/DomainSeparator protocol.
use spongefish::{DuplexSpongeInterface, instantiations::Keccak};
use zkc_runtime::interactive::Identity;

pub(crate) enum Transcript {
    Merlin(merlin::Transcript),
    Spongefish(Keccak),
}

// absorb is associative in spongefish: call boundaries carry no information.
// Each frame is tag:u8 || label_len:u64be || label || data_len:u64be || data.
fn frame(sponge: &mut Keccak, tag: u8, label: &[u8], data: &[u8]) {
    sponge.absorb(&[tag]);
    sponge.absorb(&(label.len() as u64).to_be_bytes());
    sponge.absorb(label);
    sponge.absorb(&(data.len() as u64).to_be_bytes());
    sponge.absorb(data);
}

impl Transcript {
    pub(crate) fn new(suite: Identity, root: &[u8]) -> Self {
        let mut result = match suite {
            Identity::Merlin3Fr64Be
            | Identity::Merlin3Ristretto64Le
            | Identity::Merlin3KoalaBearExt8 => {
                Self::Merlin(merlin::Transcript::new(b"zkc.artifact/1"))
            }
            Identity::Spongefish074KeccakFr64Be => {
                let mut sponge = Keccak::default();
                frame(&mut sponge, 0, b"domain", b"zkc.artifact/1");
                frame(&mut sponge, 0, b"suite", suite.name().as_bytes());
                Self::Spongefish(sponge)
            }
            _ => unreachable!("resource issuance checks suite"),
        };
        result.append_message(b"binding", root);
        result
    }
    pub(crate) fn append_message(&mut self, label: &'static [u8], value: &[u8]) {
        match self {
            Self::Merlin(t) => t.append_message(label, value),
            Self::Spongefish(t) => frame(t, 1, label, value),
        }
    }
    pub(crate) fn challenge_bytes(&mut self, label: &'static [u8], output: &mut [u8; 64]) {
        match self {
            Self::Merlin(t) => t.challenge_bytes(label, output),
            Self::Spongefish(t) => {
                frame(t, 2, label, &64u64.to_be_bytes());
                t.squeeze(output);
            }
        }
    }
}
