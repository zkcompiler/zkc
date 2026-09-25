use crate::{Dimensions, Error, Result, decode_point};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};

#[derive(Clone, Debug)]
pub(crate) struct Proof {
    pub a_commit: RistrettoPoint,
    pub s_commit: RistrettoPoint,
    pub t1_commit: RistrettoPoint,
    pub t2_commit: RistrettoPoint,
    pub tx: Scalar,
    pub tau: Scalar,
    pub mu: Scalar,
    pub rounds: Vec<(RistrettoPoint, RistrettoPoint)>,
    pub a: Scalar,
    pub b: Scalar,
}
impl Proof {
    pub fn parse(bytes: &[u8], d: Dimensions) -> Result<Self> {
        if bytes.len() != d.proof_len() {
            return Err(Error::Length);
        }
        // Length/count admission precedes indexing and allocation.
        let chunk = |i: usize| -> [u8; 32] {
            bytes[32 * i..32 * (i + 1)]
                .try_into()
                .expect("admitted length")
        };
        let point = |i| decode_point(chunk(i), true);
        let scalar = |i| {
            Option::<Scalar>::from(Scalar::from_canonical_bytes(chunk(i)))
                .ok_or(Error::NoncanonicalScalar)
        };
        let a_commit = point(0)?;
        let s_commit = point(1)?;
        let t1_commit = point(2)?;
        let t2_commit = point(3)?;
        let tx = scalar(4)?;
        let tau = scalar(5)?;
        let mu = scalar(6)?;
        let rounds = (0..d.rounds())
            .map(|i| Ok((point(7 + 2 * i)?, point(8 + 2 * i)?)))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            a_commit,
            s_commit,
            t1_commit,
            t2_commit,
            tx,
            tau,
            mu,
            rounds,
            a: scalar(7 + 2 * d.rounds())?,
            b: scalar(8 + 2 * d.rounds())?,
        })
    }
    pub fn bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(32 * (9 + 2 * self.rounds.len()));
        for p in [self.a_commit, self.s_commit, self.t1_commit, self.t2_commit] {
            out.extend_from_slice(p.compress().as_bytes());
        }
        for s in [self.tx, self.tau, self.mu] {
            out.extend_from_slice(s.as_bytes());
        }
        for (l, r) in &self.rounds {
            out.extend_from_slice(l.compress().as_bytes());
            out.extend_from_slice(r.compress().as_bytes());
        }
        out.extend_from_slice(self.a.as_bytes());
        out.extend_from_slice(self.b.as_bytes());
        out
    }
}
