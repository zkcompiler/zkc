use crate::{Dimensions, Result};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT, ristretto::RistrettoPoint, scalar::Scalar,
};
use sha3::{
    Digest, Sha3_512, Shake256,
    digest::{ExtendableOutput, Update, XofReader},
};

/// Private fields prevent accidental substitution of an unbound generator suite.
pub struct Generators {
    d: Dimensions,
    pub(crate) g: Vec<RistrettoPoint>,
    pub(crate) h: Vec<RistrettoPoint>,
    pub(crate) base: RistrettoPoint,
    pub(crate) blind: RistrettoPoint,
}
impl Generators {
    pub fn new(n: usize, m: usize) -> Result<Self> {
        let d = Dimensions::new(n, m)?;
        let mut g = Vec::with_capacity(d.total);
        let mut h = Vec::with_capacity(d.total);
        for j in 0..m {
            for (namespace, dst) in [(b'G', &mut g), (b'H', &mut h)] {
                let mut xof = Shake256::default();
                Update::update(&mut xof, b"GeneratorsChain");
                Update::update(&mut xof, &[namespace]);
                Update::update(&mut xof, &(j as u32).to_le_bytes());
                let mut reader = xof.finalize_xof();
                for _ in 0..n {
                    let mut uniform = [0; 64];
                    reader.read(&mut uniform);
                    dst.push(RistrettoPoint::from_uniform_bytes(&uniform));
                }
            }
        }
        let base = RISTRETTO_BASEPOINT_POINT;
        let hash: [u8; 64] = Sha3_512::digest(base.compress().as_bytes()).into();
        let blind = RistrettoPoint::from_uniform_bytes(&hash);
        Ok(Self {
            d,
            g,
            h,
            base,
            blind,
        })
    }
    pub fn dimensions(&self) -> Dimensions {
        self.d
    }
    pub fn commit(&self, value: u64, blinding: Scalar) -> [u8; 32] {
        crate::linear::msm(&[Scalar::from(value), blinding], &[self.base, self.blind])
            .expect("fixed two-term MSM")
            .compress()
            .to_bytes()
    }
    pub fn generator_bytes(&self) -> Vec<[u8; 32]> {
        [self.base, self.blind]
            .iter()
            .chain(&self.g)
            .chain(&self.h)
            .map(|p| p.compress().to_bytes())
            .collect()
    }
}
