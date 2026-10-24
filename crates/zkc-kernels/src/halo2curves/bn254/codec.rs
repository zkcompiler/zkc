//! Arkworks 0.6 compressed mathematical bytes, not upstream parity encoding.
//! Flag/sign rules follow ark-ec `short_weierstrass/serialization_flags.rs`;
//! Fq2 coefficient order follows ark-ff `quadratic_extension.rs`.
use super::{Error, G1Element, G2Element, validate_g1, validate_g2};
use halo2curves_axiom::{
    CurveAffine,
    bn256::{Fq, Fq2},
    ff::{Field, PrimeField},
    group::prime::PrimeCurveAffine,
};

const INFINITY: u8 = 1 << 6;
const NEGATIVE: u8 = 1 << 7;

fn fq(bytes: &[u8]) -> Result<Fq, Error> {
    let repr = bytes.try_into().map_err(|_| Error::InvalidEncoding)?;
    Option::<Fq>::from(Fq::from_repr(repr)).ok_or(Error::InvalidEncoding)
}

fn flags<const N: usize>(bytes: &[u8]) -> Result<([u8; N], bool, bool), Error> {
    let mut payload: [u8; N] = bytes.try_into().map_err(|_| Error::InvalidEncoding)?;
    let infinity = payload[N - 1] & INFINITY != 0;
    let negative = payload[N - 1] & NEGATIVE != 0;
    payload[N - 1] &= !(INFINITY | NEGATIVE);
    if infinity && (negative || payload.iter().any(|byte| *byte != 0)) {
        return Err(Error::InvalidEncoding);
    }
    Ok((payload, infinity, negative))
}

pub(super) fn encode_g1(point: G1Element) -> [u8; 32] {
    if bool::from(point.is_identity()) {
        let mut bytes = [0; 32];
        bytes[31] = INFINITY;
        return bytes;
    }
    let mut bytes = point.x.to_repr();
    if point.y > -point.y {
        bytes[31] |= NEGATIVE;
    }
    bytes
}

pub(super) fn encode_g2(point: G2Element) -> [u8; 64] {
    let mut bytes = [0; 64];
    if bool::from(point.is_identity()) {
        bytes[63] = INFINITY;
        return bytes;
    }
    bytes[..32].copy_from_slice(&point.x.c0.to_repr());
    bytes[32..].copy_from_slice(&point.x.c1.to_repr());
    // Pinned Fq2::Ord compares c1 before c0, exactly as Arkworks does.
    if point.y > -point.y {
        bytes[63] |= NEGATIVE;
    }
    bytes
}

pub(super) fn decode_g1(bytes: &[u8]) -> Result<G1Element, Error> {
    let (payload, infinity, negative) = flags::<32>(bytes)?;
    let point = if infinity {
        G1Element::identity()
    } else {
        let x = fq(&payload)?;
        let mut y = Option::<Fq>::from((x.square() * x + G1Element::b()).sqrt())
            .ok_or(Error::InvalidEncoding)?;
        if (y > -y) != negative {
            y = -y;
        }
        let point =
            Option::<G1Element>::from(G1Element::from_xy(x, y)).ok_or(Error::InvalidEncoding)?;
        validate_g1(point)?
    };
    if encode_g1(point).as_slice() != bytes {
        return Err(Error::InvalidEncoding);
    }
    Ok(point)
}

pub(super) fn decode_g2(bytes: &[u8]) -> Result<G2Element, Error> {
    let (payload, infinity, negative) = flags::<64>(bytes)?;
    let point = if infinity {
        G2Element::identity()
    } else {
        // Upstream Fq2::from_repr/from_bytes unwrap failed Fq component
        // parses. Each component must be checked independently here.
        let x = Fq2::new(fq(&payload[..32])?, fq(&payload[32..])?);
        let mut y = Option::<Fq2>::from((x.square() * x + G2Element::b()).sqrt())
            .ok_or(Error::InvalidEncoding)?;
        if (y > -y) != negative {
            y = -y;
        }
        let point =
            Option::<G2Element>::from(G2Element::from_xy(x, y)).ok_or(Error::InvalidEncoding)?;
        validate_g2(point)?
    };
    if encode_g2(point).as_slice() != bytes {
        return Err(Error::InvalidEncoding);
    }
    Ok(point)
}
