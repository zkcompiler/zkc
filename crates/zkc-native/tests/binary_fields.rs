//! The characteristic-two fields `gf2-64.pentanomial-4-3-1` and its cubic
//! extension, checked against an independent carry-less reference and against
//! Plonky3 0.8.0's `Poly64` and `Poly192`, through native kernels, codecs and
//! refusals of every operation that needs a prime or odd characteristic.
#[path = "domains/support.rs"]
mod support;

use p3_field::{Field, PrimeCharacteristicRing};
use serde_json::json;
use support::{assert_value, backend, one};
use zkc_kernels::plonky3::binary;
use zkc_native::{
    Binary64, Binary64Ext3, Policy, Value,
    domains::{BINARY64, BINARY64_EXT3},
};
use zkc_runtime::vm::{
    Backend, Identity, LogicalType, OperationBinding, PhysicalType, Type, Value as RuntimeValue,
};

const BASE: &str = "gf2-64.pentanomial-4-3-1";
const CUBIC: &str = "gf2-64.pentanomial-4-3-1.ext3-trinomial1";

/// Arithmetic in GF(2)[x]/(x^64 + x^4 + x^3 + x + 1) and in its extension by
/// y^3 + y + 1, written from the definitions: shift-and-add multiplication with
/// one reduction step per shift. Nothing here calls Plonky3 or the backend.
mod reference {
    /// The defining polynomial without its leading term: x^64 = x^4 + x^3 + x + 1.
    const TAIL: u64 = 0b1_1011;

    /// `a * x` reduced modulo the defining polynomial.
    pub fn times_x(a: u64) -> u64 {
        (a << 1) ^ if a >> 63 == 1 { TAIL } else { 0 }
    }
    pub fn mul(a: u64, b: u64) -> u64 {
        let (mut product, mut shifted) = (0, a);
        for i in 0..64 {
            if b >> i & 1 == 1 {
                product ^= shifted;
            }
            shifted = times_x(shifted);
        }
        product
    }
    /// `a^e` for an exponent given as little-endian 64-bit words.
    pub fn pow(a: u64, exponent: &[u64]) -> u64 {
        let (mut result, mut base) = (1, a);
        for word in exponent {
            for i in 0..64 {
                if word >> i & 1 == 1 {
                    result = mul(result, base);
                }
                base = mul(base, base);
            }
        }
        result
    }
    /// Inverse by Lagrange: a^(2^64 - 2).
    pub fn inverse(a: u64) -> u64 {
        pow(a, &[u64::MAX - 1])
    }

    pub type Cubic = [u64; 3];
    /// Schoolbook product, then y^3 = y + 1 and y^4 = y^2 + y.
    pub fn cubic_mul(a: Cubic, b: Cubic) -> Cubic {
        let mut c = [0u64; 5];
        for i in 0..3 {
            for j in 0..3 {
                c[i + j] ^= mul(a[i], b[j]);
            }
        }
        [c[0] ^ c[3], c[1] ^ c[3] ^ c[4], c[2] ^ c[4]]
    }
    pub fn cubic_pow(a: Cubic, exponent: &[u64]) -> Cubic {
        let (mut result, mut base) = ([1, 0, 0], a);
        for word in exponent {
            for i in 0..64 {
                if word >> i & 1 == 1 {
                    result = cubic_mul(result, base);
                }
                base = cubic_mul(base, base);
            }
        }
        result
    }
    /// Inverse by Lagrange: a^(2^192 - 2).
    pub fn cubic_inverse(a: Cubic) -> Cubic {
        cubic_pow(a, &[u64::MAX - 1, u64::MAX, u64::MAX])
    }

    /// Remainder of polynomial division over GF(2); bit `i` is the coefficient
    /// of `x^i`.
    pub fn rem(mut a: u128, b: u128) -> u128 {
        let degree = 127 - b.leading_zeros();
        while a != 0 && 127 - a.leading_zeros() >= degree {
            a ^= b << (127 - a.leading_zeros() - degree);
        }
        a
    }
    pub fn gcd(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            (a, b) = (b, rem(a, b));
        }
        a
    }
}

/// Deterministic test values; the generator is unrelated to either field.
struct Values(u64);
impl Values {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 29)
    }
    fn cubic(&mut self) -> [u64; 3] {
        [self.next(), self.next(), self.next()]
    }
}

fn base(bits: u64) -> Binary64 {
    binary::from_bits(bits)
}
fn cubic(words: [u64; 3]) -> Binary64Ext3 {
    binary::ext3_from_bits(words)
}
fn binding(field: &str, name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![field.into()],
        implementation: format!("plonky3/{name}"),
        physical_arguments: vec![],
    }
}
fn call(field: &str, name: &str, attrs: &[&str], args: Vec<Value>) -> Result<Vec<Value>, String> {
    one(
        backend(Policy::default()),
        binding(field, name),
        attrs,
        args,
    )
    .0
}
fn base_vector(values: &[u64]) -> Value {
    Value::binary64_vector(
        &values.iter().copied().map(base).collect::<Vec<_>>(),
        &Policy::default(),
    )
    .unwrap()
}
fn cubic_vector(values: &[[u64; 3]]) -> Value {
    Value::binary64_ext3_vector(
        &values.iter().copied().map(cubic).collect::<Vec<_>>(),
        &Policy::default(),
    )
    .unwrap()
}

#[test]
fn reference_defines_fields_of_the_stated_orders() {
    // Rabin's test: a degree-64 polynomial over GF(2) is irreducible exactly
    // when x^(2^64) = x modulo it and gcd(x^(2^32) - x, it) = 1.
    let mut power = 2u64; // x
    for _ in 0..32 {
        power = reference::mul(power, power);
    }
    let modulus = (1u128 << 64) | 0b1_1011;
    assert_eq!(reference::gcd(u128::from(power ^ 2), modulus), 1);
    for _ in 0..32 {
        power = reference::mul(power, power);
    }
    assert_eq!(power, 2);
    // A root of y^3 + y + 1 in GF(2^64) would lie in GF(8) and so in GF(2),
    // and the cubic has none there. Lagrange holds for the extension.
    for y in [0u64, 1] {
        assert_eq!(reference::mul(reference::mul(y, y), y) ^ y ^ 1, 1);
    }
    let mut values = Values(3);
    for _ in 0..4 {
        let a = values.cubic();
        let order = [u64::MAX, u64::MAX, u64::MAX];
        assert_eq!(reference::cubic_pow(a, &order), [1, 0, 0]);
        assert_eq!(
            reference::cubic_mul(a, reference::cubic_inverse(a)),
            [1, 0, 0]
        );
    }
    // x * x^63 = x^64 = x^4 + x^3 + x + 1, and y * y^2 = y + 1.
    assert_eq!(reference::mul(2, 1 << 63), 0x1b);
    assert_eq!(reference::cubic_mul([0, 1, 0], [0, 0, 1]), [1, 1, 0]);
}

#[test]
fn plonky3_arithmetic_agrees_with_the_carry_less_reference() {
    let mut values = Values(17);
    for _ in 0..256 {
        let (a, b) = (values.next(), values.next());
        assert_eq!(binary::bits(base(a) * base(b)), reference::mul(a, b));
        assert_eq!(binary::bits(base(a) + base(b)), a ^ b);
        assert_eq!(binary::bits(base(a) - base(b)), a ^ b);
        assert_eq!(binary::bits(-base(a)), a);
        if a != 0 {
            assert_eq!(
                binary::bits(base(a).try_inverse().unwrap()),
                reference::inverse(a)
            );
        }
        let (c, d) = (values.cubic(), values.cubic());
        assert_eq!(
            binary::ext3_bits(cubic(c) * cubic(d)),
            reference::cubic_mul(c, d)
        );
        assert_eq!(
            binary::ext3_bits(cubic(c) + cubic(d)),
            [c[0] ^ d[0], c[1] ^ d[1], c[2] ^ d[2]]
        );
    }
    for _ in 0..8 {
        let c = values.cubic();
        assert_eq!(
            binary::ext3_bits(cubic(c).try_inverse().unwrap()),
            reference::cubic_inverse(c)
        );
    }
    assert!(Binary64::ZERO.try_inverse().is_none());
    assert!(Binary64Ext3::ZERO.try_inverse().is_none());
    // Integer casts go through GF(2): only the parity of the argument remains.
    assert_eq!(Binary64::from_u64(5), Binary64::ONE);
    assert_eq!(Binary64::from_u64(6), Binary64::ZERO);
}

#[test]
fn byte_and_serde_forms_agree_with_plonky3() {
    use p3_field::RawDataSerializable;
    // Plonky3's own raw bytes and serde values fix the coordinate order and
    // byte order that the wire frames and byte codecs use.
    let mut values = Values(53);
    for _ in 0..64 {
        let k = base(values.next());
        let c = cubic(values.cubic());
        assert_eq!(
            k.into_bytes().into_iter().collect::<Vec<u8>>(),
            binary::encode(k)
        );
        assert_eq!(
            c.into_bytes().into_iter().collect::<Vec<u8>>(),
            binary::encode_ext3(c)
        );
        assert_eq!(
            <Binary64Ext3 as RawDataSerializable>::NUM_BYTES,
            binary::EXT3_WIDTH
        );
        assert_eq!(serde_json::to_value(k).unwrap(), json!(binary::bits(k)));
        assert_eq!(
            serde_json::to_value(c).unwrap(),
            json!(binary::ext3_bits(c))
        );
        let back: Binary64Ext3 = serde_json::from_value(json!(binary::ext3_bits(c))).unwrap();
        assert_eq!(back, c);
    }
}

#[test]
fn identities_signatures_and_capabilities_are_nominal() {
    let b = backend(Policy::default());
    let k = Identity::parse(BASE).unwrap();
    let e = Identity::parse(CUBIC).unwrap();
    assert_eq!((k, e), (Identity::Binary64, Identity::Binary64Ext3));
    assert_eq!(e.base_field(), Some(k));
    assert_eq!(k.base_field(), None);
    for identity in [k, e] {
        assert_eq!(identity.scalar_field(), Some(identity));
        assert_eq!(identity.provider(), Some("plonky3"));
        assert_eq!(identity.group(), None);
        assert_eq!(identity.transcript(), None);
        assert!(!identity.has_characteristic_not_two());
        assert!(!identity.is_prime_field());
        assert!(!identity.has_residue_coordinates());
    }
    assert_eq!(k.bit_pattern_width(), Some(64));
    assert_eq!(e.bit_pattern_width(), Some(192));
    for (domain, name) in [(BINARY64, BASE), (BINARY64_EXT3, CUBIC)] {
        for kind in [
            Type::Field,
            Type::Vector,
            Type::Polynomial,
            Type::Round,
            Type::Matrix,
        ] {
            let ty = domain.physical(kind).unwrap();
            assert_eq!(PhysicalType::parse(&ty.spelling()).unwrap(), ty);
            assert!(ty.spelling().contains(name));
        }
        for kind in [
            Type::Rng,
            Type::Nonce,
            Type::Transcript,
            Type::Table,
            Type::Point,
            Type::Group,
            Type::Groups,
            Type::Commitment,
            Type::Proof,
        ] {
            assert!(LogicalType::new(kind, domain.field).is_err());
            assert!(domain.physical(kind).is_none());
        }
    }
    let installed = |field: &str, name: &str| {
        let bind = binding(field, name);
        let signature = b.binding_signature(&bind);
        assert_eq!(bind.signature().ok(), signature, "{field} {name}");
        signature.is_some()
    };
    for field in [BASE, CUBIC] {
        for name in [
            "field.constant",
            "field.from_index",
            "field.add",
            "field.sub",
            "field.mul",
            "field.neg",
            "field.inverse",
            "field.equal",
            "vector.constant",
            "vector.mul",
            "vector.dot",
            "vector.sum",
            "vector.product",
            "vector.inverse",
            "vector.prefix_product",
            "vector.kronecker",
            "vector.bit_reverse",
            "poly.from_coefficients",
            "poly.coefficients",
            "poly.univariate_evaluate",
            "poly.boundary",
            "poly.round_evaluate",
            "poly.divide_opening",
            "matrix.mul_vector",
            "matrix.bilinear",
            "matrix.identity_check",
            "encoding.field_le",
            "encoding.field_from_le",
            "encoding.fields_le",
            "encoding.fields_from_le",
        ] {
            assert!(installed(field, name), "{field} {name}");
        }
        // Two-adic domains, folding by halving, Montgomery residues, residue
        // arenas and relation views need a prime or odd characteristic.
        for name in [
            "poly.coset_evaluate",
            "poly.coset_interpolate",
            "poly.domain_point",
            "poly.domain_root",
            "poly.domain_points",
            "poly.even_odd_fold",
            "poly.opening_quotient",
            "encoding.field_montgomery_le",
            "encoding.field_from_montgomery_le",
            "encoding.fields_montgomery_le",
            "encoding.fields_from_montgomery_le",
            "encoding.field_reduce_le",
            "ring.point",
            "ring.rows",
            "relation.table_point",
            "random.draw",
            "random.index",
            "hash.poseidon2_16",
            "fixed_vector.dot",
        ] {
            assert!(!installed(field, name), "{field} {name}");
        }
        for provider in ["arkworks", "dalek", "uninstalled"] {
            let mut wrong = binding(field, "field.mul");
            wrong.implementation = format!("{provider}/field.mul");
            assert!(b.binding_signature(&wrong).is_none());
        }
    }
    // Only the cubic extension embeds, and only its declared base field.
    assert!(installed(CUBIC, "field.embed") && installed(CUBIC, "vector.embed"));
    assert!(!installed(BASE, "field.embed") && !installed(BASE, "vector.embed"));
    let embed = binding(CUBIC, "field.embed").signature().unwrap();
    assert_eq!(embed.inputs[0].logical().identity(), Identity::Binary64);
    assert_eq!(
        embed.outputs[0].logical().identity(),
        Identity::Binary64Ext3
    );
}

#[test]
fn field_kernels_match_the_reference() {
    let mut values = Values(29);
    for _ in 0..24 {
        let (a, b) = (values.next() | 2, values.next());
        let k = |x| Value::Binary64Field(base(x));
        assert_value(
            &call(BASE, "field.mul", &[], vec![k(a), k(b)]).unwrap()[0],
            &k(reference::mul(a, b)),
        );
        assert_value(
            &call(BASE, "field.add", &[], vec![k(a), k(b)]).unwrap()[0],
            &k(a ^ b),
        );
        assert_value(
            &call(BASE, "field.sub", &[], vec![k(a), k(b)]).unwrap()[0],
            &k(a ^ b),
        );
        assert_value(&call(BASE, "field.neg", &[], vec![k(a)]).unwrap()[0], &k(a));
        assert_value(
            &call(BASE, "field.inverse", &[], vec![k(a)]).unwrap()[0],
            &k(reference::inverse(a)),
        );
        let (c, d) = (values.cubic(), values.cubic());
        let e = |x| Value::Binary64Ext3Field(cubic(x));
        assert_value(
            &call(CUBIC, "field.mul", &[], vec![e(c), e(d)]).unwrap()[0],
            &e(reference::cubic_mul(c, d)),
        );
        assert_value(
            &call(CUBIC, "field.inverse", &[], vec![e(c)]).unwrap()[0],
            &e(reference::cubic_inverse(c)),
        );
    }
    for field in [BASE, CUBIC] {
        let zero = if field == BASE {
            Value::Binary64Field(Binary64::ZERO)
        } else {
            Value::Binary64Ext3Field(Binary64Ext3::ZERO)
        };
        assert_eq!(
            call(field, "field.inverse", &[], vec![zero]).unwrap_err(),
            "refused:zero-inverse"
        );
    }
    // Natural casts land in GF(2).
    for (n, bit) in [(0, 0), (1, 1), (2, 0), (5, 1), (u64::MAX, 1)] {
        assert_value(
            &call(BASE, "field.from_index", &[], vec![Value::Index(n)]).unwrap()[0],
            &Value::Binary64Field(base(bit)),
        );
    }
    // The embedding sends a to (a, 0, 0).
    let a = values.next();
    assert_value(
        &call(
            CUBIC,
            "field.embed",
            &[],
            vec![Value::Binary64Field(base(a))],
        )
        .unwrap()[0],
        &Value::Binary64Ext3Field(cubic([a, 0, 0])),
    );
    assert_value(
        &call(CUBIC, "vector.embed", &[], vec![base_vector(&[a, 7])]).unwrap()[0],
        &cubic_vector(&[[a, 0, 0], [7, 0, 0]]),
    );
}

#[test]
fn bit_pattern_literals_name_every_element() {
    let k = |x| Value::Binary64Field(base(x));
    for (literal, bits) in [
        ("0", 0),
        ("1", 1),
        ("0x2", 2),
        ("0x1b", 0x1b),
        ("0x8000000000000000", 1 << 63),
        ("0xffffffffffffffff", u64::MAX),
    ] {
        assert_value(
            &call(BASE, "field.constant", &[literal], vec![]).unwrap()[0],
            &k(bits),
        );
    }
    // y is bit 64 and y^2 bit 128; y * y^2 = y + 1.
    let y = call(CUBIC, "field.constant", &["0x10000000000000000"], vec![]).unwrap();
    let y2 = call(
        CUBIC,
        "field.constant",
        &["0x100000000000000000000000000000000"],
        vec![],
    )
    .unwrap();
    let product = call(CUBIC, "field.mul", &[], vec![y[0].clone(), y2[0].clone()]).unwrap();
    assert_value(&product[0], &Value::Binary64Ext3Field(cubic([1, 1, 0])));
    let top = format!("0x{}", "f".repeat(48));
    assert_value(
        &call(CUBIC, "field.constant", &[&top], vec![]).unwrap()[0],
        &Value::Binary64Ext3Field(cubic([u64::MAX; 3])),
    );
    assert_value(
        &call(BASE, "vector.constant", &["0", "1", "0x1b"], vec![]).unwrap()[0],
        &base_vector(&[0, 1, 0x1b]),
    );
    // One spelling per element: decimals other than 0 and 1, bit patterns of
    // zero and one, leading zeros, uppercase and out-of-width values refuse
    // at program admission and in the backend's own attribute check.
    let binding_for = |field: &str| binding(field, "field.constant");
    let admits = |field: &str, literal: &str| {
        let binding = binding_for(field);
        let signature = binding.signature().unwrap();
        let program = support::program(
            &[binding],
            &[],
            vec![json!(["op", "site", "b0", [literal], [], ["o0"]])],
            &signature.outputs,
            &["o0".to_string()],
        );
        let admitted = zkc_runtime::vm::Program::decode(&program, zkc_native::native_contracts())
            .and_then(|program| program.check_installation(&backend(Policy::default())))
            .is_ok();
        // The backend checks the attributes it is handed, independently of
        // admission: run an admitted constant with the literal substituted.
        let mut controlled = support::Controlled::new(backend(Policy::default()));
        controlled.attributes = Some(vec![literal.to_string()]);
        let valid = if field.starts_with("koala-bear") {
            "2"
        } else {
            "0x2"
        };
        let native = one(controlled, binding_for(field), &[valid], vec![])
            .0
            .is_ok();
        assert_eq!(admitted, native, "{field} {literal}");
        admitted
    };
    for (field, literal) in [(BASE, "0"), (BASE, "1"), (BASE, "0x2"), (CUBIC, "0x1b")] {
        assert!(admits(field, literal), "{field} {literal}");
    }
    for (field, literal) in [
        (BASE, "2"),
        (BASE, "27"),
        (BASE, "0x0"),
        (BASE, "0x1"),
        (BASE, "0x01b"),
        (BASE, "0x1B"),
        (BASE, "0X1b"),
        (BASE, "0x"),
        (BASE, "0x10000000000000000"),
        (BASE, "-0x2"),
        (CUBIC, "3"),
        (CUBIC, "0x1"),
        (CUBIC, &format!("0x1{}", "0".repeat(48))),
    ] {
        assert!(!admits(field, literal), "{field} {literal}");
    }
    // Prime fields keep decimal literals only.
    assert!(!admits("koala-bear", "0x2"));
    assert!(admits("koala-bear", "2"));
}

#[test]
fn vector_polynomial_and_matrix_kernels_match_the_reference() {
    let mut values = Values(41);
    let a: Vec<u64> = (0..5).map(|_| values.next()).collect();
    let b: Vec<u64> = (0..5).map(|_| values.next()).collect();
    let products: Vec<u64> = a
        .iter()
        .zip(&b)
        .map(|(x, y)| reference::mul(*x, *y))
        .collect();
    assert_value(
        &call(
            BASE,
            "vector.mul",
            &[],
            vec![base_vector(&a), base_vector(&b)],
        )
        .unwrap()[0],
        &base_vector(&products),
    );
    let dot = products.iter().fold(0, |s, x| s ^ x);
    assert_value(
        &call(
            BASE,
            "vector.dot",
            &[],
            vec![base_vector(&a), base_vector(&b)],
        )
        .unwrap()[0],
        &Value::Binary64Field(base(dot)),
    );
    let product = a.iter().fold(1, |p, x| reference::mul(p, *x));
    assert_value(
        &call(BASE, "vector.product", &[], vec![base_vector(&a)]).unwrap()[0],
        &Value::Binary64Field(base(product)),
    );
    // A polynomial over the extension evaluated by Horner in the reference.
    let coefficients: Vec<[u64; 3]> = (0..4).map(|_| values.cubic()).collect();
    let point = values.cubic();
    let expected = coefficients.iter().rev().fold([0; 3], |acc, c| {
        let s = reference::cubic_mul(acc, point);
        [s[0] ^ c[0], s[1] ^ c[1], s[2] ^ c[2]]
    });
    let polynomial = call(
        CUBIC,
        "poly.from_coefficients",
        &[],
        vec![cubic_vector(&coefficients)],
    )
    .unwrap()
    .remove(0);
    assert_value(
        &call(
            CUBIC,
            "poly.univariate_evaluate",
            &[],
            vec![polynomial, Value::Binary64Ext3Field(cubic(point))],
        )
        .unwrap()[0],
        &Value::Binary64Ext3Field(cubic(expected)),
    );
    // A sumcheck round in coefficient form: p(0) + p(1) is the boundary.
    let round = [values.next(), values.next(), values.next()];
    assert_value(
        &call(
            BASE,
            "poly.boundary",
            &[],
            vec![Value::Binary64Round(round.map(base))],
        )
        .unwrap()[0],
        &Value::Binary64Field(base(round[0] ^ round[0] ^ round[1] ^ round[2])),
    );
    let matrix = Value::binary64_matrix(
        2,
        2,
        &[(0, 1, base(a[0])), (1, 0, base(a[1]))],
        &Policy::default(),
    )
    .unwrap();
    assert_value(
        &call(
            BASE,
            "matrix.mul_vector",
            &[],
            vec![matrix, base_vector(&b[..2])],
        )
        .unwrap()[0],
        &base_vector(&[reference::mul(a[0], b[1]), reference::mul(a[1], b[0])]),
    );
}

#[test]
fn wire_frames_round_trip_with_their_own_tags() {
    let b = backend(Policy::default());
    let k = 0x0123_4567_89ab_cdef;
    let c = [k, 0x1b, u64::MAX];
    assert_eq!(binary::encode(base(k)), k.to_le_bytes());
    assert_eq!(binary::decode(&k.to_le_bytes()).unwrap(), base(k));
    let flat: Vec<u8> = c.iter().flat_map(|w| w.to_le_bytes()).collect();
    assert_eq!(binary::encode_ext3(cubic(c)).to_vec(), flat);
    assert_eq!(binary::decode_ext3(&flat).unwrap(), cubic(c));
    for n in [0, 7, 9, 16, 23, 25] {
        assert!(binary::decode(&vec![0; n]).is_err() || n == 8);
        assert!(binary::decode_ext3(&vec![0; n]).is_err());
    }
    let cases = vec![
        (Value::Binary64Field(base(k)), Some((73, 14))),
        (base_vector(&[k, 2, 0]), Some((74, 10 + 3 * 8))),
        (
            Value::binary64_matrix(2, 3, &[(1, 2, base(k))], &Policy::default()).unwrap(),
            Some((75, 18 + 16)),
        ),
        (Value::Binary64Ext3Field(cubic(c)), Some((76, 30))),
        (cubic_vector(&[c, [1, 0, 0]]), Some((77, 10 + 2 * 24))),
        (
            Value::binary64_ext3_matrix(1, 1, &[(0, 0, cubic(c))], &Policy::default()).unwrap(),
            Some((78, 18 + 32)),
        ),
        (Value::Binary64Polynomial(vec![base(k)].into()), None),
        (Value::Binary64Round([base(k); 3]), None),
        (Value::Binary64Ext3Polynomial(vec![cubic(c)].into()), None),
        (Value::Binary64Ext3Round([cubic(c); 3]), None),
    ];
    for (value, frame) in cases {
        let ty = value.physical_type();
        let Some((tag, length)) = frame else {
            assert!(!zkc_native::has_native_wire(&ty));
            assert!(b.encode_native_value(&value).is_err());
            continue;
        };
        let bytes = b.encode_native_value(&value).unwrap();
        assert_eq!(&bytes[..6], &[b'Z', b'K', b'C', b'V', 0, tag]);
        assert_eq!(bytes.len(), length);
        assert_value(&value, &b.decode_native_value(&ty, &bytes).unwrap());
        for len in 0..bytes.len() {
            assert!(b.decode_native_value(&ty, &bytes[..len]).is_err());
        }
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(b.decode_native_value(&ty, &extra).is_err());
        // No other field family of the same kind reads this frame.
        for other in [
            BINARY64,
            BINARY64_EXT3,
            zkc_native::domains::KOALA_BEAR,
            zkc_native::domains::KOALA_BEAR_EXT4,
            zkc_native::domains::KOALA_BEAR_EXT8,
        ] {
            let Some(other) = other.physical(ty.kind()) else {
                continue;
            };
            if other != ty {
                assert!(b.decode_native_value(&other, &bytes).is_err());
            }
        }
        // The readable form is hexadecimal and lowers to the same frame.
        let readable = serde_json::to_value(b.encode_readable_value(&value).unwrap()).unwrap();
        assert_eq!(
            zkc_native::readable_wire(&ty, &readable, bytes.len()).unwrap(),
            bytes
        );
    }
}

#[test]
fn readable_values_are_bit_patterns_not_residues() {
    let b = backend(Policy::default());
    let readable =
        |value: &Value| serde_json::to_value(b.encode_readable_value(value).unwrap()).unwrap();
    assert_eq!(readable(&Value::Binary64Field(base(0))), json!("0x0"));
    assert_eq!(readable(&Value::Binary64Field(base(1))), json!("0x1"));
    assert_eq!(readable(&Value::Binary64Field(base(0x1b))), json!("0x1b"));
    assert_eq!(
        readable(&Value::Binary64Ext3Field(cubic([2, 0, u64::MAX]))),
        json!(["0x2", "0x0", "0xffffffffffffffff"])
    );
    assert_eq!(readable(&base_vector(&[3, 0x80])), json!(["0x3", "0x80"]));
    let field = BINARY64.physical(Type::Field).unwrap();
    let cubic_field = BINARY64_EXT3.physical(Type::Field).unwrap();
    // A base element embeds in the extension's readable input.
    assert_eq!(
        zkc_native::readable_wire(&cubic_field, &json!("0x1b"), 64).unwrap(),
        b.encode_native_value(&Value::Binary64Ext3Field(cubic([0x1b, 0, 0])))
            .unwrap()
    );
    for bad in [
        json!("27"),
        json!("0"),
        json!("0x"),
        json!("0x01"),
        json!("0X1"),
        json!("0x1B"),
        json!("0x10000000000000000"),
        json!(27),
        json!(["0x1"]),
    ] {
        assert!(
            zkc_native::readable_wire(&field, &bad, 64).is_err(),
            "{bad}"
        );
    }
    for bad in [json!(["0x1", "0x2"]), json!(["0x1", "0x2", "3"])] {
        assert!(zkc_native::readable_wire(&cubic_field, &bad, 64).is_err());
    }
}

#[test]
fn bit_pattern_byte_codecs_are_little_endian_and_total() {
    let k = 0x0011_2233_4455_6677u64;
    let encoded = call(
        BASE,
        "encoding.field_le",
        &[],
        vec![Value::Binary64Field(base(k))],
    )
    .unwrap();
    assert_value(&encoded[0], &Value::Bytes(k.to_le_bytes().to_vec().into()));
    let c = [k, 1, 1 << 63];
    let bytes: Vec<u8> = c.iter().flat_map(|w| w.to_le_bytes()).collect();
    let decoded = call(
        CUBIC,
        "encoding.field_from_le",
        &[],
        vec![Value::Bytes(bytes.clone().into())],
    )
    .unwrap();
    assert_value(&decoded[0], &Value::Bool(true));
    assert_value(&decoded[1], &Value::Binary64Ext3Field(cubic(c)));
    // Every pattern of the exact width decodes; only the length can fail.
    for n in [0, 8, 23, 25] {
        let decoded = call(
            CUBIC,
            "encoding.field_from_le",
            &[],
            vec![Value::Bytes(vec![0xff; n].into())],
        )
        .unwrap();
        assert_value(&decoded[0], &Value::Bool(false));
        assert_value(&decoded[1], &Value::Binary64Ext3Field(Binary64Ext3::ZERO));
    }
    let many = call(
        BASE,
        "encoding.fields_from_le",
        &[],
        vec![Value::Bytes(
            [[0xffu8; 8], [2, 0, 0, 0, 0, 0, 0, 0]].concat().into(),
        )],
    )
    .unwrap();
    assert_value(&many[0], &Value::Bool(true));
    assert_value(&many[1], &base_vector(&[u64::MAX, 2]));
    let ragged = call(
        BASE,
        "encoding.fields_from_le",
        &[],
        vec![Value::Bytes(vec![0; 12].into())],
    )
    .unwrap();
    assert_value(&ragged[0], &Value::Bool(false));
    assert_value(&ragged[1], &base_vector(&[]));
    let back = call(BASE, "encoding.fields_le", &[], vec![many[1].clone()]).unwrap();
    assert_value(
        &back[0],
        &Value::Bytes([[0xffu8; 8], [2, 0, 0, 0, 0, 0, 0, 0]].concat().into()),
    );
}

#[test]
fn ring_formulas_form_but_ring_kernels_refuse() {
    // A Ring formula over a binary field forms, with natural literals only; a
    // bit-pattern constant is a bound input. The Ring row provider substitutes
    // integer residue coordinates, so its kernels refuse binary carriers.
    let ring = format!(
        r#"["zkc.ring/0",["{BASE}"],[["input",0],["constant","{BASE}","1"],["mul",0,1]],[2]]"#
    );
    assert!(zkc_runtime::ring::Expression::parse(&ring).is_ok());
    for literal in ["2", "0x1b"] {
        let constant = ring.replace(r#""1"]"#, &format!(r#""{literal}"]"#));
        assert_eq!(
            zkc_runtime::ring::Expression::parse(&constant)
                .unwrap_err()
                .0,
            "ring-literal"
        );
    }
    let b = backend(Policy::default());
    for field in [BASE, CUBIC] {
        for name in [
            "ring.point",
            "ring.rows",
            "ring.coefficients",
            "ring.affine_sum",
        ] {
            let bind = binding(field, name);
            assert!(b.binding_signature(&bind).is_none(), "{field} {name}");
        }
    }
}

/// Plonky3's `halve` and `div_2exp_u64` panic in characteristic two. Run every
/// kernel installed for the binary fields on ordinary operands: each returns a
/// result or a refusal, and none reaches a halving step.
#[test]
fn every_installed_binary_kernel_returns_without_panicking() {
    use zkc_runtime::vm::AttributeRule as A;
    const DIGEST: &str = "00000000000000000000000000000000000000000000000000000000000000ab";
    let b = backend(Policy::default());
    let mut exercised = Vec::new();
    for field in [BASE, CUBIC] {
        let cubic_field = field == CUBIC;
        let element = |bits: u64| {
            if cubic_field {
                Value::Binary64Ext3Field(cubic([bits, 1, 0]))
            } else {
                Value::Binary64Field(base(bits))
            }
        };
        let vector = |bits: &[u64]| {
            if cubic_field {
                cubic_vector(&bits.iter().map(|b| [*b, 1, 0]).collect::<Vec<_>>())
            } else {
                base_vector(bits)
            }
        };
        for (implementation, contract) in b.installed_implementations() {
            let contract = contract.to_string();
            if !implementation.starts_with("plonky3/") {
                continue;
            }
            let bind = binding(field, &contract);
            let Some(signature) = b.binding_signature(&bind) else {
                continue;
            };
            let args = signature
                .inputs
                .iter()
                .map(|ty| match ty.kind() {
                    Type::Field if ty.logical().identity() == Identity::Binary64 => {
                        Value::Binary64Field(base(0x1b))
                    }
                    Type::Vector if ty.logical().identity() == Identity::Binary64 => {
                        base_vector(&[2, 3, 5, 7])
                    }
                    Type::Field => element(0x1b),
                    Type::Vector => vector(&[2, 3, 5, 7]),
                    Type::Polynomial if cubic_field => Value::Binary64Ext3Polynomial(
                        vec![cubic([1, 0, 0]), cubic([3, 0, 0])].into(),
                    ),
                    Type::Polynomial => Value::Binary64Polynomial(vec![base(1), base(3)].into()),
                    Type::Round if cubic_field => Value::Binary64Ext3Round([
                        cubic([1, 0, 0]),
                        cubic([2, 0, 0]),
                        cubic([3, 0, 0]),
                    ]),
                    Type::Round => Value::Binary64Round([base(1), base(2), base(3)]),
                    Type::Matrix if cubic_field => Value::binary64_ext3_matrix(
                        4,
                        4,
                        &[(0, 1, cubic([2, 0, 0])), (3, 2, cubic([5, 1, 0]))],
                        &Policy::default(),
                    )
                    .unwrap(),
                    Type::Matrix => Value::binary64_matrix(
                        4,
                        4,
                        &[(0, 1, base(2)), (3, 2, base(5))],
                        &Policy::default(),
                    )
                    .unwrap(),
                    Type::Index => Value::Index(1),
                    Type::Bool => Value::Bool(true),
                    Type::Bytes => Value::Bytes(vec![7; if cubic_field { 24 } else { 8 }].into()),
                    other => panic!("{contract}: unexpected operand kind {other:?}"),
                })
                .collect::<Vec<_>>();
            let attributes: &[&str] = match signature.attributes {
                A::None => &[],
                A::Binary64Literal | A::Binary64Ext3Literal => &["0x1b"],
                A::Binary64Literals | A::Binary64Ext3Literals => &["1", "0x2", "0x1b", "0"],
                A::NaturalIndex | A::Unsigned64 => &["1"],
                A::NaturalIndices => &["0", "3"],
                A::ScatterShape => &["4", "3", "2", "1", "0"],
                A::MatrixDimensions => &["4", "4"],
                A::MatrixShape => &["4", "4", "0"],
                A::MatrixIdentity => &[DIGEST],
                other => panic!("{contract}: unexpected attribute rule {other:?}"),
            };
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                one(backend(Policy::default()), bind.clone(), attributes, args)
                    .0
                    .is_ok()
            }));
            assert!(outcome.is_ok(), "{field} {contract} panicked");
            exercised.push((field, contract, outcome.unwrap()));
        }
    }
    // Every installed binary kernel was reached, and arithmetic succeeded.
    let succeeded = |field: &str, name: &str| {
        exercised
            .iter()
            .any(|(f, c, ok)| *f == field && c == name && *ok)
    };
    for field in [BASE, CUBIC] {
        for name in [
            "field.mul",
            "field.inverse",
            "vector.inverse",
            "vector.powers",
            "vector.geometric",
            "vector.prefix_product",
            "poly.boundary",
            "matrix.bilinear",
        ] {
            assert!(succeeded(field, name), "{field} {name}");
        }
    }
    assert!(succeeded(CUBIC, "vector.embed"));
    assert!(exercised.len() > 100, "{}", exercised.len());
}
