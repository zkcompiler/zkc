//! The installed width-16 KoalaBear Poseidon2 kernel against three references:
//! the upstream known-answer vector for the default constants, p3-poseidon2
//! 0.8.0's generic round functions and linear layers (a code path separate
//! from the optimized Monty31 layers the kernel links), and an integer
//! implementation of the round structure written from the Poseidon2 definition.
//! The round constants and the internal diagonal are the only shared inputs.
#[path = "domains/support.rs"]
mod support;

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
    KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL, KOALABEAR_POSEIDON2_RC_16_INTERNAL, KoalaBear,
};
use p3_poseidon2::{
    GenericPoseidon2LinearLayers, MDSMat4, add_rc_and_sbox_generic, external_initial_permute_state,
    external_terminal_permute_state, internal_permute_state,
};
use support::{backend, one};
use zkc_native::{Policy, Value};
use zkc_runtime::vm::OperationBinding;

const P: u64 = 2_130_706_433;

fn binding() -> OperationBinding {
    OperationBinding {
        contract: "hash.poseidon2_16".into(),
        arguments: vec!["koala-bear".into()],
        implementation: "plonky3/hash.poseidon2_16".into(),
    }
}

fn kernel(states: &[[u32; 16]]) -> Vec<[u32; 16]> {
    let input = Value::KoalaBearVector(
        states
            .iter()
            .flatten()
            .map(|x| KoalaBear::new(*x))
            .collect::<Vec<_>>()
            .into(),
    );
    let out = one(backend(Policy::default()), binding(), &[], vec![input])
        .0
        .unwrap();
    let Value::KoalaBearVector(out) = &out[0] else {
        panic!("vector result")
    };
    out.chunks(16)
        .map(|c| std::array::from_fn(|i| c[i].as_canonical_u32()))
        .collect()
}

/// p3-poseidon2's generic composition, which the optimized layers must match.
fn generic(state: [u32; 16]) -> [u32; 16] {
    let mut state = state.map(KoalaBear::new);
    external_initial_permute_state(
        &mut state,
        &KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
        add_rc_and_sbox_generic::<KoalaBear, KoalaBear, 3>,
        &MDSMat4,
    );
    internal_permute_state::<KoalaBear, KoalaBear, 16, 3>(
        &mut state,
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer,
        &KOALABEAR_POSEIDON2_RC_16_INTERNAL,
    );
    external_terminal_permute_state(
        &mut state,
        &KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
        add_rc_and_sbox_generic::<KoalaBear, KoalaBear, 3>,
        &MDSMat4,
    );
    state.map(|x| x.as_canonical_u32())
}

/// Integer Poseidon2: the external layer multiplies each four-element block
/// by circ(2, 3, 1, 1) and adds the sum of the blocks; the internal layer adds
/// the state sum to `V[i] * s[i]`; the S-box is the cube.
fn integer(state: [u32; 16]) -> [u32; 16] {
    let inverse = |x: u64| pow(x, P - 2);
    let half = inverse(2);
    let v: [u64; 16] = [
        P - 2,
        1,
        2,
        half,
        3,
        4,
        P - half,
        P - 3,
        P - 4,
        inverse(1 << 8),
        inverse(8),
        inverse(1 << 24),
        P - inverse(1 << 8),
        P - inverse(8),
        P - inverse(16),
        P - inverse(1 << 24),
    ];
    let constant = |x: KoalaBear| u64::from(x.as_canonical_u32());
    let external = |s: &mut [u64; 16]| {
        for block in s.chunks_mut(4) {
            let x = [block[0], block[1], block[2], block[3]];
            for (i, row) in [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]]
                .iter()
                .enumerate()
            {
                block[i] = row.iter().zip(x).map(|(m, y)| m * y % P).sum::<u64>() % P;
            }
        }
        let sums: [u64; 4] = std::array::from_fn(|j| (0..4).map(|b| s[4 * b + j]).sum::<u64>() % P);
        for (i, x) in s.iter_mut().enumerate() {
            *x = (*x + sums[i % 4]) % P;
        }
    };
    let cube = |x: u64| x * x % P * x % P;
    let mut s = state.map(u64::from);
    external(&mut s);
    for round in KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL {
        for (x, c) in s.iter_mut().zip(round) {
            *x = cube((*x + constant(c)) % P);
        }
        external(&mut s);
    }
    for c in KOALABEAR_POSEIDON2_RC_16_INTERNAL {
        s[0] = cube((s[0] + constant(c)) % P);
        let sum = s.iter().sum::<u64>() % P;
        for (x, d) in s.iter_mut().zip(v) {
            *x = (sum + d * *x % P) % P;
        }
    }
    for round in KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL {
        for (x, c) in s.iter_mut().zip(round) {
            *x = cube((*x + constant(c)) % P);
        }
        external(&mut s);
    }
    s.map(|x| x as u32)
}

fn pow(mut base: u64, mut exponent: u64) -> u64 {
    let mut result = 1;
    base %= P;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = result * base % P;
        }
        base = base * base % P;
        exponent >>= 1;
    }
    result
}

#[test]
fn installed_kernel_matches_the_upstream_known_answer() {
    // p3-koala-bear 0.8.0 src/poseidon2.rs, test_default_koalabear_poseidon2_width_16.
    let input = [
        894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
        19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
    ];
    let expected = [
        1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110, 1391183747, 351743874,
        1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461, 748270449,
        651545025,
    ];
    assert_eq!(kernel(&[input]), [expected]);
    assert_eq!(generic(input), expected);
    assert_eq!(integer(input), expected);
}

#[test]
fn batched_kernel_matches_generic_and_integer_permutations() {
    // A deterministic spread of states, including boundary residues.
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        (seed % P) as u32
    };
    let mut states: Vec<[u32; 16]> = (0..24).map(|_| std::array::from_fn(|_| next())).collect();
    states.push([0; 16]);
    states.push([(P - 1) as u32; 16]);
    states.push(std::array::from_fn(|i| i as u32));
    let actual = kernel(&states);
    assert_eq!(actual.len(), states.len());
    for (state, actual) in states.iter().zip(&actual) {
        assert_eq!(*actual, generic(*state));
        assert_eq!(*actual, integer(*state));
    }
    // The optimized internal layer agrees with the generic one on the diagonal.
    let mut a = std::array::from_fn::<KoalaBear, 16, _>(|i| KoalaBear::from_u32(3 + i as u32));
    let b = a;
    GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut a);
    let sum: KoalaBear = b.iter().copied().sum();
    assert_eq!(a[0], sum - b[0].double());
    assert_eq!(a[1], sum + b[1]);
}
