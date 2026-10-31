//! Exact quartic installation through native admission, codecs and execution.
#[path = "domains/support.rs"]
mod support;

use sha3::{Digest as _, Keccak256};
use support::{Controlled, backend, one};
use zkc_cpu::{KoalaBear, KoalaBearExt4, Policy, Value, oracle::Domain};
use zkc_runtime::vm::{
    Backend, Identity, LogicalType, OperationBinding, PhysicalType, ServiceContract, Type,
    Value as _,
};

const FIELD: &str = "koala-bear.ext4-binomial3";
const SCHEME: &str = "rows.merkle-keccak256.koala-bear.ext4-binomial3/0";
const SUITE: &str = "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0";
const MODULUS: u32 = 2_130_706_433;
fn binding(name: &str, identity: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![identity.into()],
        implementation: format!("plonky3/{name}"),
        physical_arguments: vec![],
    }
}
fn call(name: &str, args: Vec<Value>) -> Vec<Value> {
    one(backend(Policy::default()), binding(name, SCHEME), &[], args)
        .0
        .unwrap()
}
fn coordinates(count: usize) -> Vec<[u32; 4]> {
    (0..count)
        .map(|i| {
            [
                i as u32,
                MODULUS - 1,
                (17 * i + 3) as u32,
                (7 * i + 5) as u32,
            ]
        })
        .collect()
}
fn vector(words: &[[u32; 4]]) -> Value {
    Value::KoalaBearExt4Vector(
        words
            .iter()
            .map(|w| KoalaBearExt4::from(w.map(KoalaBear::new)))
            .collect::<Vec<_>>()
            .into(),
    )
}
/// Scalar byte reference independent of the kernel's leaf codec and batched tree.
fn reference(width: usize, height: usize, words: &[[u32; 4]]) -> Vec<Vec<[u8; 32]>> {
    let codec = b"koala-bear.ext4-binomial3.ascending-u32le/0";
    let mut bottom: Vec<[u8; 32]> = words
        .chunks(width)
        .map(|row| {
            let mut hash = Keccak256::new();
            hash.update(b"zkc.oracle.keccak256.leaf/0\0");
            hash.update((codec.len() as u64).to_le_bytes());
            hash.update(codec);
            hash.update((width as u64).to_le_bytes());
            hash.update((height as u64).to_le_bytes());
            for word in row.iter().flatten() {
                hash.update(word.to_le_bytes());
            }
            hash.finalize().into()
        })
        .collect();
    let mut layers = vec![];
    loop {
        if bottom.len() > 1 && bottom.len() % 2 == 1 {
            bottom.push([0; 32]);
        }
        layers.push(bottom.clone());
        if bottom.len() == 1 {
            return layers;
        }
        bottom = bottom
            .chunks(2)
            .map(|pair| {
                let mut hash = Keccak256::new();
                hash.update(b"zkc.oracle.keccak256.node/0\0");
                hash.update(pair[0]);
                hash.update(pair[1]);
                hash.finalize().into()
            })
            .collect();
    }
}
#[test]
fn installed_trees_match_scalar_bytes_across_batch_tails_and_wide_rows() {
    for (width, height) in [(1, 1), (2, 3), (3, 7), (8, 8), (9, 9), (17, 17), (1024, 9)] {
        let words = coordinates(width * height);
        let layers = reference(width, height, &words);
        let values = call(
            "oracle.commit",
            vec![vector(&words), Value::Index(width as u64)],
        );
        let Value::OracleRoot(Domain::Quartic, root) = values[0] else {
            panic!("quartic root")
        };
        assert_eq!(root, layers.last().unwrap()[0], "{width}x{height}");
        for position in [0, height / 2, height - 1] {
            let opening = call(
                "oracle.open",
                vec![values[1].clone(), Value::Index(position as u64)],
            );
            let Value::OraclePath(Domain::Quartic, path) = &opening[1] else {
                panic!("quartic path")
            };
            let expected: Vec<_> = layers[..layers.len() - 1]
                .iter()
                .enumerate()
                .map(|(depth, layer)| layer[(position >> depth) ^ 1])
                .collect();
            assert_eq!(path.as_ref(), expected);
            support::assert_value(
                &opening[0],
                &vector(&words[position * width..(position + 1) * width]),
            );
            let mut args = vec![
                values[0].clone(),
                Value::Index(width as u64),
                Value::Index(height as u64),
                Value::Index(position as u64),
                opening[0].clone(),
                opening[1].clone(),
            ];
            assert!(matches!(
                call("oracle.check", args.clone())[0],
                Value::Bool(true)
            ));
            args[4] = vector(&coordinates(width));
            if position != 0 {
                assert!(matches!(
                    call("oracle.check", args.clone())[0],
                    Value::Bool(false)
                ));
            }
            args[4] = opening[0].clone();
            args[2] = Value::Index((height + 1) as u64);
            assert!(matches!(call("oracle.check", args)[0], Value::Bool(false)));
        }
    }
}
#[test]
fn quartet_wire_preserves_coordinates_and_refuses_every_noncanonical_slot() {
    let b = backend(Policy::default());
    let words = [[1, 0x0403_0201, MODULUS - 1, 7]];
    for value in [
        Value::KoalaBearExt4Field(KoalaBearExt4::from(words[0].map(KoalaBear::new))),
        vector(&words),
    ] {
        let bytes = b.encode_native_value(&value).unwrap();
        let prefix = if value.ty() == Type::Field { 6 } else { 10 };
        assert_eq!(
            &bytes[prefix..],
            words[0]
                .iter()
                .flat_map(|w| w.to_le_bytes())
                .collect::<Vec<_>>()
        );
        for coordinate in 0..4 {
            for word in [MODULUS, MODULUS + 1, u32::MAX] {
                let mut bad = bytes.clone();
                bad[prefix + 4 * coordinate..prefix + 4 * coordinate + 4]
                    .copy_from_slice(&word.to_le_bytes());
                assert!(b.decode_native_value(&value.physical_type(), &bad).is_err());
            }
        }
    }
    let result = call("oracle.commit", vec![vector(&words), Value::Index(1)]);
    let opening = call("oracle.open", vec![result[1].clone(), Value::Index(0)]);
    for (value, tag) in [(&result[0], 79), (&opening[1], 80)] {
        let bytes = b.encode_native_value(value).unwrap();
        assert_eq!(bytes[5], tag);
        for domain in [Domain::Base, Domain::Extension] {
            let ty =
                PhysicalType::default_for(LogicalType::new(value.ty(), domain.identity()).unwrap())
                    .unwrap();
            assert!(b.decode_native_value(&ty, &bytes).is_err());
        }
        let mut bad = bytes.clone();
        bad[5] = if tag == 79 { 35 } else { 36 };
        assert!(b.decode_native_value(&value.physical_type(), &bad).is_err());
    }
    assert!(
        b.decode_native_value(
            &opening[1].physical_type(),
            &[b"ZKCV\x00\x50".as_slice(), &25u32.to_le_bytes(), &[0; 800]].concat()
        )
        .is_err()
    );
}
#[test]
fn exact_identities_and_independent_installation_signatures_agree() {
    let b = backend(Policy::default());
    let scheme = Identity::parse(SCHEME).unwrap();
    let suite = Identity::parse(SUITE).unwrap();
    assert_eq!(scheme, Identity::MerkleKoalaBearExt4);
    assert_eq!(suite, Identity::HashChainKeccak256KoalaBearExt4);
    assert_eq!(scheme.scalar_field(), Some(Identity::KoalaBearExt4));
    assert_eq!(suite.scalar_field(), Some(Identity::KoalaBearExt4));
    assert!(scheme.is_row_commitment());
    assert!(!scheme.has_multi_opening());
    assert!(suite.has_index_transcript());
    let service = ServiceContract::parse("random.koala-bear.ext4-binomial3/0").unwrap();
    assert_eq!(service.field(), Identity::KoalaBearExt4);
    assert!(service.signature("index").is_some());
    for (identity, names) in [
        (FIELD, vec!["random.draw", "random.vector", "random.index"]),
        (SUITE, vec!["transcript.challenge", "transcript.index"]),
        (SCHEME, vec!["oracle.commit", "oracle.open", "oracle.check"]),
    ] {
        for name in names {
            let valid = binding(name, identity);
            assert_eq!(
                b.binding_signature(&valid),
                Some(valid.signature().unwrap())
            );
            for provider in ["arkworks", "dalek", "spongefish"] {
                let mut bad = valid.clone();
                bad.implementation = format!("{provider}/{name}");
                assert!(b.binding_signature(&bad).is_none());
                assert!(bad.signature().is_err());
            }
        }
    }
    for bad in [
        "rows.merkle-keccak256.koala-bear.ext4-binomial3/1",
        "rows.merkle-keccak256.koala-bear.ext4-binomial11/0",
        "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection64le/0",
        "hash-chain.sha256.koala-bear.ext4-binomial3.rejection31le/0",
        "merlin3.koala-bear.ext4-binomial3.rejection31le/0",
    ] {
        assert!(Identity::parse(bad).is_err(), "{bad}");
    }
    for name in ["oracle.open_many", "pcs.open"] {
        let bad = binding(name, SCHEME);
        assert!(b.binding_signature(&bad).is_none());
        assert!(bad.signature().is_err());
    }
}
#[test]
fn quartic_tree_preflight_uses_sixteen_byte_elements_and_private_custody() {
    let shape = zkc_kernels::plonky3::oracle::Shape::new(2, 3, 6).unwrap();
    let bytes = shape.retained_bytes::<KoalaBearExt4>().unwrap();
    let values = vector(&coordinates(6));
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(bytes + zkc_cpu::VALUE_SLOT_BYTES - 1);
    let (out, _) = one(
        controlled,
        binding("oracle.commit", SCHEME),
        &[],
        vec![values.clone(), Value::Index(2)],
    );
    assert!(out.unwrap_err().contains("output-bytes"));
    let policy = Policy {
        max_table_elements: 5,
        ..Policy::default()
    };
    assert_eq!(
        backend(policy).validate_value(&values).unwrap_err().code,
        "exhausted:element-limit"
    );
    let result = call(
        "oracle.commit",
        vec![vector(&coordinates(6)), Value::Index(2)],
    );
    let Value::OracleState(state) = &result[1] else {
        panic!()
    };
    assert_eq!(state.retained_bytes().unwrap(), bytes);
    let opening = call("oracle.open", vec![result[1].clone(), Value::Index(0)]);
    let (out, _) = one(
        backend(policy),
        binding("oracle.check", SCHEME),
        &[],
        vec![
            result[0].clone(),
            Value::Index(2),
            Value::Index(3),
            Value::Index(0),
            opening[0].clone(),
            opening[1].clone(),
        ],
    );
    assert_eq!(out.unwrap_err(), "exhausted:oracle-element-limit");
    assert!(
        backend(Policy::default())
            .encode_native_value(&result[1])
            .is_err()
    );
}
#[test]
fn quartic_rng_draw_vector_index_and_budget_preserve_capability_transitions() {
    let domain = || zkc_cpu::Domain::new("P", "session", "main", None);
    let mut b = backend(Policy::default());
    let token = b
        .issue_rng_for(Identity::KoalaBearExt4, domain(), 5)
        .unwrap();
    let Value::Rng(handle) = &token else { panic!() };
    let handle = handle.clone();
    let (out, next) = one(b, binding("random.draw", FIELD), &[], vec![token]);
    b = next;
    let mut out = out.unwrap();
    assert!(matches!(out[0], Value::KoalaBearExt4Field(_)));
    let (draws, next) = one(
        b,
        binding("random.vector", FIELD),
        &["2"],
        vec![out.remove(1)],
    );
    b = next;
    let mut draws = draws.unwrap();
    let Value::KoalaBearExt4Vector(v) = &draws[0] else {
        panic!()
    };
    assert_eq!(v.len(), 2);
    let (index, next) = one(
        b,
        binding("random.index", FIELD),
        &[],
        vec![draws.remove(1), Value::Index(1)],
    );
    b = next;
    let mut index = index.unwrap();
    assert!(matches!(index[0], Value::Index(0)));
    let (last, next) = one(
        b,
        binding("random.index", FIELD),
        &[],
        vec![index.remove(1), Value::Index(1 << 63)],
    );
    b = next;
    let mut last = last.unwrap();
    assert!(matches!(last[0],Value::Index(n) if n < 1<<63));
    assert_eq!(b.observe(&handle).unwrap().draw_count, 5);
    let (out, b) = one(b, binding("random.draw", FIELD), &[], vec![last.remove(1)]);
    assert!(out.unwrap_err().contains("exhausted"));
    assert_eq!(b.observe(&handle).unwrap().generation, 5);
    assert_eq!(b.active_frames(), 0);
}
