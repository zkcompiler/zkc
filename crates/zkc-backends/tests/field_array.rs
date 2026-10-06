//! Shape-bound native field arrays and explicit legacy-codec refusal.
mod common;
use common::ark_backend;
use zkc_backends::{
    FieldArray, NativeBackend, NativeWireError, Policy, Scalar, Value, native_wire_size,
};
use zkc_runtime::interactive::{
    DecodeReason, Identity, LogicalType, PhysicalType, Value as RuntimeValue,
};

fn array(length: usize) -> Value {
    Value::FieldArray(
        FieldArray::new(
            LogicalType::field_array(Identity::Bls12381Fr, length as u64).unwrap(),
            (1..=length)
                .map(|x| Scalar::from(x as u64))
                .collect::<Vec<_>>()
                .into(),
        )
        .unwrap(),
    )
}

#[test]
fn exact_frame_and_shape_cannot_cross_codec_profiles() {
    let backend = ark_backend(None);
    let value = array(2);
    let ty = value.physical_type();
    assert_eq!(native_wire_size(&ty), Some(70));
    assert!(!ty.logical().kind().is_serializable());
    assert!(backend.encode_value(&value).is_err());
    let bytes = backend.encode_native_value(&value).unwrap();
    let mut expected = b"ZKCV\x01\x40".to_vec();
    for x in [1u8, 2] {
        let mut scalar = [0u8; 32];
        scalar[0] = x;
        expected.extend(scalar);
    }
    assert_eq!(bytes, expected);
    let decoded = backend.decode_native_value(&ty, &bytes).unwrap();
    assert_eq!(decoded.physical_type(), ty);
    assert_eq!(backend.encode_native_value(&decoded).unwrap(), bytes);
    assert!(backend.decode_typed_value(ty.clone(), &bytes).is_err());
    for end in 0..bytes.len() {
        assert_eq!(
            backend.decode_native_value(&ty, &bytes[..end]).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Length)
        );
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert_eq!(
        backend.decode_native_value(&ty, &extra).unwrap_err(),
        NativeWireError::Invalid(DecodeReason::Length)
    );
    for index in 0..6 {
        let mut wrong = bytes.clone();
        wrong[index] ^= 1;
        assert_eq!(
            backend.decode_native_value(&ty, &wrong).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Header)
        );
    }
    for length in [1, 3] {
        let wrong = PhysicalType::default_for(
            LogicalType::field_array(Identity::Bls12381Fr, length).unwrap(),
        )
        .unwrap();
        assert_eq!(
            backend.decode_native_value(&wrong, &bytes).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Length)
        );
    }
    for index in [0, 1] {
        let mut noncanonical = bytes.clone();
        let modulus = zkc_test_support::unhex(
            "01000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73",
        );
        noncanonical[6 + 32 * index..6 + 32 * (index + 1)].copy_from_slice(&modulus);
        assert_eq!(
            backend.decode_native_value(&ty, &noncanonical).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Scalar)
        );
    }
}

#[test]
fn construction_and_policy_are_checked_before_decode_allocation() {
    let empty = array(0);
    let backend = ark_backend(None);
    let bytes = backend.encode_native_value(&empty).unwrap();
    assert_eq!(bytes.len(), 6);
    let ty = PhysicalType::default_for(LogicalType::field_array(Identity::Bls12381Fr, 0).unwrap())
        .unwrap();
    assert!(backend.decode_native_value(&ty, &bytes).is_ok());
    assert!(backend.decode_native_value(&ty, &bytes[..5]).is_err());
    assert!(LogicalType::field_array(Identity::Bls12381Fr, 1_048_577).is_err());
    assert!(
        FieldArray::new(
            LogicalType::field_array(Identity::Bls12381Fr, 2).unwrap(),
            [Scalar::from(1)].into()
        )
        .is_err()
    );
    assert!(
        PhysicalType::default_for(LogicalType::field_array(Identity::KoalaBear, 2).unwrap())
            .is_err()
    );
    let value = array(2);
    let bytes = ark_backend(None).encode_native_value(&value).unwrap();
    for policy in [
        Policy {
            max_wire_bytes: 69,
            ..Policy::default()
        },
        Policy {
            max_value_bytes: 1407,
            ..Policy::default()
        },
        Policy {
            max_table_elements: 1,
            ..Policy::default()
        },
    ] {
        let backend = NativeBackend::new(policy, common::entry(None), None).unwrap();
        assert_eq!(
            backend
                .decode_native_value(&value.physical_type(), &bytes)
                .unwrap_err(),
            NativeWireError::Limit
        );
    }
}

#[test]
fn decoder_charges_the_temporary_and_retained_array_at_the_peak() {
    let value = array(2);
    let bytes = ark_backend(None).encode_native_value(&value).unwrap();
    let backend = NativeBackend::new(
        Policy {
            max_value_bytes: 1408,
            ..Policy::default()
        },
        common::entry(None),
        None,
    )
    .unwrap();
    assert!(
        backend
            .decode_native_value(&value.physical_type(), &bytes)
            .is_ok()
    );
}

#[test]
fn native_encoding_enforces_the_array_element_limit() {
    let value = array(2);
    let backend = NativeBackend::new(
        Policy {
            max_table_elements: 1,
            ..Policy::default()
        },
        common::entry(None),
        None,
    )
    .unwrap();
    assert_eq!(
        backend.encode_native_value(&value).unwrap_err(),
        NativeWireError::Limit
    );
}

#[test]
fn scalar_and_singleton_array_frames_are_distinct_at_equal_width() {
    let backend = ark_backend(None);
    let scalar = Value::Field(Scalar::from(1));
    let singleton = array(1);
    let scalar_bytes = backend.encode_native_value(&scalar).unwrap();
    let array_bytes = backend.encode_native_value(&singleton).unwrap();
    assert_eq!(scalar_bytes.len(), array_bytes.len());
    for (ty, bytes) in [
        (scalar.physical_type(), &array_bytes),
        (singleton.physical_type(), &scalar_bytes),
    ] {
        assert_eq!(
            backend.decode_native_value(&ty, bytes).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Header)
        );
    }
}

#[test]
fn encoding_and_decoding_charge_their_own_value_memory() {
    let value = array(2);
    let backend = |max_value_bytes| {
        NativeBackend::new(
            Policy {
                max_value_bytes,
                ..Policy::default()
            },
            common::entry(None),
            None,
        )
        .unwrap()
    };
    // Encoding retains 32*N+1280 bytes; decoding also needs a temporary
    // 32*N-byte vector. Identical policies need not admit both operations.
    assert_eq!(
        backend(1343).encode_native_value(&value).unwrap_err(),
        NativeWireError::Limit
    );
    let bytes = backend(1344).encode_native_value(&value).unwrap();
    assert_eq!(
        backend(1344)
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        NativeWireError::Limit
    );
    assert!(
        backend(1408)
            .decode_native_value(&value.physical_type(), &bytes)
            .is_ok()
    );
}
