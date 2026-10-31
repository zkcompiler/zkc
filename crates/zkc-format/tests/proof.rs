use zkc_format::proof::{
    self, FormatError, HEADER_BYTES, MAX_PROOF_BYTES, ProofFormat, ProofReader,
};

// Independent bytes: two frames, including an empty payload.
fn fixture() -> Vec<u8> {
    let mut bytes = b"ZKCPRF00".to_vec();
    bytes.extend([9; 32]);
    bytes.extend([3, 0, 0, 0, 0, 0, 0, 0, 4, 5, 6]);
    bytes.extend([0; 8]);
    bytes
}

#[test]
fn format_names_and_serde_are_exact_and_never_detected_from_content() {
    for (format, name) in [
        (ProofFormat::Native, "zkc.framed/0"),
        (ProofFormat::RawBytes, "raw.bytes/0"),
    ] {
        assert_eq!(format.name(), name);
        assert_eq!(ProofFormat::parse(name), Some(format));
        assert_eq!(
            serde_json::from_value::<ProofFormat>(serde_json::json!(name)).unwrap(),
            format
        );
    }
    for name in ["zkc.framed/1", "raw.bytes/1", "Native", "zkc.framed/0 "] {
        assert_eq!(ProofFormat::parse(name), None);
        assert!(serde_json::from_value::<ProofFormat>(serde_json::json!(name)).is_err());
    }
    for payload in [&[][..], b"ZKCPRF00payload", &[0xff, 0, 0x80]] {
        let mut reader = ProofReader::new(ProofFormat::RawBytes, payload, &[2; 32]).unwrap();
        assert_eq!(reader.finish(), Err(FormatError::Truncated));
        assert_eq!(reader.message().unwrap(), payload);
        assert_eq!((reader.messages(), reader.bytes_read()), (1, payload.len()));
        assert_eq!(reader.message(), Err(FormatError::Truncated));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn native_fixture_and_every_truncated_prefix_preserve_the_cursor() {
    let bytes = fixture();
    assert_eq!(proof::header(&[9; 32]).as_slice(), &bytes[..40]);
    assert_eq!(proof::message_length(3), [3, 0, 0, 0, 0, 0, 0, 0]);
    for end in 0..bytes.len() {
        if end < 40 {
            assert!(matches!(
                ProofReader::new(ProofFormat::Native, &bytes[..end], &[9; 32]),
                Err(FormatError::Truncated)
            ));
            continue;
        }
        let mut reader = ProofReader::new(ProofFormat::Native, &bytes[..end], &[9; 32]).unwrap();
        if end < 51 {
            assert_eq!(reader.message(), Err(FormatError::Truncated));
            assert_eq!(reader.bytes_read(), if end < 48 { 40 } else { 48 });
            assert_eq!(reader.messages(), 0);
        } else {
            assert_eq!(reader.message().unwrap(), [4, 5, 6]);
            assert_eq!(reader.message(), Err(FormatError::Truncated));
            assert_eq!((reader.messages(), reader.bytes_read()), (1, 51));
        }
    }
    let mut reader = ProofReader::new(ProofFormat::Native, &bytes, &[9; 32]).unwrap();
    assert_eq!(reader.message().unwrap(), [4, 5, 6]);
    assert_eq!(reader.finish(), Err(FormatError::Trailing));
    assert!(reader.message().unwrap().is_empty());
    assert_eq!(reader.finish(), Ok(()));
    assert_eq!((reader.messages(), reader.bytes_read()), (2, bytes.len()));
    assert_eq!(reader.message(), Err(FormatError::Truncated));
    assert_eq!(reader.finish(), Ok(()));
}

#[test]
fn unreached_bad_frames_stay_lazy_and_failed_lengths_remain_consumed() {
    let mut bytes = fixture()[..51].to_vec();
    bytes.extend([0xff; 8]);
    let mut reader = ProofReader::new(ProofFormat::Native, &bytes, &[9; 32]).unwrap();
    assert_eq!(reader.message().unwrap(), [4, 5, 6]);
    assert_eq!(reader.finish(), Err(FormatError::Trailing));
    assert_eq!(reader.message(), Err(FormatError::Limit));
    assert_eq!((reader.messages(), reader.bytes_read()), (1, 59));
    assert_eq!(reader.message(), Err(FormatError::Truncated));

    // A truncated payload consumes its length. A subsequent read starts at the
    // surviving cursor, rather than retrying or rolling back the original frame.
    let mut bytes = b"ZKCPRF00".to_vec();
    bytes.extend([9; 32]);
    bytes.extend([9, 0, 0, 0, 0, 0, 0, 0]);
    bytes.extend([0; 8]);
    let mut reader = ProofReader::new(ProofFormat::Native, &bytes, &[9; 32]).unwrap();
    assert_eq!(reader.message(), Err(FormatError::Truncated));
    assert_eq!((reader.messages(), reader.bytes_read()), (0, 48));
    assert!(reader.message().unwrap().is_empty());
    assert_eq!((reader.messages(), reader.bytes_read()), (1, 56));
    assert_eq!(reader.finish(), Ok(()));
}

#[test]
fn header_and_size_refusals_keep_their_precedence() {
    let bytes = fixture();
    assert!(matches!(
        ProofReader::new(ProofFormat::Native, &bytes, &[8; 32]),
        Err(FormatError::Header)
    ));
    let short_bad_header = [0; 39];
    assert!(matches!(
        ProofReader::new(ProofFormat::Native, &short_bad_header, &[9; 32]),
        Err(FormatError::Truncated)
    ));
    let oversized_bad_header = vec![0; MAX_PROOF_BYTES + 1];
    for format in [ProofFormat::Native, ProofFormat::RawBytes] {
        assert!(matches!(
            ProofReader::new(format, &oversized_bad_header, &[9; 32]),
            Err(FormatError::Limit)
        ));
        assert_eq!(proof::validate_limit(format, MAX_PROOF_BYTES), Ok(()));
        assert_eq!(
            proof::validate_limit(format, MAX_PROOF_BYTES + 1),
            Err(FormatError::Limit)
        );
    }
    assert_eq!(proof::validate_limit(ProofFormat::RawBytes, 0), Ok(()));
    assert_eq!(
        proof::validate_limit(ProofFormat::Native, HEADER_BYTES),
        Ok(())
    );
    assert_eq!(
        proof::validate_limit(ProofFormat::Native, HEADER_BYTES - 1),
        Err(FormatError::Limit)
    );
    // A duplicate raw message refuses before any length or capacity check.
    assert_eq!(
        proof::message_preflight(ProofFormat::RawBytes, 0, 1, usize::MAX, 0),
        Err(FormatError::Trailing)
    );
    assert_eq!(
        proof::message_preflight(ProofFormat::Native, 40, 0, usize::MAX, MAX_PROOF_BYTES),
        Err(FormatError::Limit)
    );
    assert_eq!(
        proof::message_preflight(ProofFormat::Native, 40, 0, 1, 49),
        Ok(9)
    );
    assert_eq!(
        proof::message_preflight(ProofFormat::Native, 49, 1, 0, 49),
        Err(FormatError::Limit)
    );
}
