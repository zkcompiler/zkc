use super::*;
use unicode_normalization::UnicodeNormalization;

#[test]
fn identifiers_keep_exact_unicode17_spelling() {
    for name in [
        "_",
        "alpha",
        "α",
        "β₂",
        "é",
        "한글",
        "𐐀",
        "𝛂",
        "a\u{315}",
        "a\u{316}\u{315}",
        "\u{1c89}",
        "\u{11f02}",
    ] {
        assert!(is_source_identifier(name), "{name:?}");
    }
    for name in [
        "",
        "₂a",
        "1a",
        "a-b",
        "e\u{301}",
        "a\u{315}\u{316}",
        "α\u{200d}",
        "a\u{fe0f}",
        "a\u{202e}",
        "a\u{2066}",
        "a\u{034f}",
        "a\u{00ad}",
        "a\u{e0100}",
        "\u{0378}",
        "\u{0558}", // Added in Unicode 18; must remain outside this profile.
        "\u{d8000}",
    ] {
        assert!(!is_source_identifier(name), "{name:?}");
    }
    assert_ne!(
        encode_nominal_identity("β₂"),
        encode_nominal_identity("beta_2")
    );
    assert_ne!(encode_nominal_identity("a"), encode_nominal_identity("а"));
}
#[test]
fn scalar_decoder_checks_exact_utf8_boundaries() {
    let source = "m::𐐀::α".as_bytes();
    assert_eq!(
        decode_source_scalar(source, 3),
        Some(SourceScalar {
            value: 0x10400,
            bytes: 4
        })
    );
    for offset in [4, 5, 6, source.len(), usize::MAX] {
        assert_eq!(decode_source_scalar(source, offset), None);
    }
    for bad in [
        &[0xc0, 0x80][..],
        &[0xed, 0xa0, 0x80],
        &[0xf4, 0x90, 0x80, 0x80],
        &[0xf0, 0x90],
        &[0x80],
    ] {
        assert_eq!(decode_source_scalar(bad, 0), None);
    }
}
#[test]
fn symbols_and_delimiters_use_the_pinned_categories() {
    assert!(is_mathematical_symbol('⊙' as u32));
    assert!(is_mathematical_symbol('∑' as u32)); // declaration reservation belongs to syntax
    for value in ['+', 'ᵀ', 'α', '\u{2329}', '\u{2066}'] {
        assert!(!is_mathematical_symbol(value as u32), "{value}");
    }
    assert_eq!(matching_source_delimiter('⟪' as u32), Some('⟫' as u32));
    assert!(is_source_delimiter_closer('⟫' as u32));
    for value in ['(', '[', '{', '<', '⟫', '\u{2329}'] {
        assert_eq!(matching_source_delimiter(value as u32), None);
    }
    assert!(!is_source_delimiter_closer(')' as u32));
}
#[test]
fn encodings_are_canonical_reversible_and_byte_bounded() {
    assert_eq!(native_role_name(0), "role00000000");
    assert_eq!(native_setup_name(0xabcdef), "setup00abcdef");
    assert_eq!(native_alternative_name(u32::MAX), "caseffffffff");
    assert_eq!(
        encode_source_symbol("m::α", 11).as_deref(),
        Some("s1h6d2hceb1")
    );
    assert!(encode_source_symbol("m::α", 10).is_none());
    assert!(encode_source_symbol("m::α", 9).is_none());
    for bad in ["", "::α", "m::", "m:::α", "m::e\u{301}", "m::a b"] {
        assert!(encode_source_symbol(bad, u64::MAX).is_none());
    }
    assert_eq!(decode_nominal_identity("", 0).as_deref(), Some(""));
    let key = "数学::Enum<α,β₂>";
    let encoded = encode_nominal_identity(key);
    assert_eq!(
        decode_nominal_identity(&encoded, key.len() as u64).as_deref(),
        Some(key)
    );
    assert!(decode_nominal_identity(&encoded, key.len() as u64 - 1).is_none());
    for bad in [
        "0", "CEB1", "gg", "ff", "eda080", "c080", "f4908080", "61 62",
    ] {
        assert!(decode_nominal_identity(bad, u64::MAX).is_none(), "{bad}");
    }
    let long = "α".repeat(64);
    let symbol = encode_source_symbol(&long, 261).unwrap();
    assert_eq!(symbol.len(), 261);
    assert!(encode_source_symbol(&long, 260).is_none());
}
#[test]
fn complete_unicode17_normalization_corpus() {
    assert_eq!(unicode_normalization::UNICODE_VERSION, (17, 0, 0));
    let corpus = include_str!("../../../../support/unicode/17.0.0/NormalizationTest.txt");
    let mut count = 0;
    for row in corpus.lines() {
        let row = row.split('#').next().unwrap().trim();
        if row.is_empty() || row.starts_with('@') {
            continue;
        }
        let columns: Vec<String> = row
            .split(';')
            .take(5)
            .map(|part| {
                part.split_whitespace()
                    .map(|hex| char::from_u32(u32::from_str_radix(hex, 16).unwrap()).unwrap())
                    .collect()
            })
            .collect();
        assert_eq!(columns.len(), 5);
        for (input, expected) in [
            (&columns[0], &columns[1]),
            (&columns[1], &columns[1]),
            (&columns[2], &columns[1]),
            (&columns[3], &columns[3]),
            (&columns[4], &columns[3]),
        ] {
            assert_eq!(&input.nfc().collect::<String>(), expected, "{row}");
            assert_eq!(is_source_nfc(input), input == expected, "{row}");
        }
        count += 1;
    }
    assert_eq!(count, 20_034);
}
