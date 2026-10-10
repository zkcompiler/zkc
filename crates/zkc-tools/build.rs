//! Deterministic, offline source-profile tables from the pinned Unicode 17 UCD.
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fmt::Write, fs, path::PathBuf};

type Ranges = Vec<(u32, u32)>;
const INPUTS: &[(&str, &str)] = &[
    (
        "DerivedCoreProperties.txt",
        "24c7fed1195c482faaefd5c1e7eb821c5ee1fb6de07ecdbaa64b56a99da22c08",
    ),
    (
        "PropList.txt",
        "130dcddcaadaf071008bdfce1e7743e04fdfbc910886f017d9f9ac931d8c64dd",
    ),
    (
        "UnicodeData.txt",
        "2e1efc1dcb59c575eedf5ccae60f95229f706ee6d031835247d843c11d96470c",
    ),
    (
        "BidiBrackets.txt",
        "dadbaf38a0d0246e5b805bf8725cb81b7c621f93d030595635f5ba2c2f179428",
    ),
    (
        "NormalizationTest.txt",
        "5019ffd530751a741900c849c0e010332f142a3612234639bd200b82138a87db",
    ),
];
fn point(text: &str) -> u32 {
    assert!((4..=6).contains(&text.len()) && text.bytes().all(|b| b.is_ascii_hexdigit()));
    let value = u32::from_str_radix(text, 16).expect("UCD code point");
    assert!(value <= 0x10ffff, "UCD code point outside Unicode");
    value
}
fn range(text: &str) -> (u32, u32) {
    let (lo, hi) = text.split_once("..").unwrap_or((text, text));
    let result = (point(lo), point(hi));
    assert!(result.0 <= result.1, "reversed UCD range");
    result
}
fn checked(mut ranges: Ranges) -> Ranges {
    ranges.sort_unstable();
    assert!(
        ranges.windows(2).all(|r| r[0].1 < r[1].0),
        "overlapping UCD ranges"
    );
    let mut merged: Ranges = Vec::new();
    for (lo, hi) in ranges {
        if let Some(last) = merged.last_mut()
            && last.1 + 1 == lo
        {
            last.1 = hi;
        } else {
            merged.push((lo, hi));
        }
    }
    merged
}
fn properties(input: &str) -> BTreeMap<String, Ranges> {
    let mut result: BTreeMap<String, Ranges> = BTreeMap::new();
    for row in input.lines() {
        let row = row.split('#').next().unwrap().trim();
        if row.is_empty() {
            continue;
        }
        let columns: Vec<_> = row.split(';').map(str::trim).collect();
        assert!((2..=3).contains(&columns.len()), "malformed UCD property");
        assert!(
            columns[1..].iter().all(|property| !property.is_empty()
                && property
                    .bytes()
                    .all(|b| b.is_ascii_alphabetic() || b == b'_')),
            "malformed UCD property name"
        );
        // Three-column enumerated properties have independent range sets.
        let property = columns[1..].join(";");
        result.entry(property).or_default().push(range(columns[0]));
    }
    result
        .into_iter()
        .map(|(key, value)| (key, checked(value)))
        .collect()
}
fn categories(input: &str) -> BTreeMap<String, Ranges> {
    let mut result: BTreeMap<String, Ranges> = BTreeMap::new();
    let mut first = None;
    let mut previous = None;
    for row in input.lines() {
        let columns: Vec<_> = row.split(';').collect();
        assert_eq!(columns.len(), 15, "malformed UnicodeData record");
        let cp = point(columns[0]);
        assert!(previous.is_none_or(|p| p < cp), "unordered UnicodeData");
        previous = Some(cp);
        let name = columns[1];
        let category = columns[2];
        assert!(category.len() == 2 && category.bytes().all(|b| b.is_ascii_alphabetic()));
        if let Some((lo, stem, expected)) = first.take() {
            assert_eq!(
                name.strip_suffix(", Last>"),
                Some(stem),
                "unpaired UCD range"
            );
            assert_eq!(category, expected);
            result
                .entry(category.to_owned())
                .or_default()
                .push((lo, cp));
        } else if let Some(stem) = name.strip_suffix(", First>") {
            first = Some((cp, stem, category));
        } else {
            assert!(!name.ends_with(", Last>"), "unpaired UCD range");
            result
                .entry(category.to_owned())
                .or_default()
                .push((cp, cp));
        }
    }
    assert!(first.is_none(), "unclosed UCD range");
    result
        .into_iter()
        .map(|(key, value)| (key, checked(value)))
        .collect()
}
fn brackets(input: &str) -> Vec<(u32, u32)> {
    let mut rows = BTreeMap::new();
    for row in input.lines() {
        let row = row.split('#').next().unwrap().trim();
        if row.is_empty() {
            continue;
        }
        let columns: Vec<_> = row.split(';').map(str::trim).collect();
        assert_eq!(columns.len(), 3, "malformed bracket record");
        assert!(matches!(columns[2], "o" | "c"));
        assert!(
            rows.insert(point(columns[0]), (point(columns[1]), columns[2]))
                .is_none()
        );
    }
    for (&cp, &(partner, kind)) in &rows {
        assert_eq!(
            rows.get(&partner),
            Some(&(cp, if kind == "o" { "c" } else { "o" }))
        );
    }
    rows.into_iter()
        .filter_map(|(cp, (partner, kind))| (kind == "o").then_some((cp, partner)))
        .collect()
}
fn emit(output: &mut String, name: &str, ranges: &[(u32, u32)]) {
    writeln!(output, "pub(super) const {name}: &[(u32, u32)] = &[").unwrap();
    for (lo, hi) in ranges {
        writeln!(output, "    (0x{lo:x}, 0x{hi:x}),").unwrap();
    }
    output.push_str("];\n");
}
fn main() {
    let root = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap())
        .join("../../common/unicode/17.0.0");
    let manifest_path = root.parent().unwrap().join("manifest.json");
    println!("cargo:rerun-if-changed={}", manifest_path.display());
    let manifest_bytes = fs::read(&manifest_path).expect("source profile manifest");
    let manifest: serde_json::Value =
        serde_json::from_slice(&manifest_bytes).expect("source profile JSON");
    check_manifest(&manifest);
    let identity = format!("zkc.source-names/0:{:x}", Sha256::digest(&manifest_bytes));
    let mut files = BTreeMap::new();
    for &(file, hash) in INPUTS {
        let path = root.join(file);
        println!("cargo:rerun-if-changed={}", path.display());
        let bytes = fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        assert_eq!(
            format!("{:x}", Sha256::digest(&bytes)),
            hash,
            "UCD hash mismatch: {file}"
        );
        files.insert(file, String::from_utf8(bytes).expect("UTF-8 UCD input"));
    }
    let core = properties(&files["DerivedCoreProperties.txt"]);
    let props = properties(&files["PropList.txt"]);
    let cats = categories(&files["UnicodeData.txt"]);
    let excluded = |cp| {
        contains(&core["Default_Ignorable_Code_Point"], cp) || contains(&props["Bidi_Control"], cp)
    };
    let start = filtered(|cp| !excluded(cp) && (cp == 0x5f || contains(&core["XID_Start"], cp)));
    let continuation = filtered(|cp| {
        !excluded(cp) && ((0x2080..=0x2089).contains(&cp) || contains(&core["XID_Continue"], cp))
    });
    let forbidden = |cp| cp < 128 || excluded(cp) || contains(&continuation, cp);
    let symbols = filtered(|cp| contains(&cats["Sm"], cp) && !forbidden(cp));
    let pairs: Vec<_> = brackets(&files["BidiBrackets.txt"])
        .into_iter()
        .filter(|&(lo, hi)| {
            contains(&cats["Ps"], lo)
                && contains(&cats["Pe"], hi)
                && !forbidden(lo)
                && !forbidden(hi)
        })
        .collect();
    let mut output = String::from("// Generated from pinned Unicode 17.0.0 inputs; do not edit.\n");
    writeln!(output, "pub(super) const IDENTITY: &str = {identity:?};").unwrap();
    for (name, ranges) in [
        ("IDENTIFIER_START", &start),
        ("IDENTIFIER_CONTINUE", &continuation),
        ("MATH_SYMBOL", &symbols),
    ] {
        emit(&mut output, name, ranges);
    }
    emit(&mut output, "BRACKETS", &pairs);
    let out = PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    fs::write(out.join("source_unicode.rs"), output).unwrap();
    // A build artifact for independent C++/Rust decoded-range comparisons.
    let profile = serde_json::json!({"identity":identity, "identifier_start":start,
        "identifier_continue":continuation, "mathematical_symbols":symbols, "delimiter_pairs":pairs});
    fs::write(
        out.join("source_profile.json"),
        serde_json::to_vec_pretty(&profile).unwrap(),
    )
    .unwrap();
}

fn contains(ranges: &[(u32, u32)], cp: u32) -> bool {
    let i = ranges.partition_point(|&(_, hi)| hi < cp);
    ranges.get(i).is_some_and(|&(lo, _)| lo <= cp)
}
fn filtered(predicate: impl Fn(u32) -> bool) -> Ranges {
    let mut ranges: Ranges = Vec::new();
    for cp in (0..=0x10ffff).filter(|&cp| predicate(cp)) {
        assert!(!(0xd800..=0xdfff).contains(&cp));
        if let Some(last) = ranges.last_mut()
            && last.1 + 1 == cp
        {
            last.1 = cp;
        } else {
            ranges.push((cp, cp));
        }
    }
    ranges
}
fn check_manifest(manifest: &serde_json::Value) {
    use serde_json::json;
    for (key, expected) in [
        ("schema", json!("zkc.source-name-profile/0")),
        ("profile", json!("zkc.source-names/0")),
        ("unicode_version", json!("17.0.0")),
        ("normalization", json!("NFC")),
        ("identifier_start_additions", json!(["005F"])),
        ("identifier_continue_additions", json!(["2080..2089"])),
        (
            "identifier_exclusions",
            json!(["Default_Ignorable_Code_Point", "Bidi_Control"]),
        ),
        ("operator_category", json!("Sm")),
        ("operator_reserved", json!(["2211", "220F"])),
        ("delimiter_categories", json!(["Ps", "Pe"])),
        ("normalization_test_rows", json!(20034)),
    ] {
        assert_eq!(manifest[key], expected, "unsupported source profile: {key}");
    }
    assert_eq!(
        manifest["normalizers"]["rust"]["name"],
        "unicode-normalization"
    );
    assert_eq!(manifest["normalizers"]["rust"]["version"], "0.1.25");
    let files = manifest["files"].as_array().expect("UCD file manifest");
    assert_eq!(files.len(), INPUTS.len());
    for &(file, hash) in INPUTS {
        let matches: Vec<_> = files.iter().filter(|row| row["file"] == file).collect();
        assert_eq!(
            matches.len(),
            1,
            "missing or duplicate Unicode input: {file}"
        );
        assert_eq!(matches[0]["sha256"], hash);
        assert_eq!(
            matches[0]["url"],
            format!("https://www.unicode.org/Public/17.0.0/ucd/{file}")
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rejects_malformed_and_overlapping_tables() {
        for input in [
            "1234..1233; X",
            "110000; X",
            "1234; X\n1234; X",
            "1234..1250; X\n1240; X",
            "1234",
            "1234; X; a; b",
            "1234;",
            "1234; Bad123",
        ] {
            assert!(
                std::panic::catch_unwind(|| properties(input)).is_err(),
                "{input}"
            );
        }
        for input in [
            "1234; 1235; o",
            "1234; 1235; o\n1235; 1234; o",
            "1234; 1235; x",
        ] {
            assert!(
                std::panic::catch_unwind(|| brackets(input)).is_err(),
                "{input}"
            );
        }
        assert_eq!(properties("1235; X\n1234; X")["X"], [(0x1234, 0x1235)]);
    }
    #[test]
    fn unicode_data_ranges_require_exact_pairs() {
        let row = |point, name| format!("{point};{name};Lo;0;L;;;;;N;;;;;\n");
        let valid = row("3400", "<CJK, First>") + &row("4DBF", "<CJK, Last>");
        assert_eq!(categories(&valid)["Lo"], [(0x3400, 0x4dbf)]);
        for bad in [
            row("3400", "<CJK, First>"),
            row("4DBF", "<CJK, Last>"),
            valid.replace("CJK, Last", "Other, Last"),
            valid.replace("4DBF", "3300"),
        ] {
            assert!(std::panic::catch_unwind(|| categories(&bad)).is_err());
        }
    }
    #[test]
    fn source_profile_manifest_rejects_changed_contract_and_input_pins() {
        let manifest: serde_json::Value =
            serde_json::from_str(include_str!("../../common/unicode/manifest.json")).unwrap();
        check_manifest(&manifest);
        for (path, replacement) in [
            ("/unicode_version", serde_json::json!("18.0.0")),
            ("/normalization", serde_json::json!("NFKC")),
            ("/identifier_continue_additions", serde_json::json!([])),
            ("/normalizers/rust/version", serde_json::json!("0.1.24")),
            ("/files/0/sha256", serde_json::json!("0".repeat(64))),
            (
                "/files/0/url",
                serde_json::json!("https://example.invalid/UCD"),
            ),
            ("/files/0/file", serde_json::json!("../UnicodeData.txt")),
        ] {
            let mut changed = manifest.clone();
            *changed.pointer_mut(path).unwrap() = replacement;
            assert!(
                std::panic::catch_unwind(|| check_manifest(&changed)).is_err(),
                "{path}"
            );
        }
        let mut changed = manifest;
        changed["files"][0] = changed["files"][1].clone();
        assert!(std::panic::catch_unwind(|| check_manifest(&changed)).is_err());
    }
}
