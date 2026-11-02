//! Deterministic, offline source-profile tables from the pinned Unicode 17 UCD,
//! and the typed tables of the shared EVM target declaration.
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
    let identity = format!("zkc.source-names/0:{}", hex_digest(&manifest_bytes));
    let mut files = BTreeMap::new();
    for &(file, hash) in INPUTS {
        let path = root.join(file);
        println!("cargo:rerun-if-changed={}", path.display());
        let bytes = fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        assert_eq!(hex_digest(&bytes), hash, "UCD hash mismatch: {file}");
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
    // Only the `evm` feature reads the EVM target declaration.
    if std::env::var_os("CARGO_FEATURE_EVM").is_some() {
        evm_target(&out);
    }
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

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

// The EVM target declaration, `zkc.evm-target/0`. The compiler's generator,
// `common/targets/generate.py`, checks the same rules independently; the shared
// refusal cases in `common/targets/evm-validation-cases.json` hold both to them.
const EVM_TARGET_FORMAT: &str = "zkc.evm-target/0";
// The emitted verifier copies memory with MCOPY.
const EVM_REQUIRED_RULE: &str = "EIP-5656";
type Json = serde_json::Value;

fn evm_target(out: &std::path::Path) {
    let path = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap())
        .join("../../common/targets/evm.json");
    println!("cargo:rerun-if-changed={}", path.display());
    let bytes = fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let declaration =
        check_evm_target(&bytes).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    fs::write(
        out.join("evm_target.rs"),
        render_evm_target(&declaration, &evm_target_identity(&bytes)),
    )
    .unwrap();
}

/// The declaration identity: its format and the SHA-256 of its exact bytes.
fn evm_target_identity(bytes: &[u8]) -> String {
    format!("{EVM_TARGET_FORMAT}:{}", hex_digest(bytes))
}

/// A broken rule, named as in the shared refusal cases.
fn refusal(rule: &str, detail: impl std::fmt::Display) -> String {
    format!("evm-target {rule}: {detail}")
}

/// Loads and validates exact declaration bytes.
fn check_evm_target(bytes: &[u8]) -> Result<Json, String> {
    let declaration = load_evm_target(bytes)?;
    validate_evm_target(&declaration)?;
    Ok(declaration)
}

/// Parses ASCII JSON with no repeated object key and only integer numbers.
fn load_evm_target(bytes: &[u8]) -> Result<Json, String> {
    if !bytes.is_ascii() {
        return Err(refusal("format", "the declaration is ASCII"));
    }
    let value: Json = serde_json::from_slice(bytes)
        .map_err(|e| refusal("format", format!("malformed JSON: {e}")))?;
    unique_keys(bytes)?;
    integers(&value)?;
    Ok(value)
}

// Runs after a successful parse, so strings and nesting are well formed. Keys
// are compared after JSON unescaping, as the parser compares them.
fn unique_keys(bytes: &[u8]) -> Result<(), String> {
    let mut objects: Vec<Option<std::collections::BTreeSet<String>>> = Vec::new();
    let (mut i, mut key) = (0, false);
    while i < bytes.len() {
        match bytes[i] {
            b'{' => {
                objects.push(Some(Default::default()));
                key = true;
            }
            b'[' => {
                objects.push(None);
                key = false;
            }
            b'}' | b']' => {
                objects.pop();
                key = false;
            }
            b',' => key = matches!(objects.last(), Some(Some(_))),
            b'"' => {
                let start = i;
                i += 1;
                while bytes[i] != b'"' {
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
                if key {
                    let name: String = serde_json::from_slice(&bytes[start..=i])
                        .map_err(|e| refusal("format", e))?;
                    if let Some(Some(keys)) = objects.last_mut()
                        && !keys.insert(name.clone())
                    {
                        return Err(refusal("keys", format!("duplicate key {name}")));
                    }
                    key = false;
                }
            }
            _ => {}
        }
        i += 1;
    }
    Ok(())
}

fn integers(value: &Json) -> Result<(), String> {
    match value {
        Json::Number(n) if !n.is_u64() && !n.is_i64() => {
            Err(refusal("keys", format!("non-integer number {n}")))
        }
        Json::Array(items) => items.iter().try_for_each(integers),
        Json::Object(fields) => fields.values().try_for_each(integers),
        _ => Ok(()),
    }
}

fn exact<'a>(
    value: &'a Json,
    keys: &[&str],
    place: &str,
) -> Result<&'a serde_json::Map<String, Json>, String> {
    let fields = value
        .as_object()
        .ok_or_else(|| refusal("keys", format!("{place} is an object")))?;
    if fields.len() != keys.len() || keys.iter().any(|key| !fields.contains_key(*key)) {
        return Err(refusal(
            "keys",
            format!("{place} has exactly the fields {}", keys.join(", ")),
        ));
    }
    Ok(fields)
}

fn text<'a>(
    value: &'a Json,
    rule: &str,
    place: &str,
    allowed: impl Fn(&str) -> bool,
) -> Result<&'a str, String> {
    value
        .as_str()
        .filter(|text| allowed(text))
        .ok_or_else(|| refusal(rule, format!("{place} has the wrong spelling")))
}

fn natural(value: &Json, rule: &str, place: &str) -> Result<u64, String> {
    value
        .as_u64()
        .filter(|n| *n >= 1)
        .ok_or_else(|| refusal(rule, format!("{place} is an integer from 1 to 2^64-1")))
}

fn nonempty_list<'a>(value: &'a Json, rule: &str, place: &str) -> Result<&'a [Json], String> {
    value
        .as_array()
        .filter(|items| !items.is_empty())
        .map(Vec::as_slice)
        .ok_or_else(|| refusal(rule, format!("{place} is a nonempty list")))
}

fn distinct<'a>(
    values: impl IntoIterator<Item = &'a str>,
    rule: &str,
    place: &str,
) -> Result<(), String> {
    let mut seen = std::collections::BTreeSet::new();
    match values.into_iter().find(|value| !seen.insert(*value)) {
        Some(value) => Err(refusal(rule, format!("duplicate {place} {value}"))),
        None => Ok(()),
    }
}

fn lowercase_word(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|b| b.is_ascii_lowercase())
}
fn abi_type(text: &str) -> bool {
    !text.is_empty()
        && text
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'[' || b == b']')
}
fn identifier(text: &str) -> bool {
    text.bytes()
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && text.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
}
fn signature(text: &str) -> bool {
    let Some((function, parameters)) = text.strip_suffix(')').and_then(|text| text.split_once('('))
    else {
        return false;
    };
    function
        .bytes()
        .next()
        .is_some_and(|b| b.is_ascii_lowercase())
        && identifier(function)
        && (parameters.is_empty() || parameters.split(',').all(abi_type))
}
fn solc_version(text: &str) -> bool {
    let Some((release, commit)) = text.split_once("+commit.") else {
        return false;
    };
    let parts: Vec<_> = release.split('.').collect();
    parts.len() == 3
        && parts
            .iter()
            .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
        && commit.len() == 8
        && commit
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
fn limit_name(text: &str) -> bool {
    text.bytes().next().is_some_and(|b| b.is_ascii_lowercase())
        && text.split('_').all(|part| {
            !part.is_empty()
                && part
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
        })
}
fn rule_name(text: &str) -> bool {
    text.strip_prefix("EIP-").is_some_and(|number| {
        number
            .bytes()
            .next()
            .is_some_and(|b| (b'1'..=b'9').contains(&b))
            && number.bytes().all(|b| b.is_ascii_digit())
    })
}

/// Checks every rule of the declaration format.
fn validate_evm_target(declaration: &Json) -> Result<(), String> {
    exact(
        declaration,
        &[
            "format",
            "abi",
            "solc",
            "default_fork",
            "forks",
            "validation_gas",
            "limits",
            "reverts",
        ],
        "the declaration",
    )?;
    if declaration["format"] != EVM_TARGET_FORMAT {
        return Err(refusal(
            "format",
            format!("format must be {EVM_TARGET_FORMAT}"),
        ));
    }

    let abi = exact(
        &declaration["abi"],
        &["signature", "selector", "json"],
        "abi",
    )?;
    let signature = text(&abi["signature"], "abi", "abi.signature", signature)?;
    let (function, parameters) = signature[..signature.len() - 1].split_once('(').unwrap();
    let selector = text(&abi["selector"], "selector", "abi.selector", |text| {
        text.len() == 8
            && text
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    })?;
    let digest = keccak256(signature.as_bytes());
    if digest[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
        != selector
    {
        return Err(refusal(
            "selector",
            "abi.selector differs from Keccak-256 of abi.signature",
        ));
    }
    let entries = abi["json"]
        .as_array()
        .filter(|entries| entries.len() == 1)
        .ok_or_else(|| refusal("abi", "abi.json declares exactly one function"))?;
    let entry = exact(
        &entries[0],
        &["type", "name", "stateMutability", "inputs", "outputs"],
        "abi.json function",
    )?;
    if entry["type"] != "function" || entry["name"] != function {
        return Err(refusal("abi", "abi.json names the signature's function"));
    }
    if !matches!(
        entry["stateMutability"].as_str(),
        Some("pure" | "view" | "nonpayable" | "payable")
    ) {
        return Err(refusal("abi", "abi.json has a Solidity state mutability"));
    }
    let mut inputs = Vec::new();
    for side in ["inputs", "outputs"] {
        let ports = entry[side]
            .as_array()
            .ok_or_else(|| refusal("abi", format!("abi.json {side} is a list")))?;
        let mut names = Vec::new();
        for port in ports {
            exact(port, &["name", "type"], "abi.json port")?;
            names.push(text(
                &port["name"],
                "abi",
                "abi.json port name",
                identifier,
            )?);
            let port_type = text(&port["type"], "abi", "abi.json port type", abi_type)?;
            if side == "inputs" {
                inputs.push(port_type);
            }
        }
        distinct(names, "abi", "abi.json port name")?;
    }
    if inputs.join(",") != parameters {
        return Err(refusal("abi", "abi.json inputs differ from abi.signature"));
    }

    let solc = exact(&declaration["solc"], &["version", "optimizer"], "solc")?;
    text(&solc["version"], "solc", "solc.version", solc_version)?;
    let optimizer = exact(
        &solc["optimizer"],
        &["enabled", "details"],
        "solc.optimizer",
    )?;
    let details = exact(
        &optimizer["details"],
        &["yul", "yulDetails"],
        "optimizer details",
    )?;
    let steps = exact(
        &details["yulDetails"],
        &["optimizerSteps"],
        "optimizer yulDetails",
    )?;
    if !optimizer["enabled"].is_boolean() || !details["yul"].is_boolean() {
        return Err(refusal("solc", "solc.optimizer switches are Booleans"));
    }
    text(
        &steps["optimizerSteps"],
        "solc",
        "optimizer steps",
        |text| !text.is_empty() && text.bytes().all(|b| b.is_ascii_graphic()),
    )?;

    let forks = nonempty_list(&declaration["forks"], "fork", "forks")?;
    for fork in forks {
        exact(
            fork,
            &[
                "name",
                "solc",
                "hardfork",
                "transaction_gas_cap",
                "runtime_code_bytes",
                "initcode_bytes",
                "rules",
            ],
            "fork",
        )?;
        let name = text(&fork["name"], "fork", "fork name", lowercase_word)?;
        text(&fork["solc"], "fork", "fork solc", lowercase_word)?;
        text(&fork["hardfork"], "fork", "fork hardfork", |text| {
            text.bytes().next().is_some_and(|b| b.is_ascii_uppercase())
                && text.bytes().all(|b| b.is_ascii_alphabetic())
        })?;
        if !fork["transaction_gas_cap"].is_null() {
            natural(
                &fork["transaction_gas_cap"],
                "fork",
                "fork transaction_gas_cap",
            )?;
        }
        natural(
            &fork["runtime_code_bytes"],
            "fork",
            "fork runtime_code_bytes",
        )?;
        natural(&fork["initcode_bytes"], "fork", "fork initcode_bytes")?;
        let rules = nonempty_list(&fork["rules"], "rules", "fork rules")?
            .iter()
            .map(|rule| text(rule, "rules", "fork rule", rule_name))
            .collect::<Result<Vec<_>, _>>()?;
        distinct(rules.iter().copied(), "rules", "rule")?;
        if !rules.contains(&EVM_REQUIRED_RULE) {
            return Err(refusal(
                "rules",
                format!("fork {name} must include {EVM_REQUIRED_RULE}"),
            ));
        }
    }
    for key in ["name", "solc", "hardfork"] {
        distinct(
            forks.iter().map(|fork| fork[key].as_str().unwrap()),
            "fork",
            key,
        )?;
    }
    if !forks
        .iter()
        .any(|fork| fork["name"] == declaration["default_fork"])
    {
        return Err(refusal(
            "default-fork",
            "default_fork must name a declared fork",
        ));
    }
    natural(
        &declaration["validation_gas"],
        "validation-gas",
        "validation_gas",
    )?;

    let limits = nonempty_list(&declaration["limits"], "limit", "limits")?;
    for limit in limits {
        exact(limit, &["name", "minimum", "maximum"], "limit")?;
        let name = text(&limit["name"], "limit", "limit name", limit_name)?;
        let minimum = natural(&limit["minimum"], "limit", "limit minimum")?;
        let maximum = natural(&limit["maximum"], "limit", "limit maximum")?;
        if minimum > maximum {
            return Err(refusal(
                "limit",
                format!("limit {name} has its minimum above its maximum"),
            ));
        }
    }
    distinct(
        limits.iter().map(|limit| limit["name"].as_str().unwrap()),
        "limit",
        "limit name",
    )?;

    let reverts = nonempty_list(&declaration["reverts"], "revert", "reverts")?;
    for revert in reverts {
        exact(revert, &["class", "tag"], "revert class")?;
        text(
            &revert["class"],
            "revert",
            "revert class name",
            lowercase_word,
        )?;
        text(&revert["tag"], "revert", "revert tag", |text| {
            text.len() == 4 && text.bytes().all(|b| b.is_ascii_uppercase())
        })?;
    }
    for key in ["class", "tag"] {
        distinct(
            reverts.iter().map(|revert| revert[key].as_str().unwrap()),
            "revert",
            key,
        )?;
    }
    Ok(())
}

/// Ethereum's Keccak-256: rate 136 bytes, original padding byte 0x01.
fn keccak256(data: &[u8]) -> [u8; 32] {
    const ROUNDS: [u64; 24] = [
        0x0000000000000001,
        0x0000000000008082,
        0x800000000000808A,
        0x8000000080008000,
        0x000000000000808B,
        0x0000000080000001,
        0x8000000080008081,
        0x8000000000008009,
        0x000000000000008A,
        0x0000000000000088,
        0x0000000080008009,
        0x000000008000000A,
        0x000000008000808B,
        0x800000000000008B,
        0x8000000000008089,
        0x8000000000008003,
        0x8000000000008002,
        0x8000000000000080,
        0x000000000000800A,
        0x800000008000000A,
        0x8000000080008081,
        0x8000000000008080,
        0x0000000080000001,
        0x8000000080008008,
    ];
    // Rotation offsets r[x][y] of the rho step.
    const ROTATIONS: [[u32; 5]; 5] = [
        [0, 36, 3, 41, 18],
        [1, 44, 10, 45, 2],
        [62, 6, 43, 15, 61],
        [28, 55, 25, 21, 56],
        [27, 20, 39, 8, 14],
    ];
    const RATE: usize = 136;
    // Lanes are indexed x + 5 * y.
    let permute = |a: &mut [u64; 25]| {
        for round in ROUNDS {
            let c: [u64; 5] =
                std::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
            for (i, lane) in a.iter_mut().enumerate() {
                let x = i % 5;
                *lane ^= c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            }
            let mut b = [0u64; 25];
            for (i, lane) in a.iter().enumerate() {
                let (x, y) = (i % 5, i / 5);
                b[y + 5 * ((2 * x + 3 * y) % 5)] = lane.rotate_left(ROTATIONS[x][y]);
            }
            for (i, lane) in a.iter_mut().enumerate() {
                let (x, y) = (i % 5, i / 5);
                *lane = b[i] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
            a[0] ^= round;
        }
    };
    let mut padded = data.to_vec();
    padded.push(0x01);
    padded.resize(padded.len().div_ceil(RATE) * RATE, 0);
    *padded.last_mut().unwrap() |= 0x80;
    let mut lanes = [0u64; 25];
    for block in padded.chunks(RATE) {
        for (lane, word) in lanes.iter_mut().zip(block.chunks(8)) {
            *lane ^= u64::from_le_bytes(word.try_into().unwrap());
        }
        permute(&mut lanes);
    }
    let mut digest = [0; 32];
    for (bytes, lane) in digest.chunks_mut(8).zip(lanes) {
        bytes.copy_from_slice(&lane.to_le_bytes());
    }
    digest
}

fn capitalized(name: &str) -> String {
    let mut text = name.to_owned();
    text[..1].make_ascii_uppercase();
    text
}

/// Projects a validated declaration as typed Rust constants.
fn render_evm_target(declaration: &Json, identity: &str) -> String {
    let abi = &declaration["abi"];
    let selector = abi["selector"].as_str().unwrap();
    let selector: Vec<_> = (0..4)
        .map(|i| format!("0x{}", &selector[2 * i..2 * i + 2]))
        .collect();
    let forks = declaration["forks"].as_array().unwrap();
    let limits = declaration["limits"].as_array().unwrap();
    let reverts = declaration["reverts"].as_array().unwrap();
    let names: Vec<_> = forks
        .iter()
        .map(|fork| capitalized(fork["name"].as_str().unwrap()))
        .collect();
    let mut o = String::from(
        "// Generated from common/targets/evm.json by crates/zkc/build.rs. Do not edit.\n",
    );
    for (comment, name, value) in [
        (
            "The installed declaration: its format and the SHA-256 of its exact bytes.",
            "IDENTITY",
            identity.to_owned(),
        ),
        (
            "The verifier function's Solidity signature.",
            "ABI_SIGNATURE",
            abi["signature"].as_str().unwrap().to_owned(),
        ),
        (
            "The verifier ABI as JSON.",
            "ABI_JSON",
            abi["json"].to_string(),
        ),
        (
            "The pinned solc release and commit.",
            "SOLC_VERSION",
            declaration["solc"]["version"].as_str().unwrap().to_owned(),
        ),
        (
            "The solc standard-JSON optimizer settings.",
            "SOLC_OPTIMIZER_JSON",
            declaration["solc"]["optimizer"].to_string(),
        ),
    ] {
        writeln!(o, "/// {comment}\npub const {name}: &str = {value:?};").unwrap();
    }
    writeln!(
        o,
        "/// The first four bytes of the signature's Keccak-256.\npub const ABI_SELECTOR: [u8; 4] = [{}];",
        selector.join(", ")
    )
    .unwrap();
    writeln!(
        o,
        "/// A declared deployment fork.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Fork {{
    {},
}}
/// The declared default fork.
pub const DEFAULT_FORK: Fork = Fork::{};
impl Fork {{
    /// Every declared fork, in declaration order.
    pub const ALL: [Fork; {}] = [{}];
    /// This fork's declared row.
    pub fn row(self) -> &'static ForkRow {{
        &FORKS[self as usize]
    }}
    /// The fork with exactly this declared name.
    pub fn from_name(name: &str) -> Option<Self> {{
        Self::ALL.into_iter().find(|fork| fork.row().name == name)
    }}
}}
/// One fork: its solc `evmVersion`, engine hardfork, consensus transaction
/// gas cap, deployment code ceilings and named consensus rules.
#[derive(Debug, PartialEq, Eq)]
pub struct ForkRow {{
    pub name: &'static str,
    pub solc: &'static str,
    pub hardfork: &'static str,
    pub transaction_gas_cap: Option<u64>,
    pub runtime_code_bytes: u64,
    pub initcode_bytes: u64,
    pub rules: &'static [&'static str],
}}
/// The fork rows, indexed by `Fork`.
pub static FORKS: [ForkRow; {}] = [",
        names.join(",\n    "),
        capitalized(declaration["default_fork"].as_str().unwrap()),
        forks.len(),
        names
            .iter()
            .map(|name| format!("Fork::{name}"))
            .collect::<Vec<_>>()
            .join(", "),
        forks.len(),
    )
    .unwrap();
    for fork in forks {
        let cap = fork["transaction_gas_cap"]
            .as_u64()
            .map_or("None".to_owned(), |cap| format!("Some({cap})"));
        let rules: Vec<_> = fork["rules"]
            .as_array()
            .unwrap()
            .iter()
            .map(|rule| format!("{:?}", rule.as_str().unwrap()))
            .collect();
        writeln!(
            o,
            "    ForkRow {{ name: {:?}, solc: {:?}, hardfork: {:?}, transaction_gas_cap: {cap}, \
             runtime_code_bytes: {}, initcode_bytes: {}, rules: &[{}] }},",
            fork["name"].as_str().unwrap(),
            fork["solc"].as_str().unwrap(),
            fork["hardfork"].as_str().unwrap(),
            fork["runtime_code_bytes"],
            fork["initcode_bytes"],
            rules.join(", "),
        )
        .unwrap();
    }
    writeln!(
        o,
        "];
/// One deployment ceiling: a compilation selects a value in its range.
#[derive(Debug, PartialEq, Eq)]
pub struct Limit {{
    pub name: &'static str,
    pub minimum: u64,
    pub maximum: u64,
}}
/// The deployment ceilings, in declaration order.
pub const LIMITS: [Limit; {}] = [",
        limits.len()
    )
    .unwrap();
    for limit in limits {
        writeln!(
            o,
            "    Limit {{ name: {:?}, minimum: {}, maximum: {} }},",
            limit["name"].as_str().unwrap(),
            limit["minimum"],
            limit["maximum"],
        )
        .unwrap();
    }
    writeln!(
        o,
        "];
/// One revert class: the four-byte tag that begins its structured reverts.
#[derive(Debug, PartialEq, Eq)]
pub struct RevertClass {{
    pub name: &'static str,
    pub tag: [u8; 4],
}}
/// The revert classes, in declaration order.
pub const REVERT_CLASSES: [RevertClass; {}] = [",
        reverts.len()
    )
    .unwrap();
    for revert in reverts {
        writeln!(
            o,
            "    RevertClass {{ name: {:?}, tag: *b{:?} }},",
            revert["class"].as_str().unwrap(),
            revert["tag"].as_str().unwrap(),
        )
        .unwrap();
    }
    o.push_str("];\n");
    // Literal forms for static text, such as command help, that `concat!`
    // composes at compile time.
    writeln!(
        o,
        "/// The declared fork names, in declaration order, joined by `|`.
#[macro_export]
macro_rules! evm_target_forks {{
    () => {{
        {:?}
    }};
}}
/// The declared default fork's name.
#[macro_export]
macro_rules! evm_target_default_fork {{
    () => {{
        {:?}
    }};
}}",
        forks
            .iter()
            .map(|fork| fork["name"].as_str().unwrap())
            .collect::<Vec<_>>()
            .join("|"),
        declaration["default_fork"].as_str().unwrap(),
    )
    .unwrap();
    o
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

#[cfg(test)]
mod evm_target_tests {
    use super::*;

    const AUTHORED: &[u8] = include_bytes!("../../common/targets/evm.json");

    fn authored() -> Json {
        check_evm_target(AUTHORED).unwrap()
    }

    // Applies one shared case's edits: `set`, `delete`, `duplicate` and `append`
    // at a path of object keys and list indices.
    fn edited(declaration: &Json, edits: &[Json]) -> Json {
        let mut result = declaration.clone();
        for edit in edits {
            let path = edit["path"].as_array().unwrap();
            let (last, parents) = path.split_last().unwrap();
            let mut parent = &mut result;
            for key in parents {
                parent = match key.as_u64() {
                    Some(index) => &mut parent[index as usize],
                    None => &mut parent[key.as_str().unwrap()],
                };
            }
            match (edit["op"].as_str().unwrap(), last.as_u64()) {
                ("set", Some(index)) => parent[index as usize] = edit["value"].clone(),
                ("set", None) => parent[last.as_str().unwrap()] = edit["value"].clone(),
                ("delete", None) => {
                    parent
                        .as_object_mut()
                        .unwrap()
                        .remove(last.as_str().unwrap())
                        .unwrap();
                }
                ("duplicate", Some(index)) => {
                    let list = parent.as_array_mut().unwrap();
                    list.push(list[index as usize].clone());
                }
                ("append", None) => parent[last.as_str().unwrap()]
                    .as_array_mut()
                    .unwrap()
                    .push(edit["value"].clone()),
                (op, _) => panic!("unknown edit {op}"),
            }
        }
        result
    }

    #[test]
    fn evm_target_declaration_is_accepted_and_named_by_its_bytes() {
        authored();
        assert_eq!(
            evm_target_identity(AUTHORED),
            format!("zkc.evm-target/0:{}", hex_digest(AUTHORED))
        );
        let generated = render_evm_target(&authored(), &evm_target_identity(AUTHORED));
        assert!(generated.contains(&format!(
            "pub const IDENTITY: &str = {:?};",
            evm_target_identity(AUTHORED)
        )));
    }

    #[test]
    fn evm_target_shared_cases_refuse_by_rule() {
        let cases: Json = serde_json::from_str(include_str!(
            "../../common/targets/evm-validation-cases.json"
        ))
        .unwrap();
        assert_eq!(cases["format"], "zkc.evm-target-validation-cases/0");
        let declaration = authored();
        let cases = cases["cases"].as_array().unwrap();
        assert!(!cases.is_empty());
        for case in cases {
            let changed = edited(&declaration, case["edits"].as_array().unwrap());
            let refused = validate_evm_target(&changed).expect_err(case["name"].as_str().unwrap());
            let rule = format!("evm-target {}:", case["rule"].as_str().unwrap());
            assert!(refused.starts_with(&rule), "{}: {refused}", case["name"]);
        }
    }

    #[test]
    fn evm_target_refuses_repeated_keys_fractions_and_non_ascii() {
        let text = std::str::from_utf8(AUTHORED).unwrap();
        for (changed, rule) in [
            (
                r#"{"format":"zkc.evm-target/0","format":"zkc.evm-target/0"}"#.to_owned(),
                "keys",
            ),
            (
                text.replacen(
                    r#""default_fork""#,
                    r#""default_fork":"cancun","default_fork""#,
                    1,
                ),
                "keys",
            ),
            (
                text.replacen(r#""maximum": 10}"#, r#""maximum": 10.0}"#, 1),
                "keys",
            ),
            (text.replacen(r#""cancun""#, "\"canc\u{fc}n\"", 1), "format"),
        ] {
            assert_ne!(changed.as_bytes(), AUTHORED);
            let refused = check_evm_target(changed.as_bytes()).unwrap_err();
            assert!(
                refused.starts_with(&format!("evm-target {rule}:")),
                "{refused}"
            );
        }
    }

    #[test]
    fn evm_target_keccak_matches_standard_vectors() {
        let hex = |digest: [u8; 32]| {
            digest
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        };
        assert_eq!(
            hex(keccak256(b"")),
            "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        );
        assert_eq!(
            &hex(keccak256(b"verify(bytes[],bytes,bytes)"))[..8],
            "a488e1e4"
        );
        // Inputs one byte short of, at and past the 136-byte rate.
        assert_ne!(keccak256(&[0x61; 135]), keccak256(&[0x61; 136]));
        assert_ne!(keccak256(&[0x61; 136]), keccak256(&[0x61; 137]));
    }

    // The SDK's generated module carries exactly the declaration.
    #[cfg(feature = "evm")]
    #[test]
    fn evm_target_generated_module_matches_the_declaration() {
        use zkc::evm_target as generated;
        let declaration = authored();
        assert_eq!(generated::IDENTITY, evm_target_identity(AUTHORED));
        assert_eq!(generated::ABI_SIGNATURE, declaration["abi"]["signature"]);
        let json: Json = serde_json::from_str(generated::ABI_JSON).unwrap();
        assert_eq!(json, declaration["abi"]["json"]);
        let selector: String = generated::ABI_SELECTOR
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(selector, declaration["abi"]["selector"]);
        assert_eq!(generated::SOLC_VERSION, declaration["solc"]["version"]);
        let optimizer: Json = serde_json::from_str(generated::SOLC_OPTIMIZER_JSON).unwrap();
        assert_eq!(optimizer, declaration["solc"]["optimizer"]);
        let forks = declaration["forks"].as_array().unwrap();
        assert_eq!(generated::Fork::ALL.len(), forks.len());
        for (fork, row) in generated::Fork::ALL.into_iter().zip(forks) {
            let fork_row = fork.row();
            assert_eq!(generated::Fork::from_name(fork_row.name), Some(fork));
            assert_eq!(fork_row.name, row["name"]);
            assert_eq!(fork_row.solc, row["solc"]);
            assert_eq!(fork_row.hardfork, row["hardfork"]);
            assert_eq!(
                fork_row.transaction_gas_cap,
                row["transaction_gas_cap"].as_u64()
            );
            assert_eq!(fork_row.runtime_code_bytes, row["runtime_code_bytes"]);
            assert_eq!(fork_row.initcode_bytes, row["initcode_bytes"]);
            assert_eq!(fork_row.rules, row["rules"].as_array().unwrap().as_slice());
        }
        assert_eq!(
            generated::DEFAULT_FORK.row().name,
            declaration["default_fork"]
        );
        let names: Vec<_> = forks
            .iter()
            .map(|row| row["name"].as_str().unwrap())
            .collect();
        assert_eq!(zkc::evm_target_forks!(), names.join("|"));
        assert_eq!(zkc::evm_target_default_fork!(), declaration["default_fork"]);
        let limits: Vec<_> = generated::LIMITS
            .iter()
            .map(|limit| serde_json::json!({"name":limit.name, "minimum":limit.minimum, "maximum":limit.maximum}))
            .collect();
        assert_eq!(Json::from(limits), declaration["limits"]);
        let reverts: Vec<_> = generated::REVERT_CLASSES
            .iter()
            .map(|revert| serde_json::json!({"class":revert.name, "tag":std::str::from_utf8(&revert.tag).unwrap()}))
            .collect();
        assert_eq!(Json::from(reverts), declaration["reverts"]);
    }
}
