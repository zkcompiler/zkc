//! Standalone, dependency-free Rust checker for the temporary F1-R package.
//!
//! This file intentionally shares no parser, canonical encoder, or hashing
//! implementation with either the untrusted exporter or the Python checker.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::process::ExitCode;

const FORMAT: &str = "zkc.formal-source-package.f1r.v0";
const CONTRACT_SCHEMA: &str = "zkc.formal-source-contract.f1r.v0";
const CONTRACT_DOMAIN: &str = "zkc/f1r/contract/v0";
const AUTH_DOMAIN: &str = "zkc/f1r/auth-node/v0";
const PACKAGE_DOMAIN: &str = "zkc/f1r/package/v0";
const MANIFEST_DOMAIN: &str = "zkc/f1r/manifest/v0";
const PROPOSITION_DOMAIN: &str = "zkc/f1r/proposition/v0";
const RESULT_DOMAIN: &str = "zkc/f1r/result/v0";
const MAX_WIRE_BYTES: usize = 1 << 20;
const MAX_DEPTH: usize = 64;
const MAX_AUTH_NODES: u64 = 128;
const MAX_READS: u64 = 512;
const EXPECTED_EXCLUSIONS: [&str; 4] = [
    "CausalCapability",
    "ConfidentialValue",
    "MutablePlanState",
    "SecretWitnessValue",
];

#[derive(Clone, Debug, Eq, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    Number(u64),
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

#[derive(Clone, Copy, Debug)]
enum ParseKind {
    DuplicateKey,
    DepthLimit,
    Other,
}

#[derive(Debug)]
struct ParseError {
    kind: ParseKind,
    detail: String,
}

struct Parser<'a> {
    input: &'a [u8],
    offset: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self { input, offset: 0 }
    }

    fn parse(mut self) -> Result<Json, ParseError> {
        self.skip_space();
        let value = self.value(0)?;
        self.skip_space();
        if self.offset != self.input.len() {
            return Err(self.error(ParseKind::Other, "trailing JSON octets"));
        }
        Ok(value)
    }

    fn value(&mut self, depth: usize) -> Result<Json, ParseError> {
        if depth > MAX_DEPTH {
            return Err(self.error(ParseKind::DepthLimit, "JSON nesting exceeds depth 64"));
        }
        self.skip_space();
        match self.peek() {
            Some(b'n') => {
                self.literal(b"null")?;
                Ok(Json::Null)
            }
            Some(b't') => {
                self.literal(b"true")?;
                Ok(Json::Bool(true))
            }
            Some(b'f') => {
                self.literal(b"false")?;
                Ok(Json::Bool(false))
            }
            Some(b'"') => self.string().map(Json::String),
            Some(b'[') => self.array(depth + 1),
            Some(b'{') => self.object(depth + 1),
            Some(b'0'..=b'9') => self.number().map(Json::Number),
            Some(_) => Err(self.error(ParseKind::Other, "unsupported JSON token")),
            None => Err(self.error(ParseKind::Other, "unexpected end of JSON")),
        }
    }

    fn array(&mut self, depth: usize) -> Result<Json, ParseError> {
        self.expect(b'[')?;
        self.skip_space();
        let mut values = Vec::new();
        if self.peek() == Some(b']') {
            self.offset += 1;
            return Ok(Json::Array(values));
        }
        loop {
            values.push(self.value(depth)?);
            self.skip_space();
            match self.peek() {
                Some(b',') => {
                    self.offset += 1;
                    self.skip_space();
                }
                Some(b']') => {
                    self.offset += 1;
                    return Ok(Json::Array(values));
                }
                _ => return Err(self.error(ParseKind::Other, "array needs ',' or ']'")),
            }
        }
    }

    fn object(&mut self, depth: usize) -> Result<Json, ParseError> {
        self.expect(b'{')?;
        self.skip_space();
        let mut values = BTreeMap::new();
        if self.peek() == Some(b'}') {
            self.offset += 1;
            return Ok(Json::Object(values));
        }
        loop {
            if self.peek() != Some(b'"') {
                return Err(self.error(ParseKind::Other, "object key is not a string"));
            }
            let key = self.string()?;
            self.skip_space();
            self.expect(b':')?;
            let value = self.value(depth)?;
            if values.insert(key.clone(), value).is_some() {
                return Err(self.error(
                    ParseKind::DuplicateKey,
                    &format!("duplicate object key {key}"),
                ));
            }
            self.skip_space();
            match self.peek() {
                Some(b',') => {
                    self.offset += 1;
                    self.skip_space();
                }
                Some(b'}') => {
                    self.offset += 1;
                    return Ok(Json::Object(values));
                }
                _ => return Err(self.error(ParseKind::Other, "object needs ',' or '}'")),
            }
        }
    }

    fn string(&mut self) -> Result<String, ParseError> {
        self.expect(b'"')?;
        let mut output = Vec::new();
        loop {
            let byte = self
                .take()
                .ok_or_else(|| self.error(ParseKind::Other, "unterminated string"))?;
            match byte {
                b'"' => break,
                b'\\' => {
                    let escaped = self.take().ok_or_else(|| {
                        self.error(ParseKind::Other, "unterminated string escape")
                    })?;
                    match escaped {
                        b'"' | b'\\' | b'/' => output.push(escaped),
                        b'u' => {
                            let value = self.hex4()?;
                            if !(0x20..=0x7e).contains(&value) {
                                return Err(self.error(
                                    ParseKind::Other,
                                    "decoded string is not printable ASCII",
                                ));
                            }
                            output.push(value as u8);
                        }
                        _ => {
                            return Err(self.error(
                                ParseKind::Other,
                                "decoded string contains a control or invalid escape",
                            ));
                        }
                    }
                }
                0x20..=0x21 | 0x23..=0x5b | 0x5d..=0x7e => output.push(byte),
                _ => {
                    return Err(
                        self.error(ParseKind::Other, "decoded string is not printable ASCII")
                    );
                }
            }
        }
        if output.is_empty() {
            return Err(self.error(ParseKind::Other, "decoded string is empty"));
        }
        String::from_utf8(output)
            .map_err(|_| self.error(ParseKind::Other, "decoded string is not ASCII"))
    }

    fn hex4(&mut self) -> Result<u16, ParseError> {
        let mut value = 0u16;
        for _ in 0..4 {
            let byte = self
                .take()
                .ok_or_else(|| self.error(ParseKind::Other, "short Unicode escape"))?;
            let digit = match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                b'A'..=b'F' => byte - b'A' + 10,
                _ => return Err(self.error(ParseKind::Other, "invalid Unicode escape")),
            };
            value = (value << 4) | u16::from(digit);
        }
        Ok(value)
    }

    fn number(&mut self) -> Result<u64, ParseError> {
        let start = self.offset;
        if self.peek() == Some(b'0') {
            self.offset += 1;
            if matches!(self.peek(), Some(b'0'..=b'9')) {
                return Err(self.error(ParseKind::Other, "number has a leading zero"));
            }
        } else {
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.offset += 1;
            }
        }
        let text = std::str::from_utf8(&self.input[start..self.offset])
            .map_err(|_| self.error(ParseKind::Other, "number is not ASCII"))?;
        text.parse::<u64>()
            .map_err(|_| self.error(ParseKind::Other, "number exceeds u64"))
    }

    fn literal(&mut self, expected: &[u8]) -> Result<(), ParseError> {
        if self.input.get(self.offset..self.offset + expected.len()) == Some(expected) {
            self.offset += expected.len();
            Ok(())
        } else {
            Err(self.error(ParseKind::Other, "invalid JSON literal"))
        }
    }

    fn expect(&mut self, expected: u8) -> Result<(), ParseError> {
        if self.take() == Some(expected) {
            Ok(())
        } else {
            Err(self.error(ParseKind::Other, "unexpected JSON punctuation"))
        }
    }

    fn skip_space(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\n' | b'\r' | b'\t')) {
            self.offset += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.offset).copied()
    }

    fn take(&mut self) -> Option<u8> {
        let value = self.peek()?;
        self.offset += 1;
        Some(value)
    }

    fn error(&self, kind: ParseKind, detail: &str) -> ParseError {
        ParseError {
            kind,
            detail: format!("{detail} at byte {}", self.offset),
        }
    }
}

#[derive(Debug)]
struct Finding {
    class: &'static str,
    code: &'static str,
    detail: String,
}

type Checked<T> = Result<T, Finding>;

fn finding(class: &'static str, code: &'static str, detail: impl Into<String>) -> Finding {
    Finding {
        class,
        code,
        detail: detail.into(),
    }
}

fn object<'a>(value: &'a Json, label: &str) -> Checked<&'a BTreeMap<String, Json>> {
    match value {
        Json::Object(result) => Ok(result),
        _ => Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            format!("{label} is not an object"),
        )),
    }
}

fn array<'a>(value: &'a Json, label: &str) -> Checked<&'a Vec<Json>> {
    match value {
        Json::Array(result) => Ok(result),
        _ => Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            format!("{label} is not an array"),
        )),
    }
}

fn text<'a>(value: &'a Json, label: &str) -> Checked<&'a str> {
    match value {
        Json::String(result) => Ok(result),
        _ => Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            format!("{label} is not text"),
        )),
    }
}

fn natural(value: &Json, label: &str) -> Checked<u64> {
    match value {
        Json::Number(result) => Ok(*result),
        _ => Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            format!("{label} is not a u64"),
        )),
    }
}

fn exact_object<'a>(
    value: &'a Json,
    fields: &[&str],
    label: &str,
) -> Checked<&'a BTreeMap<String, Json>> {
    let result = object(value, label)?;
    let expected: BTreeSet<&str> = fields.iter().copied().collect();
    let actual: BTreeSet<&str> = result.keys().map(String::as_str).collect();
    if actual != expected {
        return Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            format!("{label} fields differ"),
        ));
    }
    Ok(result)
}

fn field<'a>(object: &'a BTreeMap<String, Json>, key: &str) -> &'a Json {
    object.get(key).expect("exact-object field exists")
}

fn sorted_unique_strings(value: &Json, label: &str) -> Checked<Vec<String>> {
    let result: Vec<String> = array(value, label)?
        .iter()
        .map(|item| text(item, label).map(str::to_owned))
        .collect::<Checked<_>>()?;
    let sorted: Vec<String> = result
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    if result != sorted {
        return Err(finding(
            "Malformed",
            "F1R-M-NONCANONICAL-SEQUENCE",
            format!("{label} is not sorted-unique"),
        ));
    }
    Ok(result)
}

fn rows_by_coordinate<'a>(
    value: &'a Json,
    fields: &[&str],
    label: &str,
) -> Checked<(
    Vec<&'a BTreeMap<String, Json>>,
    BTreeMap<String, &'a BTreeMap<String, Json>>,
)> {
    let mut rows = Vec::new();
    let mut coordinates = Vec::new();
    for (ordinal, item) in array(value, label)?.iter().enumerate() {
        let row = exact_object(item, fields, &format!("{label} row {ordinal}"))?;
        let coordinate = text(field(row, "coordinate"), &format!("{label} coordinate"))?;
        rows.push(row);
        coordinates.push(coordinate.to_owned());
    }
    let sorted: Vec<String> = coordinates
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    if coordinates != sorted {
        return Err(finding(
            "Malformed",
            "F1R-M-NONCANONICAL-SEQUENCE",
            format!("{label} is not coordinate-sorted-unique"),
        ));
    }
    let index = coordinates.into_iter().zip(rows.iter().copied()).collect();
    Ok((rows, index))
}

fn valid_digest(value: &Json, label: &str) -> Checked<String> {
    let value = text(value, label)?;
    let suffix = value.strip_prefix("sha256:").ok_or_else(|| {
        finding(
            "Malformed",
            "F1R-M-DIGEST",
            format!("{label} has no SHA-256 prefix"),
        )
    })?;
    if suffix.len() != 64
        || !suffix
            .as_bytes()
            .iter()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
    {
        return Err(finding(
            "Malformed",
            "F1R-M-DIGEST",
            format!("{label} is not a lowercase SHA-256 ID"),
        ));
    }
    Ok(value.to_owned())
}

fn quote_ascii(value: &str, output: &mut Vec<u8>) {
    output.push(b'"');
    for byte in value.as_bytes() {
        if matches!(byte, b'"' | b'\\') {
            output.push(b'\\');
        }
        output.push(*byte);
    }
    output.push(b'"');
}

fn encode_canonical(value: &Json, output: &mut Vec<u8>) {
    match value {
        Json::Null => output.extend_from_slice(b"null"),
        Json::Bool(true) => output.extend_from_slice(b"true"),
        Json::Bool(false) => output.extend_from_slice(b"false"),
        Json::Number(number) => output.extend_from_slice(number.to_string().as_bytes()),
        Json::String(string) => quote_ascii(string, output),
        Json::Array(values) => {
            output.push(b'[');
            for (index, item) in values.iter().enumerate() {
                if index != 0 {
                    output.push(b',');
                }
                encode_canonical(item, output);
            }
            output.push(b']');
        }
        Json::Object(values) => {
            output.push(b'{');
            for (index, (key, item)) in values.iter().enumerate() {
                if index != 0 {
                    output.push(b',');
                }
                quote_ascii(key, output);
                output.push(b':');
                encode_canonical(item, output);
            }
            output.push(b'}');
        }
    }
}

fn canonical(value: &Json) -> Vec<u8> {
    let mut output = Vec::new();
    encode_canonical(value, &mut output);
    output
}

fn sha256(input: &[u8]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut state = [
        0x6a09e667u32,
        0xbb67ae85,
        0x3c6ef372,
        0xa54ff53a,
        0x510e527f,
        0x9b05688c,
        0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = (input.len() as u64) * 8;
    let mut padded = input.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    for block in padded.chunks_exact(64) {
        let mut words = [0u32; 64];
        for index in 0..16 {
            words[index] = u32::from_be_bytes([
                block[index * 4],
                block[index * 4 + 1],
                block[index * 4 + 2],
                block[index * 4 + 3],
            ]);
        }
        for index in 16..64 {
            let s0 = words[index - 15].rotate_right(7)
                ^ words[index - 15].rotate_right(18)
                ^ (words[index - 15] >> 3);
            let s1 = words[index - 2].rotate_right(17)
                ^ words[index - 2].rotate_right(19)
                ^ (words[index - 2] >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }
        let mut a = state[0];
        let mut b = state[1];
        let mut c = state[2];
        let mut d = state[3];
        let mut e = state[4];
        let mut f = state[5];
        let mut g = state[6];
        let mut h = state[7];
        for index in 0..64 {
            let upper = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choose = (e & f) ^ ((!e) & g);
            let temp1 = h
                .wrapping_add(upper)
                .wrapping_add(choose)
                .wrapping_add(K[index])
                .wrapping_add(words[index]);
            let lower = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = lower.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    }
    let mut output = [0u8; 32];
    for (index, word) in state.iter().enumerate() {
        output[index * 4..index * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    output
}

fn value_id(domain: &str, value: &Json) -> String {
    let mut preimage = domain.as_bytes().to_vec();
    preimage.push(0);
    preimage.extend_from_slice(&canonical(value));
    let digest = sha256(&preimage);
    let mut result = String::from("sha256:");
    for byte in digest {
        result.push_str(&format!("{byte:02x}"));
    }
    result
}

fn string(value: impl Into<String>) -> Json {
    Json::String(value.into())
}

fn array_of_strings(values: &[String]) -> Json {
    Json::Array(values.iter().cloned().map(Json::String).collect())
}

fn json_object(fields: impl IntoIterator<Item = (String, Json)>) -> Json {
    Json::Object(fields.into_iter().collect())
}

fn validate_shape(package_value: &Json) -> Checked<()> {
    let package = exact_object(
        package_value,
        &[
            "asserted_package_id",
            "authentication",
            "contract",
            "format",
            "ledger",
            "manifest",
            "projection",
            "semantic_profile",
        ],
        "package",
    )?;
    if text(field(package, "format"), "package format")? != FORMAT {
        return Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            "unsupported package format",
        ));
    }
    text(
        field(package, "semantic_profile"),
        "package semantic profile",
    )?;
    valid_digest(field(package, "asserted_package_id"), "asserted package ID")?;

    let contract = exact_object(
        field(package, "contract"),
        &["asserted_id", "body"],
        "contract",
    )?;
    valid_digest(field(contract, "asserted_id"), "contract asserted ID")?;
    let body = exact_object(
        field(contract, "body"),
        &[
            "contract_schema",
            "excluded_support_kinds",
            "finite_controls",
            "package_schema",
            "protected_observations",
            "read_catalog",
            "read_roots",
            "root_requirements",
            "semantic_profile",
        ],
        "contract body",
    )?;
    if text(field(body, "contract_schema"), "contract schema")? != CONTRACT_SCHEMA
        || text(field(body, "package_schema"), "contract package schema")? != FORMAT
    {
        return Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            "unsupported contract schema",
        ));
    }
    text(field(body, "semantic_profile"), "contract semantic profile")?;
    let exclusions = sorted_unique_strings(
        field(body, "excluded_support_kinds"),
        "excluded support kinds",
    )?;
    if exclusions
        != EXPECTED_EXCLUSIONS
            .iter()
            .map(|item| (*item).to_owned())
            .collect::<Vec<_>>()
    {
        return Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            "wrong excluded-support catalog",
        ));
    }
    let observations = object(
        field(body, "protected_observations"),
        "protected observations",
    )?;
    if observations.is_empty() {
        return Err(finding(
            "Malformed",
            "F1R-M-SCHEMA",
            "protected observations are empty",
        ));
    }
    for (observation, reads) in observations {
        if sorted_unique_strings(reads, &format!("protected observation {observation}"))?.is_empty()
        {
            return Err(finding(
                "Malformed",
                "F1R-M-SCHEMA",
                format!("protected observation {observation} covers no reads"),
            ));
        }
    }
    sorted_unique_strings(field(body, "read_roots"), "read roots")?;

    let controls = exact_object(
        field(body, "finite_controls"),
        &["max_auth_nodes", "max_depth", "max_reads", "max_wire_bytes"],
        "finite controls",
    )?;
    let expected_controls = [
        ("max_auth_nodes", MAX_AUTH_NODES),
        ("max_depth", MAX_DEPTH as u64),
        ("max_reads", MAX_READS),
        ("max_wire_bytes", MAX_WIRE_BYTES as u64),
    ];
    for (key, expected) in expected_controls {
        if natural(field(controls, key), key)? != expected {
            return Err(finding(
                "Malformed",
                "F1R-M-SCHEMA",
                format!("finite control {key} differs"),
            ));
        }
    }

    let (requirements, _) = rows_by_coordinate(
        field(body, "root_requirements"),
        &["coordinate", "kind", "profile"],
        "root requirements",
    )?;
    for row in requirements {
        text(field(row, "kind"), "root requirement kind")?;
        text(field(row, "profile"), "root requirement profile")?;
    }
    let (read_rows, _) = rows_by_coordinate(
        field(body, "read_catalog"),
        &[
            "coordinate",
            "requires",
            "source_node",
            "source_pointer",
            "value_kind",
        ],
        "read catalog",
    )?;
    if read_rows.len() as u64 > MAX_READS {
        return Err(finding(
            "DeterministicLimitExceeded",
            "F1R-L-READS",
            "read catalog exceeds its bound",
        ));
    }
    for row in read_rows {
        text(field(row, "source_node"), "read source node")?;
        text(field(row, "source_pointer"), "read source pointer")?;
        text(field(row, "value_kind"), "read value kind")?;
        sorted_unique_strings(field(row, "requires"), "read requirements")?;
    }

    let authentication = exact_object(
        field(package, "authentication"),
        &["nodes", "roots"],
        "authentication",
    )?;
    sorted_unique_strings(field(authentication, "roots"), "authentication roots")?;
    let (node_rows, _) = rows_by_coordinate(
        field(authentication, "nodes"),
        &[
            "asserted_id",
            "body",
            "coordinate",
            "dependencies",
            "kind",
            "profile",
        ],
        "authentication nodes",
    )?;
    if node_rows.len() as u64 > MAX_AUTH_NODES {
        return Err(finding(
            "DeterministicLimitExceeded",
            "F1R-L-AUTH-NODES",
            "authentication nodes exceed their bound",
        ));
    }
    for row in node_rows {
        valid_digest(field(row, "asserted_id"), "authentication asserted ID")?;
        text(field(row, "kind"), "authentication kind")?;
        text(field(row, "profile"), "authentication profile")?;
        sorted_unique_strings(field(row, "dependencies"), "authentication dependencies")?;
        let node_body = object(field(row, "body"), "authentication body")?;
        let imports = node_body.get("imports").ok_or_else(|| {
            finding(
                "Malformed",
                "F1R-M-SCHEMA",
                "authentication body has no imports",
            )
        })?;
        sorted_unique_strings(imports, "authentication imports")?;
    }

    sorted_unique_strings(field(package, "manifest"), "package manifest")?;
    let (projection_rows, _) = rows_by_coordinate(
        field(package, "projection"),
        &[
            "coordinate",
            "source_node",
            "source_pointer",
            "value",
            "value_kind",
        ],
        "projection",
    )?;
    let (ledger_rows, _) = rows_by_coordinate(
        field(package, "ledger"),
        &["coordinate", "source_node", "source_pointer"],
        "ledger",
    )?;
    if projection_rows.len() as u64 > MAX_READS || ledger_rows.len() as u64 > MAX_READS {
        return Err(finding(
            "DeterministicLimitExceeded",
            "F1R-L-READS",
            "realized reads exceed their bound",
        ));
    }
    for row in projection_rows {
        text(field(row, "source_node"), "projection source node")?;
        text(field(row, "source_pointer"), "projection source pointer")?;
        text(field(row, "value_kind"), "projection value kind")?;
    }
    for row in ledger_rows {
        text(field(row, "source_node"), "ledger source node")?;
        text(field(row, "source_pointer"), "ledger source pointer")?;
    }
    Ok(())
}

fn package_without_id(package: &BTreeMap<String, Json>) -> Json {
    Json::Object(
        package
            .iter()
            .filter(|(key, _)| key.as_str() != "asserted_package_id")
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect(),
    )
}

fn authenticate_nodes(
    package: &BTreeMap<String, Json>,
    contract_body: &BTreeMap<String, Json>,
) -> Checked<Vec<Json>> {
    let authentication = object(field(package, "authentication"), "authentication")?;
    let roots = sorted_unique_strings(field(authentication, "roots"), "authentication roots")?;
    let (_, node_refs) = rows_by_coordinate(
        field(authentication, "nodes"),
        &[
            "asserted_id",
            "body",
            "coordinate",
            "dependencies",
            "kind",
            "profile",
        ],
        "authentication nodes",
    )?;
    let nodes: BTreeMap<String, Json> = node_refs
        .into_iter()
        .map(|(coordinate, row)| (coordinate, Json::Object(row.clone())))
        .collect();
    let mut memo = BTreeMap::<String, String>::new();
    let mut active = BTreeSet::<String>::new();

    fn compute(
        coordinate: &str,
        nodes: &BTreeMap<String, Json>,
        memo: &mut BTreeMap<String, String>,
        active: &mut BTreeSet<String>,
    ) -> Checked<String> {
        if let Some(result) = memo.get(coordinate) {
            return Ok(result.clone());
        }
        if !active.insert(coordinate.to_owned()) {
            return Err(finding(
                "Malformed",
                "F1R-M-AUTH-CYCLE",
                "authentication graph is cyclic",
            ));
        }
        let current = nodes.get(coordinate).ok_or_else(|| {
            finding(
                "Negative",
                "F1R-N-MISSING-AUTH-NODE",
                format!("missing authentication node {coordinate}"),
            )
        })?;
        let row = object(current, "authentication node")?;
        let dependencies =
            sorted_unique_strings(field(row, "dependencies"), "authentication dependencies")?;
        let imports = sorted_unique_strings(
            field(
                object(field(row, "body"), "authentication body")?,
                "imports",
            ),
            "authentication imports",
        )?;
        if imports != dependencies {
            return Err(finding(
                "Negative",
                "F1R-N-AUTH-DEPENDENCY",
                format!("authentication dependencies disagree at {coordinate}"),
            ));
        }
        let mut dependency_rows = Vec::new();
        for dependency in dependencies {
            let dependency_id = compute(&dependency, nodes, memo, active)?;
            dependency_rows.push(json_object([
                ("coordinate".to_owned(), string(dependency)),
                ("id".to_owned(), string(dependency_id)),
            ]));
        }
        let preimage = json_object([
            ("body".to_owned(), field(row, "body").clone()),
            ("coordinate".to_owned(), string(coordinate)),
            ("dependencies".to_owned(), Json::Array(dependency_rows)),
            ("kind".to_owned(), field(row, "kind").clone()),
            ("profile".to_owned(), field(row, "profile").clone()),
        ]);
        let computed = value_id(AUTH_DOMAIN, &preimage);
        if text(field(row, "asserted_id"), "asserted auth ID")? != computed {
            return Err(finding(
                "Negative",
                "F1R-N-AUTH-ID",
                format!("authentication ID mismatch at {coordinate}"),
            ));
        }
        active.remove(coordinate);
        memo.insert(coordinate.to_owned(), computed.clone());
        Ok(computed)
    }

    for root in &roots {
        compute(root, &nodes, &mut memo, &mut active)?;
    }
    if memo.len() != nodes.len() {
        return Err(finding(
            "Negative",
            "F1R-N-EXTRA-AUTH-NODE",
            "authentication closure contains an unreachable node",
        ));
    }

    let (_, requirement_refs) = rows_by_coordinate(
        field(contract_body, "root_requirements"),
        &["coordinate", "kind", "profile"],
        "root requirements",
    )?;
    let requirement_keys: Vec<String> = requirement_refs.keys().cloned().collect();
    if roots != requirement_keys {
        return Err(finding(
            "Negative",
            "F1R-N-ROOT-SET",
            "authentication roots differ from contract roots",
        ));
    }
    let mut root_ids = Vec::new();
    for root in roots {
        let node = object(nodes.get(&root).expect("root node exists"), "root node")?;
        let requirement = requirement_refs
            .get(&root)
            .expect("root requirement exists");
        if field(node, "kind") != field(requirement, "kind")
            || field(node, "profile") != field(requirement, "profile")
        {
            return Err(finding(
                "KindMismatch",
                "F1R-K-ROOT",
                format!("root kind/profile mismatch at {root}"),
            ));
        }
        root_ids.push(json_object([
            ("coordinate".to_owned(), string(root.clone())),
            (
                "id".to_owned(),
                string(memo.get(&root).expect("computed root ID").clone()),
            ),
        ]));
    }
    Ok(root_ids)
}

fn required_reads(contract_body: &BTreeMap<String, Json>) -> Checked<Vec<String>> {
    let (_, catalog_refs) = rows_by_coordinate(
        field(contract_body, "read_catalog"),
        &[
            "coordinate",
            "requires",
            "source_node",
            "source_pointer",
            "value_kind",
        ],
        "read catalog",
    )?;
    let catalog: BTreeMap<String, Json> = catalog_refs
        .into_iter()
        .map(|(coordinate, row)| (coordinate, Json::Object(row.clone())))
        .collect();
    let roots = sorted_unique_strings(field(contract_body, "read_roots"), "read roots")?;
    let mut seen = BTreeSet::<String>::new();
    let mut active = BTreeSet::<String>::new();

    fn visit(
        coordinate: &str,
        catalog: &BTreeMap<String, Json>,
        seen: &mut BTreeSet<String>,
        active: &mut BTreeSet<String>,
    ) -> Checked<()> {
        if seen.contains(coordinate) {
            return Ok(());
        }
        if !active.insert(coordinate.to_owned()) {
            return Err(finding(
                "Malformed",
                "F1R-M-READ-CYCLE",
                "read graph is cyclic",
            ));
        }
        let row = object(
            catalog.get(coordinate).ok_or_else(|| {
                finding(
                    "Malformed",
                    "F1R-M-SCHEMA",
                    format!("unknown read coordinate {coordinate}"),
                )
            })?,
            "read row",
        )?;
        for dependency in sorted_unique_strings(field(row, "requires"), "read requirements")? {
            visit(&dependency, catalog, seen, active)?;
        }
        active.remove(coordinate);
        seen.insert(coordinate.to_owned());
        Ok(())
    }

    for root in roots {
        visit(&root, &catalog, &mut seen, &mut active)?;
    }
    let catalog_coordinates: BTreeSet<String> = catalog.keys().cloned().collect();
    if catalog_coordinates != seen {
        return Err(finding(
            "Malformed",
            "F1R-M-READ-CLOSURE",
            "read catalog contains a coordinate outside the required closure",
        ));
    }

    let mut source_bindings = BTreeSet::<(String, String)>::new();
    for (coordinate, row_value) in &catalog {
        let row = object(row_value, "read row")?;
        let binding = (
            text(field(row, "source_node"), "read source node")?.to_owned(),
            text(field(row, "source_pointer"), "read source pointer")?.to_owned(),
        );
        if !source_bindings.insert(binding) {
            return Err(finding(
                "Malformed",
                "F1R-M-ALIASED-SOURCE",
                format!("read catalog aliases a source binding at {coordinate}"),
            ));
        }
    }

    let observations = object(
        field(contract_body, "protected_observations"),
        "protected observations",
    )?;
    let mut covered = BTreeSet::<String>::new();
    for (observation, raw_reads) in observations {
        for read in
            sorted_unique_strings(raw_reads, &format!("protected observation {observation}"))?
        {
            if !seen.contains(&read) {
                return Err(finding(
                    "Malformed",
                    "F1R-M-OBSERVATION-COVERAGE",
                    format!("protected observation {observation} names an unknown read"),
                ));
            }
            covered.insert(read);
        }
    }
    if covered != seen {
        return Err(finding(
            "Malformed",
            "F1R-M-OBSERVATION-COVERAGE",
            "protected observations do not cover the exact read closure",
        ));
    }
    Ok(seen.into_iter().collect())
}

fn decode_pointer_token(token: &str) -> Checked<String> {
    let bytes = token.as_bytes();
    let mut output = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'~' {
            output.push(bytes[index]);
            index += 1;
            continue;
        }
        if index + 1 >= bytes.len() || !matches!(bytes[index + 1], b'0' | b'1') {
            return Err(finding(
                "Malformed",
                "F1R-M-POINTER",
                "invalid JSON Pointer escape",
            ));
        }
        output.push(if bytes[index + 1] == b'0' { b'~' } else { b'/' });
        index += 2;
    }
    String::from_utf8(output).map_err(|_| {
        finding(
            "Malformed",
            "F1R-M-POINTER",
            "JSON Pointer token is not ASCII",
        )
    })
}

fn select_pointer(node_body: &Json, pointer: &str) -> Checked<Json> {
    let parts: Vec<&str> = pointer.split('/').collect();
    if parts.len() < 2 || !parts[0].is_empty() || parts[1] != "body" {
        return Err(finding(
            "Malformed",
            "F1R-M-POINTER",
            "source pointer is not rooted at /body",
        ));
    }
    let mut current = node_body;
    for encoded in parts.iter().skip(2) {
        let token = decode_pointer_token(encoded)?;
        match current {
            Json::Object(values) => {
                current = values.get(&token).ok_or_else(|| {
                    finding(
                        "Negative",
                        "F1R-N-SOURCE-SELECTION",
                        format!("source pointer {pointer} selects no field"),
                    )
                })?;
            }
            Json::Array(values) => {
                if token.is_empty()
                    || !token.as_bytes().iter().all(u8::is_ascii_digit)
                    || (token.len() > 1 && token.starts_with('0'))
                {
                    return Err(finding(
                        "Malformed",
                        "F1R-M-POINTER",
                        "source pointer has a noncanonical array index",
                    ));
                }
                let index = token.parse::<usize>().map_err(|_| {
                    finding(
                        "Malformed",
                        "F1R-M-POINTER",
                        "source pointer array index exceeds usize",
                    )
                })?;
                current = values.get(index).ok_or_else(|| {
                    finding(
                        "Negative",
                        "F1R-N-SOURCE-SELECTION",
                        format!("source pointer {pointer} exceeds its array"),
                    )
                })?;
            }
            _ => {
                return Err(finding(
                    "Negative",
                    "F1R-N-SOURCE-SELECTION",
                    format!("source pointer {pointer} descends through a scalar"),
                ));
            }
        }
    }
    Ok(current.clone())
}

fn compare_reads(
    package: &BTreeMap<String, Json>,
    contract_body: &BTreeMap<String, Json>,
) -> Checked<Vec<String>> {
    let expected = required_reads(contract_body)?;
    let manifest = sorted_unique_strings(field(package, "manifest"), "package manifest")?;
    let expected_set: BTreeSet<String> = expected.iter().cloned().collect();
    let manifest_set: BTreeSet<String> = manifest.iter().cloned().collect();
    if expected_set.difference(&manifest_set).next().is_some() {
        return Err(finding(
            "Negative",
            "F1R-N-MISSING-READ",
            "package omits a required read",
        ));
    }
    if manifest_set.difference(&expected_set).next().is_some() {
        return Err(finding(
            "Negative",
            "F1R-N-EXTRA-READ",
            "package contains an extra read",
        ));
    }

    let (_, projection) = rows_by_coordinate(
        field(package, "projection"),
        &[
            "coordinate",
            "source_node",
            "source_pointer",
            "value",
            "value_kind",
        ],
        "projection",
    )?;
    let (_, ledger) = rows_by_coordinate(
        field(package, "ledger"),
        &["coordinate", "source_node", "source_pointer"],
        "ledger",
    )?;
    for index in [&projection, &ledger] {
        if expected
            .iter()
            .any(|coordinate| !index.contains_key(coordinate))
        {
            return Err(finding(
                "Negative",
                "F1R-N-MISSING-READ",
                "projection or ledger omits a required read",
            ));
        }
        if index
            .keys()
            .any(|coordinate| !expected_set.contains(coordinate))
        {
            return Err(finding(
                "Negative",
                "F1R-N-EXTRA-READ",
                "projection or ledger contains an extra read",
            ));
        }
    }

    let (_, catalog) = rows_by_coordinate(
        field(contract_body, "read_catalog"),
        &[
            "coordinate",
            "requires",
            "source_node",
            "source_pointer",
            "value_kind",
        ],
        "read catalog",
    )?;
    let authentication = object(field(package, "authentication"), "authentication")?;
    let (_, nodes) = rows_by_coordinate(
        field(authentication, "nodes"),
        &[
            "asserted_id",
            "body",
            "coordinate",
            "dependencies",
            "kind",
            "profile",
        ],
        "authentication nodes",
    )?;

    for coordinate in &expected {
        let specification = catalog
            .get(coordinate)
            .expect("required catalog row exists");
        let projected = projection
            .get(coordinate)
            .expect("required projection row exists");
        let recorded = ledger.get(coordinate).expect("required ledger row exists");
        let source_node = field(specification, "source_node");
        let source_pointer = field(specification, "source_pointer");
        if field(projected, "source_node") != source_node
            || field(projected, "source_pointer") != source_pointer
            || field(recorded, "source_node") != source_node
            || field(recorded, "source_pointer") != source_pointer
        {
            return Err(finding(
                "Negative",
                "F1R-N-COORDINATE-BINDING",
                format!("source binding mismatch at {coordinate}"),
            ));
        }
        if field(projected, "value_kind") != field(specification, "value_kind") {
            return Err(finding(
                "KindMismatch",
                "F1R-K-VALUE",
                format!("value kind mismatch at {coordinate}"),
            ));
        }
        let source_coordinate = text(source_node, "read source node")?;
        let source = nodes.get(source_coordinate).ok_or_else(|| {
            finding(
                "Negative",
                "F1R-N-MISSING-AUTH-NODE",
                format!("missing read source {source_coordinate}"),
            )
        })?;
        let selected = select_pointer(
            field(source, "body"),
            text(source_pointer, "read source pointer")?,
        )?;
        if field(projected, "value") != &selected {
            let code = if coordinate == "view.shared-challenge.binding" {
                "F1R-N-SHARED-CHALLENGE"
            } else if coordinate == "view.execution.order" {
                "F1R-N-EXECUTION-ORDER"
            } else {
                "F1R-N-OBSERVATION-VALUE"
            };
            return Err(finding(
                "Negative",
                code,
                format!("projected value mismatch at {coordinate}"),
            ));
        }
    }
    Ok(expected)
}

fn check(package_value: &Json) -> Checked<Json> {
    validate_shape(package_value)?;
    let package = object(package_value, "package")?;
    let contract = object(field(package, "contract"), "contract")?;
    let contract_body = object(field(contract, "body"), "contract body")?;

    let exclusions: BTreeSet<String> = sorted_unique_strings(
        field(contract_body, "excluded_support_kinds"),
        "excluded support kinds",
    )?
    .into_iter()
    .collect();
    for row in array(field(package, "projection"), "projection")? {
        let row = object(row, "projection row")?;
        if exclusions.contains(text(field(row, "value_kind"), "projection value kind")?) {
            return Err(finding(
                "Refused",
                "F1R-R-EXCLUDED-SUPPORT",
                "projection serializes owner-local support",
            ));
        }
    }

    if field(package, "semantic_profile") != field(contract_body, "semantic_profile") {
        return Err(finding(
            "KindMismatch",
            "F1R-K-PROFILE",
            "package and contract profiles differ",
        ));
    }

    let computed_contract_id = value_id(CONTRACT_DOMAIN, field(contract, "body"));
    if text(field(contract, "asserted_id"), "contract asserted ID")? != computed_contract_id {
        return Err(finding(
            "Negative",
            "F1R-N-CONTRACT-ID",
            "contract ID mismatch",
        ));
    }
    let computed_package_id = value_id(PACKAGE_DOMAIN, &package_without_id(package));
    if text(field(package, "asserted_package_id"), "asserted package ID")? != computed_package_id {
        return Err(finding(
            "Negative",
            "F1R-N-PACKAGE-ID",
            "package ID mismatch",
        ));
    }

    let root_ids = authenticate_nodes(package, contract_body)?;
    let reads = compare_reads(package, contract_body)?;
    let manifest_id = value_id(MANIFEST_DOMAIN, &array_of_strings(&reads));
    let semantic_profile = field(package, "semantic_profile").clone();
    let proposition = json_object([
        (
            "contract_id".to_owned(),
            string(computed_contract_id.clone()),
        ),
        ("direction".to_owned(), string("ExactSemanticReadAgreement")),
        ("manifest_id".to_owned(), string(manifest_id.clone())),
        ("package_id".to_owned(), string(computed_package_id.clone())),
        ("root_ids".to_owned(), Json::Array(root_ids.clone())),
        ("semantic_profile".to_owned(), semantic_profile),
    ]);
    let proposition_id = value_id(PROPOSITION_DOMAIN, &proposition);
    let mut agreement = BTreeMap::from([
        ("class".to_owned(), string("Affirmative")),
        ("code".to_owned(), string("F1R-AFFIRMATIVE")),
        ("contract_id".to_owned(), string(computed_contract_id)),
        ("manifest_id".to_owned(), string(manifest_id)),
        ("package_id".to_owned(), string(computed_package_id)),
        ("proposition_id".to_owned(), string(proposition_id)),
        ("required_reads".to_owned(), array_of_strings(&reads)),
        ("root_ids".to_owned(), Json::Array(root_ids)),
    ]);
    let result_id = value_id(RESULT_DOMAIN, &Json::Object(agreement.clone()));
    agreement.insert("result_id".to_owned(), string(result_id));
    Ok(Json::Object(agreement))
}

fn envelope(outcome: Json) -> Json {
    json_object([
        ("checker".to_owned(), string("rust-standalone-v0")),
        ("outcome".to_owned(), outcome),
    ])
}

fn error_outcome(class: &str, code: &str) -> Json {
    json_object([
        ("class".to_owned(), string(class)),
        ("code".to_owned(), string(code)),
    ])
}

fn print_json(value: &Json) {
    println!(
        "{}",
        String::from_utf8(canonical(value)).expect("canonical ASCII")
    );
}

fn run() -> Result<(Json, u8), Finding> {
    let paths: Vec<String> = env::args().skip(1).collect();
    if paths.len() != 1 {
        return Ok((error_outcome("Malformed", "F1R-M-INVOCATION"), 2));
    }
    let wire = fs::read(&paths[0]).map_err(|error| {
        finding(
            "Malformed",
            "F1R-M-IO",
            format!("cannot read package: {error}"),
        )
    })?;
    if wire.len() > MAX_WIRE_BYTES {
        return Ok((error_outcome("DeterministicLimitExceeded", "F1R-L-WIRE"), 2));
    }
    let package = match Parser::new(&wire).parse() {
        Ok(value) => value,
        Err(error) => {
            let (class, code) = match error.kind {
                ParseKind::DuplicateKey => ("Malformed", "F1R-M-DUPLICATE-KEY"),
                ParseKind::DepthLimit => ("DeterministicLimitExceeded", "F1R-L-DEPTH"),
                ParseKind::Other => ("Malformed", "F1R-M-JSON"),
            };
            eprintln!("rust checker: {}", error.detail);
            return Ok((error_outcome(class, code), 2));
        }
    };
    match check(&package) {
        Ok(outcome) => Ok((outcome, 0)),
        Err(error) => {
            eprintln!("rust checker: {}", error.detail);
            let exit = if error.class == "Negative" { 1 } else { 2 };
            Ok((error_outcome(error.class, error.code), exit))
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok((outcome, exit)) => {
            print_json(&envelope(outcome));
            ExitCode::from(exit)
        }
        Err(error) => {
            eprintln!("rust checker failed: {}", error.detail);
            print_json(&envelope(error_outcome(
                "CheckerFailure",
                "F1R-CHECKER-FAILURE",
            )));
            ExitCode::from(3)
        }
    }
}
