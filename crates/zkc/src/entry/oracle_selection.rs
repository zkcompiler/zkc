//! Strict requested oracle selection. Installed implementations and source
//! occurrence coverage are checked by compilation against prepared source.
use serde::{
    Deserialize, Serialize,
    de::{self, MapAccess, Visitor},
};
use std::{collections::BTreeSet, fmt};

const FORMAT: &str = "zkc.oracle-selection/0";
const BYTE_LIMIT: usize = 1024 * 1024;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case", remote = "Self")]
pub enum OracleLeafGrouping {
    #[default]
    Individual,
    AntipodalPairs,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case", remote = "Self")]
pub enum OracleLeafOrder {
    #[default]
    Natural,
    BitReversed,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case", remote = "Self")]
pub enum OracleQueryOrder {
    #[default]
    Unrestricted,
    AfterFinalDraw,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case", remote = "Self")]
pub enum OracleAuthentication {
    #[default]
    PerQuery,
    AtomicBlocks,
}
macro_rules! serialize_remote {
    ($($ty:ty),*) => {$(impl Serialize for $ty {
        fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            Self::serialize(self, s)
        }
    })*};
}
serialize_remote!(
    OracleLeafGrouping,
    OracleLeafOrder,
    OracleQueryOrder,
    OracleAuthentication
);
super::decode::names!(
    OracleLeafGrouping,
    OracleLeafOrder,
    OracleQueryOrder,
    OracleAuthentication
);

#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields, remote = "Self")]
pub struct OracleTableRealization {
    pub scheme: String,
    pub grouping: OracleLeafGrouping,
    pub order: OracleLeafOrder,
}
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields, remote = "Self")]
pub struct OracleRootSelection {
    pub entry: String,
    pub path: Vec<u32>,
    pub scheme: String,
    pub grouping: OracleLeafGrouping,
    pub order: OracleLeafOrder,
}
serialize_remote!(OracleTableRealization, OracleRootSelection);
super::decode::objects!(OracleTableRealization, OracleRootSelection);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OracleRoots {
    Uniform(OracleTableRealization),
    Exact(Vec<OracleRootSelection>),
}
impl Default for OracleRoots {
    fn default() -> Self {
        Self::Uniform(OracleTableRealization::default())
    }
}
impl<'de> Deserialize<'de> for OracleRoots {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct Roots;
        impl<'de> Visitor<'de> for Roots {
            type Value = OracleRoots;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("an exact uniform or exact roots object")
            }
            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                let (mut kind, mut table, mut entries) = (None, None, None);
                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "kind" if kind.is_none() => kind = Some(map.next_value::<String>()?),
                        "table" if table.is_none() => {
                            table = Some(map.next_value::<OracleTableRealization>()?)
                        }
                        "entries" if entries.is_none() => {
                            entries = Some(map.next_value::<Vec<OracleRootSelection>>()?)
                        }
                        _ => return Err(de::Error::custom("unknown or duplicate selection field")),
                    }
                }
                match (kind.as_deref(), table, entries) {
                    (Some("uniform"), Some(table), None) => Ok(OracleRoots::Uniform(table)),
                    (Some("exact"), None, Some(entries)) => Ok(OracleRoots::Exact(entries)),
                    _ => Err(de::Error::custom("invalid selection roots")),
                }
            }
        }
        d.deserialize_map(Roots)
    }
}
impl Serialize for OracleRoots {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;
        let mut map = s.serialize_map(Some(2))?;
        match self {
            Self::Uniform(table) => {
                map.serialize_entry("kind", "uniform")?;
                map.serialize_entry("table", table)?;
            }
            Self::Exact(entries) => {
                let mut sorted: Vec<_> = entries.iter().collect();
                sorted.sort_by(|a, b| (&a.entry, &a.path).cmp(&(&b.entry, &b.path)));
                map.serialize_entry("kind", "exact")?;
                map.serialize_entry("entries", &sorted)?;
            }
        }
        map.end()
    }
}

#[derive(Clone, Debug, Default, Eq)]
pub struct OracleSelection {
    pub roots: OracleRoots,
    pub order: OracleQueryOrder,
    pub authentication: OracleAuthentication,
}
impl PartialEq for OracleSelection {
    fn eq(&self, other: &Self) -> bool {
        if self.order != other.order || self.authentication != other.authentication {
            return false;
        }
        match (&self.roots, &other.roots) {
            (OracleRoots::Uniform(a), OracleRoots::Uniform(b)) => a == b,
            (OracleRoots::Exact(a), OracleRoots::Exact(b)) => {
                let mut a: Vec<_> = a.iter().collect();
                let mut b: Vec<_> = b.iter().collect();
                a.sort_by(|a, b| (&a.entry, &a.path).cmp(&(&b.entry, &b.path)));
                b.sort_by(|a, b| (&a.entry, &a.path).cmp(&(&b.entry, &b.path)));
                a == b
            }
            _ => false,
        }
    }
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields, remote = "Self")]
struct Request {
    format: String,
    roots: OracleRoots,
    order: OracleQueryOrder,
    authentication: OracleAuthentication,
}
super::decode::objects!(Request);
impl<'de> Deserialize<'de> for OracleSelection {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let request = <Request as Deserialize>::deserialize(d)?;
        if request.format != FORMAT {
            return Err(de::Error::custom("oracle-selection-format"));
        }
        let result = Self {
            roots: request.roots,
            order: request.order,
            authentication: request.authentication,
        };
        result.validate().map_err(de::Error::custom)?;
        // Also applies to nested package/project settings, rather than just parse().
        result.canonical_json().map_err(de::Error::custom)?;
        Ok(result)
    }
}
impl Serialize for OracleSelection {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let (value, _) = self.encoded().map_err(serde::ser::Error::custom)?;
        value.serialize(s)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleSelectionError;
impl fmt::Display for OracleSelectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("oracle-realization-selection")
    }
}
impl std::error::Error for OracleSelectionError {}
impl OracleSelection {
    pub fn parse(text: &str) -> Result<Self, OracleSelectionError> {
        if text.len() > BYTE_LIMIT || !bounded_json(text) {
            return Err(OracleSelectionError);
        }
        serde_json::from_str(text).map_err(|_| OracleSelectionError)
    }
    pub fn canonical_json(&self) -> Result<String, OracleSelectionError> {
        self.encoded().map(|(_, text)| text)
    }
    /// Bind a canonical compiler inventory to the request. Source coverage and
    /// installed realization checking remain the compiler's responsibility.
    #[cfg(any(feature = "cpu", feature = "evm"))]
    pub(crate) fn check_normalized(&self, encoded: &str) -> Result<(), OracleSelectionError> {
        let normalized = Self::parse(encoded)?;
        let OracleRoots::Exact(entries) = &normalized.roots else {
            return Err(OracleSelectionError);
        };
        let roots_match = match &self.roots {
            OracleRoots::Uniform(table) => entries.iter().all(|root| {
                root.scheme == table.scheme
                    && root.grouping == table.grouping
                    && root.order == table.order
            }),
            OracleRoots::Exact(_) => self == &normalized,
        };
        if normalized.canonical_json()? != encoded
            || normalized.order != self.order
            || normalized.authentication != self.authentication
            || !roots_match
        {
            return Err(OracleSelectionError);
        }
        Ok(())
    }
    fn encoded(&self) -> Result<(serde_json::Value, String), OracleSelectionError> {
        self.validate()?;
        let value = self.value();
        let text = serde_json::to_string(&value).map_err(|_| OracleSelectionError)?;
        if text.len() > BYTE_LIMIT {
            return Err(OracleSelectionError);
        }
        Ok((value, text))
    }
    pub fn validate(&self) -> Result<(), OracleSelectionError> {
        let valid_table = |scheme: &str, grouping, order| {
            scheme.len() <= 4096
                && (!scheme.is_empty()
                    || (grouping == OracleLeafGrouping::Individual
                        && order == OracleLeafOrder::Natural))
        };
        let valid = match &self.roots {
            OracleRoots::Uniform(t) => valid_table(&t.scheme, t.grouping, t.order),
            OracleRoots::Exact(entries) => {
                let mut seen = BTreeSet::new();
                entries.len() <= 100_000
                    && entries.iter().all(|r| {
                        !r.entry.is_empty()
                            && r.entry.len() <= 4096
                            && !r.path.is_empty()
                            && r.path.len() <= 64
                            && valid_table(&r.scheme, r.grouping, r.order)
                            && seen.insert((&r.entry, &r.path))
                    })
            }
        };
        if valid {
            Ok(())
        } else {
            Err(OracleSelectionError)
        }
    }
    fn value(&self) -> serde_json::Value {
        serde_json::json!({"format": FORMAT, "roots": self.roots,
            "order": self.order, "authentication": self.authentication})
    }
}
// Bound nesting before serde's recursive parser. Numeric syntax outside strings
// is restricted to canonical unsigned tokens, including rejection of -0.
fn bounded_json(text: &str) -> bool {
    let bytes = text.as_bytes();
    let (mut i, mut depth) = (0, 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    if bytes[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
                }
            }
            b'{' | b'[' => {
                depth += 1;
                if depth > 32 {
                    return false;
                }
            }
            b'}' | b']' => {
                let Some(next) = depth.checked_sub(1) else {
                    return false;
                };
                depth = next;
            }
            b'-' | b'+' | b'.' => return false,
            b'0'..=b'9' => {
                let start = i;
                while i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit() {
                    i += 1;
                }
                if (bytes[start] == b'0' && i > start)
                    || bytes
                        .get(i + 1)
                        .is_some_and(|b| matches!(*b, b'.' | b'e' | b'E'))
                {
                    return false;
                }
            }
            _ => (),
        }
        i += 1;
    }
    depth == 0
}

// Package authentication happens before this scan. Preserve the request's raw
// byte/nesting/numeric limits even when it is nested in a much larger package.
pub(super) fn validate_packaged_selection(bytes: &[u8]) -> Result<(), OracleSelectionError> {
    fn string_end(bytes: &[u8], mut at: usize) -> usize {
        at += 1;
        while at < bytes.len() {
            match bytes[at] {
                b'"' => return at + 1,
                b'\\' => at += 1,
                _ => (),
            }
            at += 1;
        }
        bytes.len()
    }
    let mut at = 0;
    while at < bytes.len() {
        if bytes[at] != b'"' {
            at += 1;
            continue;
        }
        let end = string_end(bytes, at);
        let mut next = end;
        while bytes.get(next).is_some_and(u8::is_ascii_whitespace) {
            next += 1;
        }
        if bytes.get(next) != Some(&b':') {
            at = end;
            continue;
        }
        let key: String =
            serde_json::from_slice(&bytes[at..end]).map_err(|_| OracleSelectionError)?;
        if key != "oracle_realization" {
            at = end;
            continue;
        }
        next += 1;
        // Whitespace within the authored value also consumes its byte budget.
        let start = next;
        while bytes.get(next).is_some_and(u8::is_ascii_whitespace) {
            next += 1;
        }
        if bytes.get(next) != Some(&b'{') {
            return Err(OracleSelectionError);
        }
        let mut depth = 0usize;
        while next < bytes.len() {
            if next - start >= BYTE_LIMIT {
                return Err(OracleSelectionError);
            }
            match bytes[next] {
                b'"' => {
                    next = string_end(bytes, next);
                    continue;
                }
                b'{' | b'[' => {
                    depth += 1;
                    if depth > 32 {
                        return Err(OracleSelectionError);
                    }
                }
                b'}' | b']' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => (),
            }
            next += 1;
        }
        let text = bytes
            .get(start..=next)
            .and_then(|b| std::str::from_utf8(b).ok())
            .ok_or(OracleSelectionError)?;
        OracleSelection::parse(text)?;
        at = next + 1;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};
    fn exact(entries: Value) -> String {
        json!({"format":FORMAT,"roots":{"kind":"exact","entries":entries},
            "order":"unrestricted","authentication":"per-query"})
        .to_string()
    }
    fn root() -> Value {
        json!({"entry":"main","path":[0],"scheme":"","grouping":"individual","order":"natural"})
    }
    #[test]
    fn default_and_exact_empty_are_distinct_and_round_trip() {
        let default = OracleSelection::default();
        let text = default.canonical_json().unwrap();
        assert_eq!(
            text,
            r#"{"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"kind":"uniform","table":{"grouping":"individual","order":"natural","scheme":""}}}"#
        );
        assert_eq!(OracleSelection::parse(&text).unwrap(), default);
        assert_eq!(
            serde_json::from_str::<OracleSelection>(&text).unwrap(),
            default
        );
        let empty = OracleSelection::parse(&exact(json!([]))).unwrap();
        assert_ne!(default, empty);
        assert_ne!(text, empty.canonical_json().unwrap());
    }
    #[test]
    fn exact_inventory_order_has_one_semantic_serialization() {
        let a = root();
        let mut b = root();
        b["path"] = json!([u32::MAX]);
        let first = OracleSelection::parse(&exact(json!([a, b]))).unwrap();
        let second = OracleSelection::parse(&exact(json!([b, a]))).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            first.canonical_json().unwrap(),
            second.canonical_json().unwrap()
        );
        assert!(OracleSelection::parse(&exact(json!([a, a]))).is_err());
        let mut unknown = a;
        unknown["scheme"] = json!("explicit-unknown/0");
        // Installation is a property of each actual selected kind, not the codec.
        assert!(OracleSelection::parse(&exact(json!([unknown]))).is_ok());
    }
    #[test]
    fn every_record_is_object_only_and_enums_are_string_only() {
        let baseline = serde_json::to_value(OracleSelection::default()).unwrap();
        for bad in [
            Value::Null,
            json!([]),
            json!([FORMAT, {}, "unrestricted", "per-query"]),
        ] {
            assert!(serde_json::from_value::<OracleSelection>(bad).is_err());
        }
        for bad in [
            json!([]),
            json!(["uniform", {"scheme":"","grouping":"individual","order":"natural"}]),
            json!({"uniform":{}}),
        ] {
            let mut v = baseline.clone();
            v["roots"] = bad;
            assert!(serde_json::from_value::<OracleSelection>(v).is_err());
        }
        let mut v = baseline.clone();
        v["roots"]["table"] = json!(["", "individual", "natural"]);
        assert!(serde_json::from_value::<OracleSelection>(v).is_err());
        assert!(
            OracleSelection::parse(&exact(json!([["main", [0], "", "individual", "natural"]])))
                .is_err()
        );
        for (field, bad) in [
            ("order", json!({"unrestricted":null})),
            ("authentication", json!({"per-query":null})),
        ] {
            let mut v = baseline.clone();
            v[field] = bad;
            assert!(serde_json::from_value::<OracleSelection>(v).is_err());
        }
    }
    #[test]
    fn mutations_reject_unknown_duplicate_missing_and_malformed_fields() {
        let text = OracleSelection::default().canonical_json().unwrap();
        for changed in [
            text.replace(FORMAT, "zkc.oracle-selection/1"),
            text.replacen('{', "{\"unknown\":0,", 1),
            text.replace(
                "\"kind\":\"uniform\"",
                "\"kind\":\"uniform\",\"kind\":\"uniform\"",
            ),
            text.replace("\"scheme\":\"\"", "\"scheme\":\"\",\"sch\\u0065me\":\"\""),
            text.replace("\"scheme\":\"\"", "\"scheme\":null"),
            text.replace("\"scheme\":\"\"", "\"scheme\":\"\\ud800\""),
            text.replace("\"scheme\":\"\"", "\"extra\":\"\""),
            text.replace("\"uniform\"", "\"unknown\""),
            text.replace("\"individual\"", "\"unknown\""),
            text.replace("\"natural\"", "\"unknown\""),
            text.replace("\"unrestricted\"", "\"unknown\""),
            text.replace("\"per-query\"", "\"unknown\""),
            text.replace("\"table\":{", "\"entries\":null,\"table\":{"),
            text.clone() + "{}",
        ] {
            assert!(
                OracleSelection::parse(&changed).is_err(),
                "accepted {changed}"
            );
        }
        let base: Value = serde_json::from_str(&text).unwrap();
        for field in ["format", "roots", "order", "authentication"] {
            let mut v = base.clone();
            v.as_object_mut().unwrap().remove(field);
            assert!(OracleSelection::parse(&v.to_string()).is_err(), "{field}");
        }
        let mut v = root();
        v["extra"] = json!(false);
        assert!(OracleSelection::parse(&exact(json!([v]))).is_err());
    }
    #[test]
    fn canonical_unsigned_paths_and_layout_rules_are_enforced() {
        let text = exact(json!([root()]));
        for path in [
            "[]",
            "[-0]",
            "[-1]",
            "[+1]",
            "[01]",
            "[1.0]",
            "[1e0]",
            "[4294967296]",
            "[18446744073709551616]",
            "[true]",
            "[\"0\"]",
            "null",
            "{}",
        ] {
            let changed = text.replace("\"path\":[0]", &format!("\"path\":{path}"));
            assert!(OracleSelection::parse(&changed).is_err(), "{path}");
        }
        for (grouping, order) in [
            ("antipodal-pairs", "natural"),
            ("individual", "bit-reversed"),
        ] {
            let mut v = root();
            v["grouping"] = json!(grouping);
            v["order"] = json!(order);
            assert!(OracleSelection::parse(&exact(json!([v]))).is_err());
            v["scheme"] = json!("selected/0");
            assert!(OracleSelection::parse(&exact(json!([v]))).is_ok());
        }
    }
    #[test]
    fn matching_bounds_apply_to_names_paths_counts_bytes_and_nesting() {
        for field in ["entry", "scheme"] {
            let mut v = root();
            v[field] = json!("é".repeat(2048));
            assert!(OracleSelection::parse(&exact(json!([v]))).is_ok());
            v[field] = json!("a".repeat(4097));
            assert!(OracleSelection::parse(&exact(json!([v]))).is_err());
        }
        let mut v = root();
        v["path"] = json!(vec![0; 64]);
        assert!(OracleSelection::parse(&exact(json!([v]))).is_ok());
        v["path"] = json!(vec![0; 65]);
        assert!(OracleSelection::parse(&exact(json!([v]))).is_err());
        assert!(OracleSelection::parse(&" ".repeat(BYTE_LIMIT + 1)).is_err());
        assert!(OracleSelection::parse(&("[".repeat(33) + &"]".repeat(33))).is_err());
        let many = OracleSelection {
            roots: OracleRoots::Exact(
                (0..100_001)
                    .map(|i| OracleRootSelection {
                        entry: "main".into(),
                        path: vec![i],
                        scheme: String::new(),
                        grouping: Default::default(),
                        order: Default::default(),
                    })
                    .collect(),
            ),
            ..Default::default()
        };
        assert!(many.validate().is_err());
        assert!(many.canonical_json().is_err());
    }
    #[test]
    fn packaged_request_retains_lexical_limits_and_escaped_key_identity() {
        let request = OracleSelection::default().canonical_json().unwrap();
        for key in ["oracle_realization", "oracle_realizati\\u006fn"] {
            let valid = format!("{{\"options\":{{\"{key}\":{request}}}}}");
            assert!(validate_packaged_selection(valid.as_bytes()).is_ok());
            let too_big = format!(
                "{{\"options\":{{\"{key}\":{}{request}}}}}",
                " ".repeat(BYTE_LIMIT)
            );
            assert!(validate_packaged_selection(too_big.as_bytes()).is_err());
        }
        let path = exact(json!([root()])).replace("\"path\":[0]", "\"path\":[-0]");
        assert!(
            validate_packaged_selection(format!("{{\"oracle_realization\":{path}}}").as_bytes())
                .is_err()
        );
    }
}
