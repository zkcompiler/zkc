//! Validate the compiler-owned selection returned over the process boundary.
use serde_json::Value as Json;

pub(super) fn canonical_name(name: &str) -> bool {
    name.contains("::") && name.split("::").all(identifier)
}

pub(super) fn identifier(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

pub(super) fn matches(request: Option<&str>, canonical: &str) -> bool {
    canonical_name(canonical)
        && request.is_none_or(|name| {
            if name.contains("::") {
                name == canonical
            } else {
                canonical.rsplit("::").next() == Some(name)
            }
        })
}

// The compiler owns discovery and selection. Validate that its diagnostic view
// describes the requested scope and canonical spelling before reporting success.
pub(super) fn valid_check(report: &Json, request: Option<&str>) -> bool {
    let Some(entries) = report["entries"].as_array() else {
        return false;
    };
    let mut previous = "";
    for candidate in entries {
        let Some(name) = candidate["name"].as_str() else {
            return false;
        };
        if !canonical_name(name)
            || name <= previous
            || !matches!(candidate["kind"].as_str(), Some("run" | "proof"))
            || candidate.as_object().is_none_or(|obj| obj.len() != 2)
        {
            return false;
        }
        previous = name;
    }
    match request {
        None => report.get("entry").is_none(),
        Some(_) => report["entry"].as_str().is_some_and(|selected| {
            matches(request, selected)
                && entries
                    .iter()
                    .filter(|candidate| matches(request, candidate["name"].as_str().unwrap()))
                    .count()
                    == 1
                && entries
                    .iter()
                    .any(|candidate| candidate["name"] == selected)
        }),
    }
}
