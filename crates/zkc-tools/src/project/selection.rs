//! Validate the compiler-owned selection returned over the process boundary.
use serde_json::Value as Json;

pub(super) fn canonical_name(name: &str) -> bool {
    name.rsplit_once("::")
        .is_some_and(|(module, _)| module.len() <= 2048)
        && name.split("::").all(identifier)
}

pub(super) fn identifier(name: &str) -> bool {
    name.len() <= 128 && crate::source_names::is_source_identifier(name)
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

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn canonical_unicode_selection_keeps_exact_names_and_byte_limits() {
        let name = "数学::𐐀::証明₂";
        assert!(canonical_name(name));
        assert!(matches(Some("証明₂"), name));
        assert!(matches(Some(name), name));
        assert!(!matches(Some("証明_2"), name));
        for invalid in [
            "証明₂",
            "::証明₂",
            "数学::::証明₂",
            "数学::e\u{301}",
            "数学::証\u{200d}明",
        ] {
            assert!(!canonical_name(invalid), "{invalid}");
        }
        assert!(canonical_name(&format!("数学::{}", "α".repeat(64))));
        assert!(!canonical_name(&format!("数学::{}", "α".repeat(65))));
        assert!(!canonical_name(&format!("{}証明", "a::".repeat(1024))));
        let report = json!({"entries":[{"name":name,"kind":"proof"}],"entry":name});
        assert!(valid_check(&report, Some("証明₂")));
        let text = report.to_string().replace('𐐀', "\\ud801\\udc00");
        assert!(valid_check(
            &serde_json::from_str(&text).unwrap(),
            Some(name)
        ));
        let duplicate = json!({"entries":[{"name":name,"kind":"proof"},{"name":name,"kind":"run"}],"entry":name});
        assert!(!valid_check(&duplicate, Some(name)));
    }
}
