//! Validate the compiler-owned selection returned over the process boundary.
use serde_json::Value as Json;

/// Argument syntax is compiler-owned. Consumers only normalize lexical trivia
/// for request equality; they never resolve types, defaults or requirements.
pub(crate) fn compact(name: &str) -> Option<String> {
    if name.len() > 4096 {
        return None;
    }
    let mut text = String::new();
    let mut chars = name.chars().peekable();
    let mut quoted = false;
    let mut separated = false;
    while let Some(c) = chars.next() {
        if !quoted && c == '/' && chars.peek() == Some(&'/') {
            for c in chars.by_ref() {
                if c == '\n' {
                    break;
                }
            }
            separated = true;
        } else if !quoted && c.is_ascii_whitespace() {
            separated = true;
        } else {
            // Trivia cannot turn two source tokens into one identifier/number.
            if separated
                && text
                    .chars()
                    .last()
                    .is_some_and(|p| p.is_alphanumeric() || p == '_')
                && (c.is_alphanumeric() || c == '_')
            {
                return None;
            }
            if c.is_control() || c == '\\' {
                return None;
            }
            if c == '"' {
                quoted = !quoted;
            }
            text.push(c);
            separated = false;
        }
    }
    (!quoted).then_some(text)
}

pub(crate) fn parts(name: &str) -> (&str, &str) {
    name.find('<')
        .map_or((name, ""), |i| (&name[..i], &name[i..]))
}

pub(crate) fn canonical_name(name: &str) -> bool {
    let (path, arguments) = parts(name);
    path.rsplit_once("::")
        .is_some_and(|(module, _)| module.len() <= 2048)
        && path.split("::").all(identifier)
        && (arguments.is_empty() || (arguments.len() > 2 && arguments.ends_with('>')))
        && compact(name).is_some_and(|value| value == name)
}

pub(super) fn identifier(name: &str) -> bool {
    name.len() <= 128 && crate::source_names::is_source_identifier(name)
}

pub(super) fn matches(request: Option<&str>, canonical: &str) -> bool {
    if !canonical_name(canonical) {
        return false;
    }
    let Some(request) = request else {
        return true;
    };
    let Some(request) = compact(request) else {
        return false;
    };
    let (requested_path, requested_args) = parts(&request);
    let (path, arguments) = parts(canonical);
    requested_args == arguments
        && if requested_path.contains("::") {
            requested_path.trim_start_matches("::") == path
        } else {
            path.rsplit("::").next() == Some(requested_path)
        }
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
            || !matches!(candidate["kind"].as_str(), Some("function" | "proof"))
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
    fn generic_selection_keeps_argument_qualification_and_normalizes_trivia() {
        let canonical = "sigma::Schnorr<example::G>";
        assert!(canonical_name(canonical));
        for request in [
            "Schnorr<example::G>",
            canonical,
            " Schnorr < example::G > ",
            "Schnorr<// source comment\nexample::G>",
        ] {
            assert!(matches(Some(request), canonical), "{request}");
        }
        for request in [
            "Schnorr",
            "Schnorr<Other>",
            "Other<example::G>",
            "wrong::Schnorr<example::G>",
            "Schnorr<ex ample::G>",
        ] {
            assert!(!matches(Some(request), canonical), "{request}");
        }
        let report = json!({"entries":[{"name":canonical,"kind":"function"}],"entry":canonical});
        assert!(valid_check(&report, Some("Schnorr<example::G>")));
        assert!(!valid_check(&report, Some("Schnorr<Other>")));
        assert!(!canonical_name("sigma::Schnorr< example::G >"));
        let boundary = format!(
            "example::Work<{}1>",
            "0".repeat(4096 - "example::Work<1>".len())
        );
        assert!(canonical_name(&boundary));
        assert!(!canonical_name(&format!("{boundary} ")));
        assert!(!canonical_name("sigma::Schnorr<>"));
        assert_eq!(
            compact("Test<builtin(\"a b\")>"),
            Some("Test<builtin(\"a b\")>".into())
        );
    }
    #[test]
    fn discovery_selects_functions_without_a_source_run_alias() {
        let function =
            json!({"entries":[{"name":"sample::Main","kind":"function"}],"entry":"sample::Main"});
        assert!(valid_check(&function, Some("Main")));
        let old = json!({"entries":[{"name":"sample::Main","kind":"run"}],"entry":"sample::Main"});
        assert!(!valid_check(&old, Some("Main")));
        assert!(serde_json::from_str::<crate::project::EntryKind>("\"run\"").is_err());
        assert_eq!(
            serde_json::to_value(crate::project::EntryKind::Function).unwrap(),
            "function"
        );
    }
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
