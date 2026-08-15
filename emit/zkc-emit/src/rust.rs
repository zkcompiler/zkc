//! The one path from an input string to emitted Rust text.
//!
//! Everything the emitter writes is assembled by concatenation, and the
//! strings it concatenates come from the document and the binding —
//! labels, class names, domains, the source identity, the binding's own
//! name. A string reaching generated source is therefore untrusted
//! input crossing into a language, and there are exactly three
//! positions it can land in, each with its own rule:
//!
//! - an **identifier** (a struct field, a crate alias), which must be a
//!   Rust identifier, must not be a keyword, and must not collide with
//!   another identifier in the same scope;
//! - a **string literal**, which must be escaped;
//! - a **line comment**, which must not be able to end the comment.
//!
//! Applying the rule at each interpolation site makes correctness a
//! matter of remembering, and the failures are not subtle: a `source`
//! carrying one quotation mark closes the literal that holds it and
//! opens whatever follows, and a label carrying a line break ends the
//! comment that quotes it. These constructors are the funnel; nothing
//! else in the emitter interpolates an input string into generated
//! text.

use std::collections::HashSet;

/// Reserved words that cannot name a struct field. Weak keywords
/// (`union`, `macro_rules`) are admitted because Rust admits them.
const KEYWORDS: &[&str] = &[
    // strict
    "as", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern", "false", "fn",
    "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
    "return", "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe",
    "use", "where", "while", // 2018 strict
    "async", "await", // reserved for future use
    "abstract", "become", "box", "do", "final", "macro", "override", "priv", "typeof", "unsized",
    "virtual", "yield", "try",
];

/// Is this text usable verbatim as a Rust field name?
///
/// Endpoint ABI labels become field names unchanged, so the naming
/// authority is the artifact and both cases are admitted; the emitted
/// struct carries `allow(non_snake_case)` to keep that quiet.
fn is_ident(text: &str) -> bool {
    !text.is_empty()
        && text.chars().next().unwrap().is_ascii_alphabetic()
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !KEYWORDS.contains(&text)
}

/// The identifiers of one generated scope — the fields of one struct.
///
/// Uniqueness is a property of the set, not of any one name, so it
/// cannot be checked where a single label is converted. A scope holds
/// the set and refuses the collision by name.
pub struct Scope {
    /// What the scope is, for the refusal message ("statement label").
    what: &'static str,
    seen: HashSet<String>,
}

impl Scope {
    pub fn new(what: &'static str) -> Scope {
        Scope {
            what,
            seen: HashSet::new(),
        }
    }

    /// Admit one label as an identifier in this scope.
    pub fn ident(&mut self, label: &str) -> Result<String, String> {
        let what = self.what;
        if !is_ident(label) {
            return Err(format!(
                "{what} '{}' is not usable as a field name: an identifier is ASCII \
                 alphanumeric with underscores, starts with a letter, and is not a Rust \
                 keyword",
                comment(label)
            ));
        }
        if !self.seen.insert(label.to_owned()) {
            return Err(format!(
                "{what} '{label}' appears twice; each names a distinct field"
            ));
        }
        Ok(label.to_owned())
    }
}

/// A Rust string literal carrying exactly this text.
pub fn literal(text: &str) -> String {
    format!("{text:?}")
}

/// Text that is safe on a `//` line: no line break can end the comment
/// early, and no control character can disturb the file. The rendering
/// is lossless enough to read the original back.
pub fn comment(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for character in text.chars() {
        match character {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            other if other.is_control() => {
                out.push_str(&format!("\\u{{{:x}}}", other as u32));
            }
            other => out.push(other),
        }
    }
    out
}

/// A cargo package name, and the crate identifier derived from it.
/// Both reach generated text — the name into `Cargo.toml`, the
/// identifier into the conformance suite's `use` — so both are checked
/// here rather than discovered by cargo or rustc downstream.
pub fn crate_name(name: &str) -> Result<(String, String), String> {
    let usable = !name.is_empty()
        && name.chars().next().unwrap().is_ascii_alphabetic()
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
    if !usable {
        return Err(format!(
            "crate name '{}' is not a usable package name: ASCII alphanumeric with hyphens \
             and underscores, starting with a letter",
            comment(name)
        ));
    }
    let ident = name.replace('-', "_");
    if KEYWORDS.contains(&ident.as_str()) {
        return Err(format!(
            "crate name '{name}' becomes the Rust identifier '{ident}', which is a keyword"
        ));
    }
    Ok((name.to_owned(), ident))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reserved_words_are_refused_as_field_names() {
        // Rust refuses these as struct fields. The list includes words
        // reserved for future use, which parse no better than the ones
        // in use.
        for keyword in [
            "yield", "become", "try", "do", "final", "Self", "self", "crate",
        ] {
            assert!(!is_ident(keyword), "{keyword} should be refused");
        }
        // Weak keywords are legal field names, so admitting them is
        // correct rather than lax.
        for weak in ["union", "macro_rules"] {
            assert!(is_ident(weak), "{weak} should be admitted");
        }
    }

    #[test]
    fn a_scope_refuses_the_second_use_of_a_label() {
        let mut scope = Scope::new("statement label");
        assert!(scope.ident("y").is_ok());
        let repeated = scope.ident("y").unwrap_err();
        assert!(repeated.contains("appears twice"), "{repeated}");
    }

    #[test]
    fn a_quotation_mark_cannot_leave_its_literal() {
        // A source identity carrying a quote, which in literal position
        // would otherwise close the literal and open code.
        let injected = "sha256:aa\" ; pub fn oops() {} const X: &str = \"bb";
        let rendered = literal(injected);
        assert!(rendered.starts_with('"') && rendered.ends_with('"'));
        // Every quotation mark inside the literal is escaped, so none of
        // them closes it and the text after them stays text.
        let interior: Vec<char> = rendered[1..rendered.len() - 1].chars().collect();
        for (at, character) in interior.iter().enumerate() {
            if *character == '"' {
                assert_eq!(
                    interior.get(at.wrapping_sub(1)),
                    Some(&'\\'),
                    "bare quote at {at}"
                );
            }
        }
        assert!(rendered.contains("\\\""), "the quotes should be escaped");
    }

    #[test]
    fn a_line_break_cannot_leave_its_comment() {
        assert_eq!(comment("a\nlet oops = 1;"), "a\\nlet oops = 1;");
        assert_eq!(comment("tab\there"), "tab\\there");
    }

    #[test]
    fn crate_names_are_checked_before_cargo_sees_them() {
        assert_eq!(
            crate_name("zkc-verifier-abc").unwrap(),
            ("zkc-verifier-abc".to_owned(), "zkc_verifier_abc".to_owned())
        );
        assert!(crate_name("1bad").is_err());
        assert!(crate_name("bad name").is_err());
        assert!(crate_name("loop").is_err());
    }
}
