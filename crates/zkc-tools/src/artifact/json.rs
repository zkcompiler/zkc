//! Allocation-free preflight for the string/array JSON carriers.
//! Syntax and UTF-8 validation still belong to serde. Structural ceilings are
//! checked before serde allocates a value tree; quoted delimiters do not count.

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Error {
    Depth,
    Structure,
    Object,
    Scalar,
    Syntax,
}

pub(super) fn preflight(bytes: &[u8], max_nodes: usize, max_items: usize) -> Result<(), Error> {
    // Root depth is zero. At most 65 arrays can be active, but no further
    // child value may start inside the last one.
    let mut items = [0usize; 65];
    let (mut depth, mut nodes, mut quoted, mut escaped) = (0usize, 0usize, false, false);
    for &byte in bytes {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
            continue;
        }
        match byte {
            b'[' | b'"' => {
                if depth >= items.len() {
                    return Err(Error::Depth);
                }
                nodes += 1;
                if nodes > max_nodes {
                    return Err(Error::Structure);
                }
                if depth > 0 {
                    items[depth - 1] += 1;
                    if items[depth - 1] > max_items {
                        return Err(Error::Structure);
                    }
                }
                if byte == b'[' {
                    items[depth] = 0;
                    depth += 1;
                } else {
                    quoted = true;
                }
            }
            b']' => depth = depth.checked_sub(1).ok_or(Error::Syntax)?,
            b'{' | b'}' => return Err(Error::Object),
            b',' | b' ' | b'\t' | b'\r' | b'\n' => (),
            b'n' | b't' | b'f' | b'-' | b'0'..=b'9' => return Err(Error::Scalar),
            _ => return Err(Error::Syntax),
        }
    }
    if quoted || depth != 0 {
        return Err(Error::Syntax);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_wide_and_quoted_values_obey_independent_limits() {
        assert_eq!(preflight(b"[[],[],[]]", 4, 2), Err(Error::Structure));
        assert_eq!(preflight(b"[[[]],[[]]]", 4, 2), Err(Error::Structure));
        assert_eq!(preflight(b"[[[]],[[]]]", 5, 2), Ok(()));
        assert_eq!(preflight(b"[0,0,0]", 4, 2), Err(Error::Scalar));
        assert_eq!(preflight(br#"["[\\\"{",[]]"#, 3, 2), Ok(()));
        let mut boundary = vec![b'['; 65];
        boundary.extend(vec![b']'; 65]);
        assert_eq!(preflight(&boundary, 65, 1), Ok(()));
        boundary.insert(65, b'"');
        boundary.insert(66, b'"');
        assert_eq!(preflight(&boundary, 66, 1), Err(Error::Depth));
    }

    use serde_json::{Value, json};

    fn metrics(v: &Value) -> (usize, usize, usize) {
        match v {
            Value::String(_) => (1, 0, 0),
            Value::Array(a) => a.iter().fold((1, a.len(), 0), |(n, w, d), v| {
                let (nn, ww, dd) = metrics(v);
                (n + nn, w.max(ww), d.max(dd + 1))
            }),
            _ => panic!("carrier only"),
        }
    }
    fn next(seed: &mut u64) -> usize {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (*seed >> 32) as usize
    }
    fn tree(seed: &mut u64, depth: usize) -> Value {
        let strings = [
            "",
            "[]{}",
            "\\\"[",
            "é한글😀",
            "\u{0}\n\t",
            "012nulltrue",
            "\\\\\"",
        ];
        if depth == 0 || next(seed).is_multiple_of(3) {
            json!(strings[next(seed) % strings.len()])
        } else {
            Value::Array((0..next(seed) % 5).map(|_| tree(seed, depth - 1)).collect())
        }
    }

    #[test]
    fn generated_trees_match_independent_structural_metrics() {
        let mut seed = 914;
        for i in 0..4096 {
            let value = tree(&mut seed, 6);
            let (n, w, d) = metrics(&value);
            assert!(d <= 64);
            let bytes = if i % 2 == 0 {
                serde_json::to_vec(&value)
            } else {
                serde_json::to_vec_pretty(&value)
            }
            .unwrap();
            assert_eq!(preflight(&bytes, n, w), Ok(()), "case {i}");
            assert_eq!(
                preflight(&bytes, n - 1, w),
                Err(Error::Structure),
                "case {i}"
            );
            if w > 0 {
                assert_eq!(
                    preflight(&bytes, n, w - 1),
                    Err(Error::Structure),
                    "case {i}"
                );
            }
            assert_eq!(
                crate::artifact::io::parse(&bytes, 16 * 1024 * 1024).unwrap(),
                value
            );
            assert_eq!(
                crate::artifact::primitive::parse_request(&bytes).unwrap(),
                value
            );
        }
    }

    #[test]
    fn depth_nodes_width_and_escaped_delimiters() {
        for (leaf, allowed) in [("[]", 64), ("\"x\"", 64)] {
            for wrappers in [allowed, allowed + 1] {
                let s = "[".repeat(wrappers) + leaf + &"]".repeat(wrappers);
                assert_eq!(
                    preflight(s.as_bytes(), 200000, 32768).is_ok(),
                    wrappers == allowed
                );
                assert_eq!(
                    crate::artifact::io::parse(s.as_bytes(), s.len()).is_ok(),
                    wrappers == allowed
                );
            }
        }
        for (nodes, width) in [(200000, 32768), (500000, 100000)] {
            let at_width = "[".to_owned() + &vec!["[]"; width].join(",") + "]";
            assert!(preflight(at_width.as_bytes(), nodes, width).is_ok());
            assert_eq!(
                preflight(at_width.as_bytes(), nodes, width - 1),
                Err(Error::Structure)
            );
            let mut groups = Vec::new();
            let mut remaining = nodes - 1;
            while remaining > 0 {
                let children = (remaining - 1).min(width);
                groups.push("[".to_owned() + &vec!["[]"; children].join(",") + "]");
                remaining -= children + 1;
            }
            let at_nodes = "[".to_owned() + &groups.join(",") + "]";
            assert!(preflight(at_nodes.as_bytes(), nodes, width).is_ok());
            assert_eq!(
                preflight(at_nodes.as_bytes(), nodes - 1, width),
                Err(Error::Structure)
            );
        }
        for s in [
            r#"["\u005b\u007b\u0022", "\\\"[]"]"#,
            r#"["\ud83d\ude00", "\u0000"]"#,
        ] {
            assert!(preflight(s.as_bytes(), 3, 2).is_ok());
            assert!(crate::artifact::io::parse(s.as_bytes(), s.len()).is_ok());
        }
        for s in [
            r#"["\uD800"]"#,
            r#"["\q"]"#,
            r#"["a" "b"]"#,
            r#"["a",]"#,
            r#"[] []"#,
            r#"[[]"#,
            r#"[null]"#,
            r#"[{}]"#,
        ] {
            assert!(
                crate::artifact::io::parse(s.as_bytes(), s.len()).is_err(),
                "{s}"
            );
            assert!(
                crate::artifact::primitive::parse_request(s.as_bytes()).is_err(),
                "{s}"
            );
        }
        assert!(crate::artifact::primitive::parse_request(b"[\"\xff\"]").is_err());
    }
}
