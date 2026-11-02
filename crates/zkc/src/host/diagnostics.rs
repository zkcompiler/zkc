//! Bounded observations for the parent Host journal. These are not semantic
//! origins or wire encodings; omitted coordinates and text are explicit.
use serde_json::{Value as Json, json};
use zkc_runtime::vm::{Origin, PathElement, Stop, StopKind};

pub(crate) const SCRATCH_BYTES: usize = 256 * 1024;
pub(crate) fn text(value: &str) -> &str {
    let mut end = value.len().min(128);
    while !value.is_char_boundary(end) {
        end -= 1;
    }
    &value[..end]
}
pub(crate) fn message(value: &str) -> Json {
    json!({"text":text(value),"omitted_bytes":value.len()-text(value).len()})
}
pub(crate) fn origin(value: &Origin) -> Json {
    json!([
        "zkc.origin/0",
        text(&value.session),
        text(&value.entry),
        text(&value.instance),
        value
            .path
            .iter()
            .take(4)
            .map(|p| match p {
                PathElement::Branch { site, alternative } =>
                    json!(["branch", text(site), text(alternative)]),
                PathElement::Match { site, alternative } =>
                    json!(["match", text(site), text(alternative)]),
                PathElement::Conditional { site, taken } =>
                    json!(["if", text(site), if *taken { "then" } else { "else" }]),
                PathElement::For { site, index } => json!(["for", text(site), index.to_string()]),
                PathElement::Loop { site, iteration } =>
                    json!(["loop", text(site), iteration.to_string()]),
            })
            .collect::<Vec<_>>()
    ])
}
pub(crate) fn stop(value: &Stop) -> Json {
    let (kind, cause) = match &value.kind {
        StopKind::Decode(reason) => ("Decode", json!(["decode", reason.as_str()])),
        StopKind::Explicit(reason) => ("Explicit", json!(["explicit", message(reason)])),
        StopKind::Backend(error) => ("Backend", json!(["backend", message(&error.code)])),
        StopKind::Limit => ("Limit", json!(["limit"])),
        StopKind::Cancelled => ("Cancelled", json!(["cancelled"])),
    };
    json!({"origin":origin(&value.origin),"origin_path_omitted":value.origin.path.len().saturating_sub(4),
        "role":text(&value.role),"site":value.site.as_deref().map(text),"kind":kind,"cause":cause,
        "local":value.local.as_ref().map(|l|json!({"site":text(&l.site),"function":text(&l.function),"instruction":l.instruction.as_deref().map(text)})),
        "cleanup_errors":value.cleanup_errors.iter().take(4).map(|e|message(&e.code)).collect::<Vec<_>>(),
        "cleanup_omitted":value.cleanup_errors.len().saturating_sub(4)})
}
/// Fixed allowance of one rendered node: a JSON value, string, array element
/// or object member, with its allocation header.
const NODE: usize = 256;
/// A bound of one string copied into a rendering.
pub(crate) fn text_bound(value: &str) -> usize {
    NODE.saturating_add(value.len())
}
/// A bound of a JSON tree copied into a rendering, read without serializing it.
pub(crate) fn json_bound(value: &Json) -> usize {
    NODE.saturating_add(match value {
        Json::String(s) => s.len(),
        Json::Array(items) => items.iter().map(json_bound).fold(0, usize::saturating_add),
        Json::Object(members) => members
            .iter()
            .map(|(key, value)| key.len().saturating_add(json_bound(value)))
            .fold(0, usize::saturating_add),
        _ => 0,
    })
}
/// A bound of a complete rendered origin: its names and every path element,
/// each with its site, alternative and decimal coordinate.
pub(crate) fn origin_bound(value: &Origin) -> usize {
    value
        .path
        .iter()
        .map(|element| {
            NODE.saturating_add(match element {
                PathElement::Branch { site, alternative }
                | PathElement::Match { site, alternative } => {
                    site.len().saturating_add(alternative.len())
                }
                PathElement::Conditional { site, .. }
                | PathElement::For { site, .. }
                | PathElement::Loop { site, .. } => site.len().saturating_add(20),
            })
        })
        .fold(
            NODE.saturating_mul(4)
                .saturating_add(value.session.len())
                .saturating_add(value.entry.len())
                .saturating_add(value.instance.len()),
            usize::saturating_add,
        )
}
/// A bound of a complete rendered stop. Its kind is rendered with debug
/// formatting, which can escape each byte of a message into several characters.
pub(crate) fn stop_bound(value: &Stop) -> usize {
    let kind = match &value.kind {
        StopKind::Explicit(reason) => reason.len(),
        StopKind::Backend(error) => error.code.len(),
        StopKind::Decode(_) | StopKind::Limit | StopKind::Cancelled => 0,
    };
    let local = value.local.as_ref().map_or(0, |local| {
        text_bound(&local.site)
            .saturating_add(text_bound(&local.function))
            .saturating_add(local.instruction.as_deref().map_or(0, text_bound))
    });
    value
        .cleanup_errors
        .iter()
        .map(|error| text_bound(&error.code))
        .fold(
            NODE.saturating_mul(8)
                .saturating_add(origin_bound(&value.origin))
                .saturating_add(text_bound(&value.role))
                .saturating_add(value.site.as_deref().map_or(0, text_bound))
                .saturating_add(NODE.saturating_add(kind.saturating_mul(10)))
                .saturating_add(local),
            usize::saturating_add,
        )
}
/// Clone a bounded prefix directly from a native diagnostic tree. Never clone
/// the original strings, complete arrays, or large intermediate trees first.
pub(crate) fn values<'a>(values: impl Iterator<Item = &'a Json>) -> Json {
    let mut nodes = 256;
    let mut bytes = 4096;
    Json::Array(
        values
            .take(16)
            .map(|v| trim(v, &mut nodes, &mut bytes, 0))
            .collect(),
    )
}
pub(crate) fn trim(value: &Json, nodes: &mut usize, bytes: &mut usize, depth: usize) -> Json {
    if *nodes == 0 || depth > 12 {
        return Json::Null;
    }
    *nodes -= 1;
    match value {
        Json::String(s) => {
            let mut end = s.len().min((*bytes).min(128));
            while !s.is_char_boundary(end) {
                end -= 1;
            }
            *bytes -= end;
            Json::String(s[..end].into())
        }
        Json::Array(v) => Json::Array(
            v.iter()
                .take(16)
                .map(|v| trim(v, nodes, bytes, depth + 1))
                .collect(),
        ),
        Json::Object(v) => Json::Object(
            v.iter()
                .take(32)
                .map(|(k, v)| (text(k).into(), trim(v, nodes, bytes, depth + 1)))
                .collect(),
        ),
        v => v.clone(),
    }
}
