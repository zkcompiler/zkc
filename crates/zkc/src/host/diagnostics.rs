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
