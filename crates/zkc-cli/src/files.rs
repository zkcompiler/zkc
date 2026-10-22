//! Command presentation for typed SDK filesystem operations.
use serde_json::{Value as Json, json};
pub(crate) use zkc::files::Outputs;
pub(crate) fn read_regular(
    path: impl AsRef<std::path::Path>,
    limit: usize,
) -> Result<Vec<u8>, String> {
    zkc::files::read_regular(path, limit).map_err(|e| match e {
        zkc::files::ReadError::Io(_) => "artifact-io".into(),
        zkc::files::ReadError::Limit => "artifact-byte-limit".into(),
    })
}
pub(crate) fn publication(
    result: Result<zkc::files::Publication, zkc::files::PublicationError>,
    report: &mut Json,
    flags: bool,
) -> Result<(), String> {
    let (receipt, error) = match result {
        Ok(receipt) => (receipt, None),
        Err(error) => {
            if let Some(path) = &error.conflict {
                report["conflict"] = json!(path);
            }
            (*error.receipt, Some(error.code))
        }
    };
    if !receipt.requested.is_empty() || error.is_none() {
        let p = report
            .as_object_mut()
            .unwrap()
            .entry("publication")
            .or_insert_with(|| json!({"requested":[],"published":[]}));
        p["requested"]
            .as_array_mut()
            .unwrap()
            .extend(receipt.requested.iter().map(|n| json!(n)));
        p["published"]
            .as_array_mut()
            .unwrap()
            .extend(receipt.published.iter().map(|n| json!(n)));
        p["stage"] = json!(match receipt.stage {
            zkc::files::PublicationStage::Staging => "staging",
            zkc::files::PublicationStage::Publication => "publication",
            zkc::files::PublicationStage::Complete => "complete",
        });
        if let Some(name) = receipt.failed {
            p["failed"] = json!(name);
        }
        if flags {
            for name in receipt.published {
                report[format!("{name}_published")] = json!(true);
            }
        }
    }
    error.map_or(Ok(()), Err)
}

pub(crate) use zkc::files::{digest, hex};
pub(crate) fn unhex(value: &serde_json::Value) -> Result<Vec<u8>, String> {
    zkc::files::context_bytes(value.as_str().ok_or("artifact-string")?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkc::files::{Publication, PublicationError, PublicationStage};

    #[test]
    fn later_failure_retains_earlier_batches_and_exact_partial_success() {
        let mut report = json!({});
        publication(
            Ok(Publication {
                requested: vec!["source".into()],
                published: vec!["source".into()],
                stage: PublicationStage::Complete,
                failed: None,
            }),
            &mut report,
            false,
        )
        .unwrap();
        let error = publication(
            Err(PublicationError {
                code: "artifact-publish-io".into(),
                conflict: None,
                receipt: Box::new(Publication {
                    requested: vec!["proof".into(), "results".into()],
                    published: vec!["proof".into()],
                    stage: PublicationStage::Publication,
                    failed: Some("results".into()),
                }),
            }),
            &mut report,
            true,
        )
        .unwrap_err();
        assert_eq!(error, "artifact-publish-io");
        assert_eq!(
            report["publication"],
            json!({
                "requested":["source","proof","results"],
                "published":["source","proof"],"stage":"publication","failed":"results"
            })
        );
        assert_eq!(report["proof_published"], true);
        assert!(report.get("results_published").is_none());
        assert!(report.get("source_published").is_none());

        let previous = report["publication"].clone();
        assert_eq!(
            publication(
                Err(PublicationError {
                    code: "entry-output-exists".into(),
                    conflict: Some("existing".into()),
                    receipt: Box::default(),
                }),
                &mut report,
                false,
            )
            .unwrap_err(),
            "entry-output-exists"
        );
        assert_eq!(report["publication"], previous);
        assert_eq!(report["conflict"], "existing");
    }
}
