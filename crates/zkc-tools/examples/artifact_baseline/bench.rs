use crate::{Result, codec::*, ensure, input::Input, source::Source, transcript::Session};
use serde_json::{Value, json};
use std::{path::Path, time::Instant};
fn stats(v: &[f64]) -> Value {
    let mut sorted = v.to_vec();
    sorted.sort_by(f64::total_cmp);
    let n = sorted.len();
    json!({"samples_ms":v,"min_ms":sorted[0],"median_ms":if n%2==1{sorted[n/2]}else{(sorted[n/2-1]+sorted[n/2])/2.0}})
}
pub fn run(
    s: &Source,
    inputs: &Path,
    proof_path: &Path,
    producer: bool,
    reps: usize,
) -> Result<Value> {
    ensure((1..=1000).contains(&reps), "repetitions-limit")?;
    let candidate = if producer {
        None
    } else {
        Some(read(proof_path, LIMIT)?)
    };
    let mut samples = Vec::new();
    let mut admissions = Vec::new();
    let mut setups = Vec::new();
    let mut vks = Vec::new();
    let mut pks = Vec::new();
    let mut last = json!(null);
    let mut produced = None;
    for _ in 0..reps {
        let start = Instant::now();
        let input = Input::load(s, inputs, producer)?;
        admissions.push(start.elapsed().as_secs_f64() * 1000.0);
        vks.push(input.vk_load_ms);
        pks.push(input.pk_load_ms);
        let start = Instant::now();
        let mut session = Session::new(&input.root, candidate.as_deref())?;
        setups.push(start.elapsed().as_secs_f64() * 1000.0);
        let start = Instant::now();
        let outcome = if let Some(n) = s.n {
            crate::two_factor::execute(&input, n, &mut session)
        } else {
            crate::dleq::execute(&input, &mut session)
        };
        samples.push(start.elapsed().as_secs_f64() * 1000.0);
        if let Err(error) = outcome {
            return Ok(
                json!({"status":"refused","code":error.to_string(),"events":session.events,"reached_messages":session.messages,"reached_draws":session.draws,"reached_transcript_actions":session.actions,"consumed_bytes":session.cursor}),
            );
        }
        if producer {
            if let Some(old) = &produced {
                ensure(*old == session.proof, "nondeterministic-development-proof")?;
            }
            produced = Some(session.proof);
        }
        last = json!({"events":session.events,"messages":session.messages,"draws":session.draws,"transcript_actions":session.actions});
    }
    let bytes = if let Some(p) = &produced {
        atomic(proof_path, p)?;
        p.as_slice()
    } else {
        candidate.as_deref().ok_or("missing-proof")?
    };
    Ok(
        json!({"status":if producer{"proved"}else{"accepted"},"protocol":if s.n.is_some(){"committed-two-factor"}else{"dleq"},
        "mode":if producer{"PUBLIC DEVELOPMENT FIXTURE ONLY"}else{"direct-public-validator"},"repetitions":reps,"preliminary":true,
        "source_sha256":s.source_hash,"descriptor_sha256":s.descriptor_hash,"proof_sha256":hash(bytes),"proof_bytes":bytes.len(),
        "kernel":stats(&samples),"input_admission_including_keys":stats(&admissions),"binding_and_transcript_setup":stats(&setups),"vk_import":stats(&vks),"pk_load_io_and_import":stats(&pks),"trace":last,
        "timing_scope":"kernel includes algorithm, Merlin observations/draws, public wire, proof messages and diagnostic event collection; excludes input admission, binding/transcript initialization, file I/O and CLI/compiler startup; input admission includes VK import and PK I/O/import (nested timings, do not add twice); same key/input values reloaded per sample; no warmup",
        "build":{"debug_assertions":cfg!(debug_assertions),"arch":std::env::consts::ARCH,"os":std::env::consts::OS}}),
    )
}
