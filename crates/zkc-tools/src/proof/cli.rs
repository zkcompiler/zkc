//! Command-line transport for independently pinned proof bundles.
use super::*;
use crate::host::publication::Outputs;
pub(crate) fn run(produce: bool, args: &[String]) -> Json {
    let mut report =
        json!({"format":"zkc.native-proof-run/0", "status":"refused", "phase":"admission"});
    let result = (|| -> Result<()> {
        let [
            deployment_path,
            expected_digest,
            inputs_path,
            proof_path,
            options @ ..,
        ] = args
        else {
            return Err("usage: prove-bundle|verify-bundle DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF [--setups=AUTHORITY] [--attempts=POLICY] [--capacity=LIMITS] [--allow-header-only]".into());
        };
        let mut protected = vec![deployment_path.as_str(), inputs_path.as_str()];
        let mut authority = None;
        let mut attempts = None;
        let mut capacity = None;
        let mut allow_header_only = false;
        for option in options {
            if option == "--allow-header-only" && !allow_header_only {
                allow_header_only = true;
                continue;
            }
            if let Some(path) = option
                .strip_prefix("--setups=")
                .filter(|_| authority.is_none())
            {
                authority = Some(SetupAuthority::parse(&read_regular(path, 64 * 1024)?)?);
            } else if let Some(path) = option
                .strip_prefix("--attempts=")
                .filter(|_| produce && attempts.is_none())
            {
                attempts = Some(AttemptPolicy::parse(&read_regular(path, 64 * 1024)?)?);
            } else if let Some(path) = option
                .strip_prefix("--capacity=")
                .filter(|_| capacity.is_none())
            {
                capacity = Some(NativeCapacity::parse(&read_regular(path, 4096)?)?);
            } else {
                return Err("native-proof-option".into());
            }
            protected.push(option.split_once('=').unwrap().1);
        }
        let output_paths = if produce {
            vec![proof_path.as_str()]
        } else {
            Vec::new()
        };
        let mut destinations = Outputs::new(&output_paths, &protected)?;
        let deployment_bytes = read_regular(deployment_path, INPUT_LIMIT)?;
        let expected_digest =
            crate::host::inputs::digest(expected_digest).map_err(|_| "native-proof-digest")?;
        let deployment = NativeDeployment::admit(
            &deployment_bytes,
            &expected_digest,
            authority.unwrap_or_default(),
        )?
        .with_capacity(capacity.unwrap_or_default())?;
        report["binding_scope"] = json!(if deployment.entry().transcript().is_some() {
            "transcript"
        } else {
            "header"
        });
        if deployment.entry().transcript().is_none() && !allow_header_only {
            return Err("native-proof-binding-policy".into());
        }
        report["capacity"] = deployment.capacity().record();
        report["phase"] = json!("inputs");
        let inputs = parse(&read_regular(inputs_path, INPUT_LIMIT)?, INPUT_LIMIT)?;
        let inputs = inputs::decode(&deployment, &inputs, produce)?;
        for input in &inputs.inputs {
            if let InputValue::ProverKeyFile { path, .. } = input {
                destinations.protect([path.as_str()])?;
            }
        }
        let proof = if produce {
            None
        } else {
            Some(read_regular(proof_path, MAX_PROOF_BYTES)?)
        };
        let result = match attempts {
            Some(policy) => deployment.execute_attempts_typed(&inputs, &policy)?,
            None => deployment.execute_typed(&inputs, proof.as_deref())?,
        };
        report["phase"] = json!("execution");
        report
            .as_object_mut()
            .unwrap()
            .extend(result.diagnostics().as_object().unwrap().clone());
        if produce {
            report["proof_bytes"] = json!(result.outcome.as_ref().map_or(0, Vec::len));
        }
        let bytes = result.outcome?;
        if produce {
            report["phase"] = json!("publication");
            destinations.publish(&[("proof", &bytes)], &mut report)?;
        }
        report["phase"] = json!("complete");
        report["status"] = json!(if produce { "produced" } else { "accepted" });
        Ok(())
    })();
    if let Err(error) = result {
        report["code"] = json!(error);
    }
    report
}
