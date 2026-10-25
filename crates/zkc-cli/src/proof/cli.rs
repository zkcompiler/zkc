//! Command-line transport for independently pinned proof bundles.
use super::*;
use crate::execution::{Capacity, InputValue};
use crate::files::read_regular;
use serde_json::{Value as Json, json};
type Result<T> = std::result::Result<T, String>;
const INPUT_LIMIT: usize = 16 * 1024 * 1024;
use crate::files::Outputs;
pub(crate) fn run(
    produce: bool,
    args: &crate::cli::Arguments<'_>,
    cpu: &crate::execution::CpuExecution,
) -> Json {
    let mut report =
        json!({"format":"zkc.native-proof-run/0", "status":"refused", "phase":"arguments"});
    let result = (|| -> Result<()> {
        let deployment_path = args.positional[0];
        let expected_digest =
            crate::files::digest(args.positional[1]).map_err(|_| "native-proof-digest")?;
        let inputs_path = args.positional[2];
        let proof_path = args.positional[3];
        let mut protected = vec![deployment_path, inputs_path];
        let mut authority = None;
        let mut attempts = None;
        let mut capacity = None;
        let mut allow_authored = false;
        for &(name, value) in &args.options {
            match name {
                "--allow-authored" => allow_authored = true,
                "--setups" => {
                    authority = Some(SetupAuthority::parse(&read_regular(
                        value.unwrap(),
                        64 * 1024,
                    )?)?)
                }
                "--attempt-policy" => {
                    attempts = Some(AttemptPolicy::parse(&read_regular(
                        value.unwrap(),
                        64 * 1024,
                    )?)?)
                }
                "--capacity" => {
                    capacity = Some(Capacity::parse(&read_regular(value.unwrap(), 4096)?)?)
                }
                "--threads" => continue, // The command dispatcher owns the CPU context.
                _ => unreachable!("validated proof bundle option"),
            }
            protected.extend(value);
        }
        let output_paths = if produce {
            vec![proof_path]
        } else {
            Vec::new()
        };
        let mut destinations = Outputs::new(&output_paths, &protected)?;
        report["phase"] = json!("admission");
        let deployment_bytes = read_regular(deployment_path, INPUT_LIMIT)?;
        let deployment = NativeDeployment::admit_with_cpu(
            &deployment_bytes,
            &expected_digest,
            authority.unwrap_or_default(),
            cpu.clone(),
        )?
        .with_capacity(capacity.unwrap_or_default())?;
        report["binding_scope"] = json!(match deployment.binding_scope() {
            crate::entry::BindingScope::Transcript => "transcript",
            crate::entry::BindingScope::HeaderOnly => "header",
            crate::entry::BindingScope::Authored => "authored",
        });
        if !deployment.entry().binds_invocation() && !allow_authored {
            return Err("native-proof-binding-policy".into());
        }
        report["capacity"] = deployment.capacity().record();
        report["phase"] = json!("inputs");
        let inputs = ProofInputs::decode_bytes(
            &deployment,
            &read_regular(inputs_path, INPUT_LIMIT)?,
            if let Some(policy) = &attempts {
                Invocation::Attempts(policy)
            } else if produce {
                Invocation::Prove
            } else {
                Invocation::Verify(&[])
            },
        )?;
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
            Some(policy) => {
                deployment.execute(&inputs, crate::proof::Invocation::Attempts(&policy))?
            }
            None => deployment.execute(
                &inputs,
                crate::proof::Invocation::one_shot(proof.as_deref()),
            )?,
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
            crate::files::publication(
                destinations.publish(&[("proof", &bytes)]),
                &mut report,
                true,
            )?;
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
