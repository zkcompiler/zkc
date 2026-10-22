//! Positional test clients for the typed proof execution API.
pub fn execute(
    deployment: &zkc::proof::NativeDeployment,
    input: &serde_json::Value,
    invocation: zkc::proof::Invocation<'_>,
) -> Result<zkc::proof::NativeProofReport, String> {
    let input = zkc::proof::ProofInputs::decode(deployment, input, invocation)?;
    deployment.execute(&input, invocation)
}
pub fn execute_test(
    deployment: &zkc::proof::NativeDeployment,
    input: &serde_json::Value,
    invocation: zkc::proof::Invocation<'_>,
    tapes: std::collections::BTreeMap<usize, Vec<zkc_native::Scalar>>,
) -> Result<zkc::proof::NativeProofReport, String> {
    let input = zkc::proof::ProofInputs::decode(deployment, input, invocation)?;
    deployment.execute_test(&input, invocation, tapes)
}
