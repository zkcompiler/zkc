//! Positional test clients for the typed proof execution API.
pub fn execute(
    deployment: &zkc_tools::proof::NativeDeployment,
    input: &serde_json::Value,
    invocation: zkc_tools::proof::Invocation<'_>,
) -> Result<zkc_tools::proof::NativeProofReport, String> {
    let input = zkc_tools::proof::ProofInputs::decode(deployment, input, invocation)?;
    deployment.execute(&input, invocation)
}
pub fn execute_test(
    deployment: &zkc_tools::proof::NativeDeployment,
    input: &serde_json::Value,
    invocation: zkc_tools::proof::Invocation<'_>,
    tapes: std::collections::BTreeMap<usize, Vec<zkc_backends::Scalar>>,
) -> Result<zkc_tools::proof::NativeProofReport, String> {
    let input = zkc_tools::proof::ProofInputs::decode(deployment, input, invocation)?;
    deployment.execute_test(&input, invocation, tapes)
}
