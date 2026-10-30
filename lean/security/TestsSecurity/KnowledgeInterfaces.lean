import ZkcSecurity.Claims.Knowledge
import ZkcSecurity.Bindings.Models.Capabilities
import Lean

/-! A fixed-meaning client sees the actual extraction and oracle interfaces
without importing Sigma justification or endpoint proof methods. -/

#check ZkcSecurity.Claims.KnowledgeRequest.meaning
#check ZkcSecurity.Claims.KnowledgeRequest.typedRun
#check ZkcSecurity.Claims.KnowledgeRequest.bytesRun
#check ZkcSecurity.Claims.ExtractionProfile.extract
#check ZkcSecurity.Endpoint.Extraction.Layout.embed
#check ZkcSecurity.Endpoint.Extraction.replay
#check ZkcSecurity.Endpoint.Sigma.historyOracle
#check ZkcSecurity.Endpoint.TypedProver
#check ZkcSecurity.Endpoint.BytesProver
#check ZkcSecurity.Claims.Domain.Capabilities

run_cmd do
  let environment ← Lean.getEnv
  for imported in environment.header.modules do
    if [
        `ZkcSecurity.Claims.Methods.Knowledge,
        `ZkcSecurity.Claims.Methods.KnowledgeEndpoint,
        `ZkcSecurity.Claims.Methods.Soundness,
        `ZkcSecurity.Transformations.FiatShamir.Knowledge].contains imported.module then
      throwError "fixed knowledge meaning imports a method module: {imported.module}"
  for name in [
      `ZkcSecurity.Claims.SigmaJustification,
      `ZkcSecurity.Claims.knowledgeEndpoint,
      `ZkcSecurity.Endpoint.KnowledgeEvidence,
      `ZkcSecurity.Endpoint.SigmaFamily,
      `ZkcSecurity.Endpoint.Extraction.replay_eq,
      `ZkcSecurity.Endpoint.Sigma.Shape.knowledge_soundness,
      `ZkcSecurity.Endpoint.fixed_soundness] do
    if environment.contains name then
      throwError "fixed knowledge meaning imports a proof method: {name}"
