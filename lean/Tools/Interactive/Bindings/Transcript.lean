import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Transcript

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let args := binding.arguments
  let observing := binding.contract.startsWith "transcript.observe."
  let observingKind := (binding.contract.drop "transcript.observe.".length).toString
  let t :: _ := args | throw "binding-static-arity"
  ensure (transcriptDomain t) "binding-static-arguments"
  let field ← associatedIdentity t "ChallengeField"
  let group := if field == fr then g1 else ristrettoGroup
  if observing then
    let identity := if domainIndependent observingKind then "" else args[1]?.getD ""
    let expected := if domainIndependent observingKind then [t, codec observingKind identity]
      else [t, identity, codec observingKind identity]
    ensure (args == expected && logicalIdentity observingKind identity) "binding-static-arguments"
    let payloadField := if ["group", "groups"].contains observingKind then
        (associatedIdentity identity "Scalar").toOption.getD ""
      else if ["commitment", "commitments", "proof"].contains observingKind then (associatedIdentity identity "ValueField").toOption.getD "" else identity
    -- Codec-valid logical observation is independent of the challenge field.
    -- The current concrete providers support only these payload combinations.
    if physical || !binding.implementation.isEmpty then
      ensure (domainIndependent observingKind || payloadField == field || (t == extensionTranscript && payloadField == koalaBear)) "binding-static-arguments"
  else ensure (args == [t]) "binding-static-arguments"
  if binding.contract == "transcript.draw_index" then
    ensure (t == extensionTranscript) "binding-index-transcript"
  let logical := Support.signature shape field group t
  let logical := if observing then
      { logical with inputs := [Support.typed "transcript" field group t,
        ValueType.mk observingKind (if domainIndependent observingKind then "" else args[1]?.getD "")] }
    else logical
  let backend := if t == spongefishTranscript then "spongefish/" else Support.scalarBackend field
  Support.realize physical binding logical backend

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "transcript.draw_index" ["transcript", "index"] ["index", "transcript"] resolve,
    Operation.ofShape "transcript.challenge" ["transcript"] ["field", "transcript"] resolve] ++ serializableKinds.map (fun kind =>
    Operation.ofShape ("transcript.observe." ++ kind) ["transcript", kind] ["transcript"] resolve)⟩
  (fun contract => Support.implementations ["arkworks", "dalek", "plonky3", "spongefish"] contract)

end Tools.Interactive.Bindings.Transcript
