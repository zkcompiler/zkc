module

public import Zkc.Construction.ConnectionOutputSelection
public import ZkcSecurity.Bindings.Transcript.RootConnectionReading

@[expose] public section

/-! Exact endpoint transport installed from the actual root certificate.
The entire row is transported before any Boolean observation. Stops, nominal
decoding failures, arbitrary oracle answers and unread proof suffixes use the
existing readExecution and transcript transform, without a new evaluator.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.RootConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript ConnectionRoot ConnectionOutputSelection

attribute [local implicit_reducible] CheckedProtocol.signature

variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Exact full-value transport, including the reached profile history. The
Option records the source encoder's domain, rather than inventing a default. -/
theorem publicReadValues (root : RootCertificate program routing role artifact)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers)
    (query : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      m (Domain.Raw event)) (proof : Domain.Proof model.toCarriers) :
    (fun result => (mapOutcome (fun target => some target.values) result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution query
        (Domain.participant model program routing.context artifact physical) proof =
    (fun result => (mapOutcome (encodedValues program.payload.entry.signature routing.context role)
        result.1, result.2)) <$>
      transform NominalDomain.interface query (publicPresentation root model physical)
        (root.inputs.initial physical).history proof :=
  (publicBridge root replacement profile noLocal model physical).run _ _
    (fun _ _ related => encodedValues_agree related) query proof

/-- A source-selected Boolean is only a consequence of the full installed
bridge. The caller cannot install a weaker acceptance-only return relation. -/
theorem publicReadAcceptance (root : RootCertificate program routing role artifact)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = [])
    (output : Var program.payload.entry.outputs .boolean)
    (visible : inScope role program.payload.entry.outputScopes output = true)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    (query : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      m (Domain.Raw event)) (proof : Domain.Proof model.toCarriers) :
    (fun result => (mapOutcome (fun target => Domain.acceptanceAt
        (scopePosition role program.payload.entry.outputScopes output) target.values) result.1,
        result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution query
        (Domain.participant model program routing.context artifact physical) proof =
    (fun result => (mapOutcome (fun source => source.1.get output) result.1, result.2)) <$>
      transform NominalDomain.interface query (publicPresentation root model physical)
        (root.inputs.initial physical).history proof :=
  (publicBridge root replacement profile noLocal model physical).run _ _
    (fun _ _ related => acceptance_agree output visible related) query proof

/-- Checked endpoint selection fixes both the source output and its physical
position. Neither coordinate is an additional semantic agreement premise. -/
theorem compiledAcceptance_agree {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) {carriers : Carriers}
    {source : Values (Component carriers.Value) compiled.imported.program.payload.entry.outputs ×
      Original.State carriers} {target : Domain.Result carriers}
    (related : Original.CompleteReturns compiled.imported.program.payload.entry.signature
      compiled.selection.context compiled.selection.context.validator art.participant source target) :
    source.1.get compiled.selection.output = compiled.acceptance target := by
  have checked := compiled.checked
  simp only [Selection.check, Bool.and_eq_true, beq_iff_eq] at checked
  have agrees := acceptance_agree compiled.selection.output checked.2.1.2 related
  rw [checked.2.2] at agrees
  have same : Domain.acceptanceAt compiled.selection.position target.values = compiled.acceptance target := rfl
  exact agrees.trans same

/-- Install the actual selected Domain endpoint for every physical row. Input
encoding of a caller's statement remains owned by the existing endpoint ABI. -/
theorem compiledReadAcceptance {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) (routing : Original.Routing)
    (context : routing.context = compiled.selection.context)
    (root : RootCertificate compiled.imported.program routing
      compiled.selection.context.validator art.participant)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers)
    (query : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      m (Domain.Raw event)) (proof : Domain.Proof model.toCarriers) :
    (fun result => (mapOutcome compiled.acceptance result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution query
        (Domain.participant model compiled.imported.program compiled.selection.context
          art.participant physical) proof =
    (fun result => (mapOutcome (fun source => source.1.get compiled.selection.output) result.1,
        result.2)) <$>
      transform NominalDomain.interface query (publicPresentation root model physical)
        (root.inputs.initial physical).history proof := by
  have agrees : ∀ source target,
      Original.CompleteReturns (carriers := model.toCarriers)
        compiled.imported.program.payload.entry.signature routing.context
        compiled.selection.context.validator art.participant source target →
        source.1.get compiled.selection.output = compiled.acceptance target := by
    intro source target related
    rw [context] at related
    exact compiledAcceptance_agree compiled related
  simpa only [context] using
    (publicBridge root replacement profile noLocal model physical).run _ _ agrees query proof

/-- The existing compiled verifier, including statement-encoding refusal.
Successful encoding uses the root's exact ABI history; malformed physical
rows still take the same refusal branch on both sides of the installed bridge. -/
theorem compiledVerifier {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) (routing : Original.Routing)
    (context : routing.context = compiled.selection.context)
    (root : RootCertificate compiled.imported.program routing
      compiled.selection.context.validator art.participant)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (model : DomainModel)
    (query : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      m (Domain.Raw event)) (statement : art.Statement model)
    (initial : Domain.History model.toCarriers) (proof : Domain.Proof model.toCarriers) :
    compiled.verifier model query statement initial proof =
      match Domain.encodeValues statement with
      | none => pure (.stopped .refused, proof)
      | some inputs =>
        let physical := Domain.inputFrame compiled.selection.context inputs initial
        (fun result => (mapOutcome (fun source => source.1.get compiled.selection.output) result.1,
          result.2)) <$>
          transform NominalDomain.interface query (publicPresentation root model physical)
            (root.inputs.initial physical).history proof := by
  rw [ZkcSecurity.Endpoint.Domain.Compiled.verifier_readExecution]
  cases Domain.encodeValues statement with
  | none => rfl
  | some inputs =>
    exact compiledReadAcceptance compiled routing context root replacement profile noLocal
      model (Domain.inputFrame compiled.selection.context inputs initial) query proof

end ZkcSecurity.FiatShamir.RootConnection
