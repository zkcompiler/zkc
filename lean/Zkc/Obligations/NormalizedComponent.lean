module

public import Zkc.Obligations.Component
public import Zkc.Semantics.StateInterpretation
public import Zkc.Source.Structured.NormalForm.Observation

@[expose] public section

/-! Transport an assembled property from the connection's occurrence-preserving
normal form to its actual typed source body. Installed helper/callee equations
are the normalizer's existing contracts; no whole-source equation or separate
Process evaluator is an author obligation. Every typed reply, stop and output
component is covered by the same normalization theorem. -/

set_option autoImplicit false
namespace Zkc.Obligations.NormalizedComponent
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Transcript

def ofOccurrence {model : DomainModel}
    {tables : Tables model (Occurrence.signature model.toCarriers)}
    {protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers)}
    {context : ProtocolContext} (signature : Signature)
    {Γ out : List Ty} (body : Region protocolDialect Γ out) (role roster : Nat)
    (pattern : InputPattern Γ) (form : Form signature.laws signature.callees pattern.scope out)
    (normalized : normalize signature body role roster pattern = .ok form)
    (matched : form.CallsMatch) (distinct : RosterDistinct context role roster)
    (results : LawResults model signature.laws)
    (processes : CalleeProcesses model signature.callees (Occurrence.signature model.toCarriers))
    (binders : Binders model pattern.scope)
    (laws : LawsHold tables results (pattern.environment model binders))
    (callees : CalleesHold protocols processes (pattern.environment model binders))
    {E P : Type} {Raw : E → Type}
    {absorb : Interface (Occurrence.signature model.toCarriers) E P Raw}
    {escape : EscapeJudgment E Raw}
    {post : List E → Values (Component model.Value) out → Prop} {history : List E}
    (assembled : Derivation absorb escape post history
      (form.denoteOn model Occurrence.actions tables results context
        (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes binders)) :
    Derivation absorb escape post history
      (body.denote (participantMeaningWithOn model (.silent _) Occurrence.actions tables
        (context.roles role) protocols context Occurrence.iterations) (pattern.environment model binders).get) :=
  assembled.transport (normalize_occurrence_sound signature body role roster pattern form normalized matched
    distinct results processes binders laws callees)

/-- The same normalization through an installed stateful operation reading.
For security this is `SourceReading.Interpretation.operations`, and the state
contains the actual occurrence stack/history. This is interpretation transport,
not another source evaluator or a request-specific whole-source equation. -/
def ofOccurrenceState {model : DomainModel}
    {tables : Tables model (Occurrence.signature model.toCarriers)}
    {protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers)}
    {context : ProtocolContext} (signature : Signature)
    {Γ out : List Ty} (body : Region protocolDialect Γ out) (role roster : Nat)
    (pattern : InputPattern Γ) (form : Form signature.laws signature.callees pattern.scope out)
    (normalized : normalize signature body role roster pattern = .ok form)
    (matched : form.CallsMatch) (distinct : RosterDistinct context role roster)
    (results : LawResults model signature.laws)
    (processes : CalleeProcesses model signature.callees (Occurrence.signature model.toCarriers))
    (binders : Binders model pattern.scope)
    (laws : LawsHold tables results (pattern.environment model binders))
    (callees : CalleesHold protocols processes (pattern.environment model binders))
    {I : PIR.Signature} {S E P : Type} {Raw : E → Type}
    (operations : PIR.StateOperationInterpretation (Occurrence.signature model.toCarriers) I S)
    (state : S) {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
    {post : List E → Values (Component model.Value) out × S → Prop} {history : List E}
    (assembled : Derivation absorb escape post history
      ((form.denoteOn model Occurrence.actions tables results context
        (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role)
        processes binders).interpretState operations state)) :
    Derivation absorb escape post history
      ((body.denote (participantMeaningWithOn model (.silent _) Occurrence.actions tables
        (context.roles role) protocols context Occurrence.iterations)
        (pattern.environment model binders).get).interpretState operations state) :=
  assembled.transport (congrArg (fun process => process.interpretState operations state)
    (normalize_occurrence_sound signature body role roster pattern form normalized matched
      distinct results processes binders laws callees))

end Zkc.Obligations.NormalizedComponent
