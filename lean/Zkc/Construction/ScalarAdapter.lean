module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Construction.Scalar
public import Zkc.Construction.DomainExecutionLaws

@[expose] public section

/-! A partial ABI adapter for the retained scalar/vector clients.

This module proves representation and calculation equations against the shared
nominal evaluator. It is not an instruction interpreter. Transcript capabilities
are deliberately outside this data adapter: their histories, dynamic occurrences
and handlers need a separate correspondence before the legacy byte claims can
use Domain execution. No equality of those games is assumed here. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.DomainAdapter
open Zkc.Source
variable {F G : Type}

/-- Embed representable legacy operands without erasing nominal domains.
A transcript is a capability, not an operand encoding. -/
def embedData : Value F G → Option (Domain.Value (Structured.uniformCarriers F G))
  | .data (.boolean value) => some (.data (.boolean value))
  | .data (.field domain value) => some (.data (.field domain value))
  | .data (.group domain value) => some (.data (.group domain value))
  | .index value => some (.data (.index value))
  | .vector domain values => some (.data (.vector domain values))
  | .indices coordinates => some (.indices coordinates)
  | .transcript _ | .unsupported => none

/-- Read only the selected legacy ABI out of the nominal value envelope. -/
def readbackData : Domain.Value (Structured.uniformCarriers F G) → Option (Value F G)
  | .data ⟨.boolean, _, value⟩ => some (.data (.boolean value))
  | .data ⟨.field domain, _, value⟩ => some (.data (.field domain value))
  | .data ⟨.group domain, _, value⟩ => some (.data (.group domain value))
  | .data ⟨.index, _, value⟩ => some (.index value)
  | .data ⟨.vector domain, _, values⟩ => some (.vector domain values)
  | .indices coordinates => some (.indices coordinates)
  | _ => none

def embedValues (values : List (Value F G)) :
    Option (Domain.Environment (Structured.uniformCarriers F G)) := values.mapM embedData

theorem embedValues_cons (head : Value F G) (tail : List (Value F G)) :
    embedValues (head :: tail) = (do
      let first ← embedData head
      let rest ← embedValues tail
      pure (first :: rest)) := by
  simp [embedValues, List.mapM_cons]

/-- Successful embedding has an exact inverse; no unsupported value is replaced
by a default datum. -/
theorem readback_embed {value : Value F G}
    {encoded : Domain.Value (Structured.uniformCarriers F G)}
    (ok : embedData value = some encoded) : readbackData encoded = some value := by
  cases value with
  | data payload => cases payload <;> cases ok <;> rfl
  | index | vector | indices => cases ok; rfl
  | transcript | unsupported => cases ok

theorem embed_injective {first second : Value F G}
    {encoded : Domain.Value (Structured.uniformCarriers F G)}
    (one : embedData first = some encoded) (two : embedData second = some encoded) :
    first = second := by
  exact Option.some.inj ((readback_embed one).symm.trans (readback_embed two))

/-- Decoding retains every nominal check and every failed operand decode. -/
theorem decode_embed (ty : Structured.Ty) {value : Value F G}
    {encoded : Domain.Value (Structured.uniformCarriers F G)}
    (ok : embedData value = some encoded) :
    encoded.decode ty = Value.decode ty value := by
  cases value with
  | data payload =>
      cases payload <;> cases ok <;> cases ty <;>
        simp [Domain.Value.decode, Domain.Payload.value, Value.decode, eq_comm]
      all_goals split <;> subst_vars <;> simp_all
  | index | vector =>
      cases ok
      cases ty <;> simp [Domain.Value.decode, Domain.Payload.value, Value.decode, eq_comm]
      all_goals split <;> subst_vars <;> simp_all
  | indices => cases ok; cases ty <;> rfl
  | transcript | unsupported => cases ok

/-- The complete operand tuple commutes, including wrong length and wrong sort. -/
theorem decodeValues_embed (tys : List Structured.Ty) {values : List (Value F G)}
    {encoded : Domain.Environment (Structured.uniformCarriers F G)}
    (ok : embedValues values = some encoded) :
    Domain.decodeValues tys encoded = decodeValues tys values := by
  induction values generalizing tys encoded with
  | nil =>
      simp [embedValues] at ok
      subst encoded
      cases tys <;> rfl
  | cons value values ih =>
      cases head : embedData value with
      | none => simp [embedValues_cons, head] at ok
      | some encodedHead =>
          cases tail : embedValues values with
          | none => simp [embedValues_cons, head, tail] at ok
          | some encodedTail =>
              simp [embedValues_cons, head, tail] at ok
              subst encoded
              cases tys with
              | nil => rfl
              | cons ty tys =>
                  simp only [Domain.decodeValues, decodeValues, decode_embed ty head, ih tys tail]

theorem encode_embed (ty : Structured.Ty) (data : dataType ty = true)
    (value : Structured.assignment F G ty) :
    embedData (Value.encode ty value) = Domain.Value.encode ty value := by
  cases ty <;> simp_all [dataType, Value.encode, embedData, Domain.Value.encode,
    Domain.Payload.ofValue, Structured.Ty.isHandle]

theorem encodeValues_embed {tys : List Structured.Ty}
    (values : Values (Structured.assignment F G) tys) (data : tys.all dataType = true) :
    embedValues (encodeValues values) = Domain.encodeValues values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at data
      simp only [encodeValues, embedValues_cons, encode_embed _ data.1,
        ih data.2, Domain.encodeValues]

/-- Preserve stopped calculations exactly. An unrepresentable returned tuple
is refused by this partial ABI, rather than silently projected. -/
def embedOutcome : PIR.Outcome (List (Value F G)) →
    PIR.Outcome (Domain.Environment (Structured.uniformCarriers F G))
  | .stopped reason => .stopped reason
  | .returned values =>
      match embedValues values with
      | some encoded => .returned encoded
      | none => .stopped .refused

section Execution
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A uniform calculation is the same typed nominal operation under every
observation interface and helper table. There is no second arithmetic meaning. -/
theorem operationOn_calculation {I : PIR.Signature}
    (observations : Structured.SiteObservations I)
    (table : Structured.Evaluation.Meanings F G I) (calculation : Calculation)
    (arguments : Values (Structured.assignment F G) calculation.op.arguments)
    (bodies : Values (RegionFunction (Structured.assignment F G) I) calculation.op.regions) :
    Structured.Evaluation.operationOn (Structured.ringModel F G) observations table
        calculation.op arguments bodies = ofOutcome (calculation.evaluate arguments) := by
  rw [← Structured.Evaluation.operation_eq_operationOn]
  exact Calculation.operation_eq observations table calculation arguments bodies

/-- The actual Domain calculation runner, including malformed operand refusal,
commutes with the legacy operand adapter on the declared scalar/vector results.
The restriction is structural eligibility, never a relation-validity premise. -/
theorem calculate_embed (calculation : Calculation)
    (resultsData : calculation.op.results.all dataType = true)
    {values : List (Value F G)}
    {encoded : Domain.Environment (Structured.uniformCarriers F G)}
    (ok : embedValues values = some encoded) :
    Domain.calculate (Structured.ringModel F G) calculation encoded =
      embedOutcome (Zkc.Construction.calculate calculation values) := by
  have closed (result : PIR.Outcome (Values (Structured.assignment F G) calculation.op.results)) :
      Domain.closedOutcome (ofOutcome result) = result := by cases result <;> rfl
  simp only [Domain.calculate, decodeValues_embed _ ok, Zkc.Construction.calculate,
    operationOn_calculation, closed]
  cases decoded : decodeValues calculation.op.arguments values with
  | none => rfl
  | some arguments =>
      cases calculated : calculation.evaluate arguments with
      | stopped reason => simp only [calculated, embedOutcome]
      | returned results =>
          simp only [calculated, embedOutcome, encodeValues_embed results resultsData]
          cases Domain.encodeValues results <;> rfl

/-- The scalar source helper table is the actual admitted Domain table. -/
theorem helperTable_eq (program : Structured.Program) :
    Domain.helperTable (Structured.ringModel F G) program =
      program.payload.definitions.foldl
        (Structured.Evaluation.extendMeanings (F := F) (G := G)
          Structured.SiteObservations.closed) [] := by
  have extend : Structured.Evaluation.extendMeanings (F := F) (G := G)
      Structured.SiteObservations.closed =
      Structured.Evaluation.extendMeaningsOn (Structured.ringModel F G)
        Structured.SiteObservations.closed :=
    funext fun table => funext
      (Structured.Evaluation.extendMeanings_eq_extendMeaningsOn _ table)
  simp only [Domain.helperTable, extend]

/-- Exact checked helper output metadata is required by the canonical runner.
The premise concerns the actual admitted helper signature and scalar ABI, not
relation validity or a proposed execution equality. Wrong argument sorts still
refuse through the same partial decoder on both sides. -/
theorem callHelper_checked_signature (program : Structured.Program) (name : String) (declared : List ValueSort)
    (signature : ∀ entry : Structured.HelperDefinition (Structured.assignment F G) Structured.closedInterface,
      (Domain.helperTable (Structured.ringModel F G) program).find? (fun found => found.helper.name == name) =
        some entry → entry.helper.outputs.map ValueSort.data = declared ∧
          entry.helper.outputs.all dataType = true)
    {values : List (Value F G)} {encoded : Domain.Environment (Structured.uniformCarriers F G)}
    (ok : embedValues values = some encoded) :
    Domain.callHelper (Structured.ringModel F G) program name declared encoded =
      embedOutcome (Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name values) := by
  have closed {A : Type} (process : PIR.Process Structured.closedInterface A) :
      Domain.closedOutcome process = Construction.closedOutcome process := by
    cases process with
    | done | halt => rfl
    | call operation => exact operation.elim
  unfold Domain.callHelper Construction.callHelper
  cases found : (Domain.helperTable (Structured.ringModel F G) program).find?
      (fun entry => entry.helper.name == name) with
  | none => rfl
  | some entry =>
      obtain ⟨declares, eligible⟩ := signature entry found
      simp only [declares, ite_true, decodeValues_embed _ ok, closed]
      cases decoded : decodeValues entry.helper.inputs values with
      | none => rfl
      | some arguments =>
          cases result : Construction.closedOutcome (entry.invoke arguments) with
          | stopped reason => simp only [result, embedOutcome]
          | returned returned =>
              simp only [result, embedOutcome, encodeValues_embed returned eligible]
              cases Domain.encodeValues returned <;> rfl

end Execution
end Zkc.Construction.Uniform.DomainAdapter

-- Own generated equations here, before independent clients request them.
-- Their proofs remain kernel checked and retain a single stored provider.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Uniform.DomainAdapter.readbackData
