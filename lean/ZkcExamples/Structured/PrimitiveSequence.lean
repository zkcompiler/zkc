module

public import ZkcExamples.Structured.PrimitiveSequenceViews
public import Zkc.Source.Structured.PrimitiveLaws
public import ZkcExamples.Structured.PrimitiveExpansions

@[expose] public section

/-! The independent arithmetic/vector caller, with its full original closure.
The complete equation includes the actual order of length, addition, append,
division, remainder, subtraction, sum and equality, including early stops. -/
namespace ZkcExamples.Structured.PrimitiveSequence
open Zkc.Source Zkc.Source.Structured
open PrimitiveSequenceViews

-- Local transparency options below elaborate dependent source-view aliases;
-- every resulting equation is still checked by the kernel.
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
set_option smartUnfolding false
set_option linter.unusedSimpArgs false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (xs : List F) (x : F) (divisor : Nat) :
    Values (assignment F G) appendSummaryHelper.inputs :=
  .cons xs (.cons x (.cons divisor .nil))

/-- Ordered eight-result tuple, including the appended scalar and empty vector. -/
def outputs (xs : List F) (x : F) (divisor : Nat) :
    Values (assignment F G) appendSummaryHelper.outputs :=
  let total := (xs ++ [x]).foldl (· + ·) 0
  .cons (xs ++ [x]) (.cons ((xs.length + 1) / divisor)
    (.cons ((xs.length + 1) % divisor) (.cons xs.length
      (.cons total (.cons false (.cons (decide (total = x)) (.cons [] .nil)))))))

/-- Complete logical reference, including representability and division guards. -/
def reference (xs : List F) (x : F) (divisor : Nat) :
    Closed (Values (assignment F G) appendSummaryHelper.outputs) :=
  if xs.length < indexLimit then
    if xs.length + 1 < indexLimit then
      if divisor < indexLimit ∧ divisor ≠ 0 then .done (outputs xs x divisor)
      else .halt .refused
    else .halt .refused
  else .halt .exhausted

set_option backward.isDefEq.respectTransparency false in
set_option smartUnfolding true in
theorem body_equation (table : Meanings F G) (xs : List F) (x : F) (divisor : Nat) :
    appendSummaryBody.denote (meaning F G table) (inputs xs x divisor).get =
      reference xs x divisor := by
  dsimp only [inputs, appendSummaryHelper]
  rw [PrimitiveExpansions.appendSummary_body]
  have extended : xs ≠ xs ++ [x] := by
    intro same
    have lengths := congrArg List.length same
    simp only [List.length_append, List.length_cons, List.length_nil] at lengths
    omega
  by_cases lengthBound : xs.length < indexLimit
  · by_cases addBound : xs.length + 1 < indexLimit
    · by_cases divisorBound : divisor < indexLimit
      · by_cases nonzero : divisor = 0 <;>
          simp [appendSummaryBody, Region.denote, meaning, Evaluation.meaning,
            Evaluation.operation, Operands.eval, Regions.denote, inputs, outputs, reference,
            Values.get_cons, Values.get, Environment.prepend, Environment.push, SiteObservations.closed,
            SiteObservations.silent, PIR.Proc.bind, Primitive.evaluate, primitiveOutcome,
            checkedIndices, lengthBound, addBound, divisorBound, nonzero, extended,
            show 1 < indexLimit by decide +kernel]
      · simp [appendSummaryBody, Region.denote, meaning, Evaluation.meaning,
          Evaluation.operation, Operands.eval, Regions.denote, inputs, reference,
          Values.get_cons, Values.get, Environment.prepend, Environment.push, SiteObservations.closed,
          SiteObservations.silent, PIR.Proc.bind, Primitive.evaluate, primitiveOutcome,
          checkedIndices, lengthBound, addBound, divisorBound, show 1 < indexLimit by decide +kernel]
    · simp [appendSummaryBody, Region.denote, meaning, Evaluation.meaning,
        Evaluation.operation, Operands.eval, Regions.denote, inputs, reference,
        Values.get_cons, Values.get, Environment.prepend, Environment.push, SiteObservations.closed,
        SiteObservations.silent, PIR.Proc.bind, Primitive.evaluate, primitiveOutcome,
        checkedIndices, lengthBound, addBound, show 1 < indexLimit by decide +kernel]
  · simp [appendSummaryBody, Region.denote, meaning, Evaluation.meaning,
      Evaluation.operation, Operands.eval, Regions.denote, inputs, reference,
      Values.get_cons, Values.get, Environment.prepend, Environment.push, SiteObservations.closed,
      SiteObservations.silent, PIR.Proc.bind, Primitive.evaluate, primitiveOutcome, lengthBound]

set_option backward.isDefEq.respectTransparency false in
set_option smartUnfolding false in
theorem helper_equation (xs : List F) (x : F) (divisor : Nat) :
    invoke (program.payload.meanings F G) appendSummaryHelper (inputs xs x divisor) =
      reference xs x divisor :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload appendSummaryDefinition appendSummary_member
    appendSummaryBody appendSummary_exact (inputs xs x divisor)).trans
      (body_equation _ xs x divisor)

set_option backward.isDefEq.respectTransparency false in
set_option smartUnfolding false in
/-- Complete equation for the actual checked original entry, on every logical input. -/
theorem process_equation (xs : List F) (x : F) (divisor : Nat) :
    program.denote F G (inputs xs x divisor) = reference xs x divisor := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs x divisor)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.sequence_entry]
  change (invoke (program.payload.meanings F G) appendSummaryHelper (inputs xs x divisor)).bind _ = _
  rw [helper_equation]
  unfold reference
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Zero division stops after append; the sum, equalities and final empty
constructor cannot rescue the stopped computation. -/
theorem division_zero (xs : List F) (x : F) (bound : xs.length + 1 < indexLimit) :
    program.denote F G (inputs xs x 0) = .halt .refused := by
  rw [process_equation]
  simp [reference, bound, show xs.length < indexLimit by omega]


set_option backward.isDefEq.respectTransparency false in
set_option smartUnfolding true in
/-- An actual original helper prefix retains every reached site and stops before
remainder, subtraction, sum, equality and empty-vector construction. -/
theorem division_zero_sites {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (xs : List F) (x : F)
    (bound : xs.length + 1 < indexLimit) :
    appendSummaryBody.denote (Evaluation.meaning sites table) (inputs xs x 0).get =
      (sites.mark "s0").bind (fun _ =>
      (sites.mark "s2").bind (fun _ =>
      (sites.mark "s3").bind (fun _ =>
      (sites.mark "s5").bind (fun _ =>
      (sites.mark "s7").bind (fun _ => .halt .refused))))) := by
  dsimp only [inputs]
  rw [PrimitiveExpansions.appendSummary_body_observed]
  have lengthBound : xs.length < indexLimit := by omega
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind, Primitive.evaluate, primitiveOutcome,
    checkedIndices, Values.get, lengthBound, bound,
    show 0 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel,
    and_self, ite_true]


set_option backward.isDefEq.respectTransparency false in
/-- The observed complete original includes the wrapper call site as well as
all five reached helper sites. No later source site can occur after refusal. -/
theorem original_division_zero_sites {I : PIR.Signature} (sites : SiteObservations I)
    (xs : List F) (x : F) (bound : xs.length + 1 < indexLimit) :
    Evaluation.payloadDenote (F := F) (G := G) sites program.payload (inputs xs x 0) =
      (sites.mark "s0").bind (fun _ =>
      (sites.mark "s0").bind (fun _ =>
      (sites.mark "s2").bind (fun _ =>
      (sites.mark "s3").bind (fun _ =>
      (sites.mark "s5").bind (fun _ =>
      (sites.mark "s7").bind (fun _ => .halt .refused)))))) := by
  have helper : invoke (Evaluation.payloadMeanings sites program.payload)
      appendSummaryHelper (inputs xs x 0) =
      appendSummaryBody.denote
        (Evaluation.meaning sites (Evaluation.payloadMeanings sites program.payload))
        (inputs xs x 0).get :=
    Evaluation.payload_invoke_body_view (F := F) (G := G) sites
      program.payload appendSummaryDefinition appendSummary_member
      appendSummaryBody appendSummary_exact (inputs xs x 0)
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) sites
    program.payload entryBody entry_exact (inputs xs x 0)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.sequence_entry_observed]
  change (sites.mark "s0").bind (fun _ =>
    (invoke (Evaluation.payloadMeanings sites program.payload) appendSummaryHelper (inputs xs x 0)).bind _) = _
  rw [helper, division_zero_sites sites _ xs x bound]
  simp only [PIR.Proc.bind_assoc]
  rfl

end ZkcExamples.Structured.PrimitiveSequence
