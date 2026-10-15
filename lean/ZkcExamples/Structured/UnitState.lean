module

public import ZkcExamples.Structured.UnitStateData
public import Zkc.Source.Structured.Laws

@[expose] public section

/-! Universal equations for the retained native export, including its stopping
zero-state callback. Scalar interpretation and vector admission are explicit;
the resulting equality is of complete imported logical processes. -/

namespace ZkcExamples.Structured.UnitState
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
-- Rewriting dependent callback types needs the resolved operation signatures.
set_option backward.isDefEq.respectTransparency false

/-- The program is computed by admission of the actual exported constructor data. -/
def program : Program := (check UnitStateData.snapshot).toOption.get (by decide +kernel)

theorem admitted : check UnitStateData.snapshot = .ok program := by rfl

def imported : Imported UnitStateData.snapshot := ⟨program, admitted⟩

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev vector : Ty := .vector "bls12-381.fr"

private abbrev foldSpec : FoldSpec :=
  ⟨⟨"items", [vector], "bls12-381.fr", .here, false⟩,
    [], [.boolean], "step", "predicate"⟩

private def stepBody : Region dialect [scalar, vector, .boolean] [] := .stop .abort

private def predicateBody : Region dialect [scalar, vector, .boolean] [.boolean] :=
  .ret (.cons (.there (.there .here)) .nil)

private abbrev foldHelper : Helper := ⟨"fold", [vector, .boolean], []⟩
private abbrev workHelper : Helper := ⟨"work", [vector, .boolean], [.boolean]⟩

private def foldBody : Region dialect [vector, .boolean] [] :=
  .letOp (.fold foldSpec) (.cons .here (.cons (.there .here) .nil)) .nil (.ret .nil)

private def workBody : Region dialect [vector, .boolean] [.boolean] :=
  .letOp (.invoke foldHelper) (.cons .here (.cons (.there .here) .nil))
    .nil (.ret (.cons (.there .here) .nil))

private def mainBody : Region dialect [vector, .boolean] [.boolean] :=
  .letOp (.invoke workHelper) (.cons .here (.cons (.there .here) .nil))
    .nil (.ret (.cons .here .nil))

variable {F : Type} [CommRing F] [DecidableEq F]

private def stepHelpers : Meanings F :=
  [⟨foldSpec.stepHelper, fun args => stepBody.denote (meaning F []) args.get⟩]

private def helpers : Meanings F :=
  ⟨foldSpec.predicateHelper,
    fun args => predicateBody.denote (meaning F stepHelpers) args.get⟩ :: stepHelpers

private def foldHelpers : Meanings F :=
  ⟨foldHelper, fun args => foldBody.denote (meaning F helpers) args.get⟩ :: helpers

private def workHelpers : Meanings F :=
  ⟨workHelper, fun args => workBody.denote (meaning F foldHelpers) args.get⟩ :: foldHelpers

def inputs (xs : List F) (enabled : Bool) :
    Values (scalarAssignment F) [.vector "bls12-381.fr", .boolean] :=
  .cons xs (.cons enabled .nil)

def outputs (enabled : Bool) : Values (scalarAssignment F) [.boolean] :=
  .cons enabled .nil

def process (xs : List F) (enabled : Bool) := program.denote F (inputs xs enabled)

private theorem process_fold (xs : List F) (enabled : Bool) :
    process xs enabled =
      (denoteFold helpers foldSpec (inputs xs enabled)).bind
        (fun _ => .done (outputs enabled)) := by
  change mainBody.denote (meaning F workHelpers) (inputs xs enabled).get = _
  simp [mainBody, workBody, foldBody, workHelpers, foldHelpers, invoke,
    Region.denote, Regions.denote, meaning, operation, inputs, outputs,
    Operands.eval, Values.get, Environment.prepend, Environment.push, PIR.Proc.bind_assoc,
    PIR.Proc.bind]
  rfl

private theorem transition (xs : List F) (enabled : Bool) (item : F)
    (state : Values (scalarAssignment F) []) :
    foldTransition helpers foldSpec (.cons xs .nil) (.cons enabled .nil) state item =
      if enabled then .halt .abort else .done state := by
  cases state
  cases enabled <;> rfl

/-- A zero-state callback still stops; the caller's Boolean is returned only
when the vector is empty or the predicate disables every step. -/
def reference (xs : List F) (enabled : Bool) :
    Closed (Values (scalarAssignment F) program.payload.entry.outputs) :=
  if enabled && !xs.isEmpty then .halt .abort else .done (outputs enabled)

/-- Complete process equality, including the abort that bypasses the return. -/
theorem process_eq_reference (xs : List F) (enabled : Bool)
    (lengthValid : xs.length < indexLimit) :
    process xs enabled = reference xs enabled := by
  rw [process_fold]
  change (denoteFold helpers foldSpec
    ((Values.cons xs Values.nil).append
      (Values.nil.append (Values.cons enabled Values.nil)))).bind _ = _
  rw [denoteFold_pack]
  have domainAdmitted :
      (foldSpec.domain.denote (.cons xs (.nil : Values (scalarAssignment F) []))).admit =
        .returned xs := by
    simp [foldSpec, DomainSpec.denote, Finite.Domain.admit, Values.get, lengthValid]
  simp only [Finite.execute, domainAdmitted, Finite.admitThen]
  cases enabled with
  | false =>
    rw [Finite.fold_total _ (fun state _ => state) (fun state item => transition xs false item state)]
    simp [reference, PIR.Proc.bind]
  | true =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      rw [Finite.fold, transition]
      rfl

/-- Domain failure precedes the predicate, including when it would disable every step. -/
theorem process_refuses (xs : List F) (enabled : Bool)
    (lengthInvalid : ¬ xs.length < indexLimit) :
    process xs enabled = .halt .refused := by
  rw [process_fold]
  change (denoteFold helpers foldSpec
    ((Values.cons xs Values.nil).append
      (Values.nil.append (Values.cons enabled Values.nil)))).bind _ = _
  rw [denoteFold_pack]
  simp [Finite.execute, DomainSpec.denote, foldSpec, Values.get, Finite.Domain.admit,
    lengthInvalid, Finite.admitThen, PIR.Proc.bind]

theorem process_eq_checked_reference (xs : List F) (enabled : Bool) :
    process xs enabled =
      if xs.length < indexLimit then reference xs enabled else .halt .refused := by
  split
  · exact process_eq_reference xs enabled ‹_›
  · exact process_refuses xs enabled ‹_›

theorem process_nil (enabled : Bool) :
    process ([] : List F) enabled = .done (outputs enabled) := by
  simpa [reference] using
    process_eq_reference ([] : List F) enabled (by change 0 < indexLimit; decide +kernel)

theorem process_disabled (xs : List F) (lengthValid : xs.length < indexLimit) :
    process xs false = .done (outputs false) := by
  simpa [reference] using process_eq_reference xs false lengthValid

theorem process_enabled_cons (x : F) (xs : List F)
    (lengthValid : (x :: xs).length < indexLimit) :
    process (x :: xs) true = .halt .abort := by
  simpa [reference] using process_eq_reference (x :: xs) true lengthValid

theorem process_aborts_iff (xs : List F) (enabled : Bool)
    (lengthValid : xs.length < indexLimit) :
    process xs enabled = .halt .abort ↔ enabled = true ∧ xs ≠ [] := by
  rw [process_eq_reference xs enabled lengthValid]
  cases enabled <;> cases xs <;> simp [reference]

theorem process_singleton (x : F) (enabled : Bool) :
    process [x] enabled = if enabled then .halt .abort else .done (outputs enabled) := by
  simpa [reference] using
    process_eq_reference [x] enabled (by change 1 < indexLimit; decide +kernel)

theorem process_pair (x y : F) (enabled : Bool) :
    process [x, y] enabled = if enabled then .halt .abort else .done (outputs enabled) := by
  simpa [reference] using
    process_eq_reference [x, y] enabled (by change 2 < indexLimit; decide +kernel)

theorem exact_subject : imported.program.snapshot = UnitStateData.snapshot :=
  imported.exactSubject

theorem imported_eq_reference (xs : List F) (enabled : Bool)
    (lengthValid : xs.length < indexLimit) :
    imported.program.denote F (inputs xs enabled) = reference xs enabled :=
  process_eq_reference xs enabled lengthValid

end ZkcExamples.Structured.UnitState
