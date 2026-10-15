module

public import ZkcExamples.Structured.UnitStateData
public import Zkc.Source.Structured.Linking

@[expose] public section

/-! Universal equations for the retained native export, including its stopping
zero-state callback. Scalar interpretation and vector admission are explicit;
the resulting equality is of complete imported logical processes. -/

namespace ZkcExamples.Structured.UnitState
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

private def stepDefinition : CheckedDefinition :=
  (program.payload.definitions.find? fun definition => definition.name == "step").get
    (by decide +kernel)

private def predicateDefinition : CheckedDefinition :=
  (program.payload.definitions.find? fun definition => definition.name == "predicate").get
    (by decide +kernel)

private def foldDefinition : CheckedDefinition :=
  (program.payload.definitions.find? fun definition => definition.name == "fold").get
    (by decide +kernel)

private def workDefinition : CheckedDefinition :=
  (program.payload.definitions.find? fun definition => definition.name == "work").get
    (by decide +kernel)

variable {F : Type} [CommRing F] [DecidableEq F]

private def table : Meanings F := program.payload.meanings F

def inputs (xs : List F) (enabled : Bool) :
    Values (scalarAssignment F) [.vector "bls12-381.fr", .boolean] :=
  .cons xs (.cons enabled .nil)

def outputs (enabled : Bool) : Values (scalarAssignment F) [.boolean] :=
  .cons enabled .nil

/-- Each invocation is justified by the named checked declaration's raw body.
The complete table is shared by all equations; callers use only these contracts. -/
private theorem invoke_step (xs : List F) (enabled : Bool) (item : F) :
    invoke table foldSpec.stepHelper (.cons item (.cons xs (.cons enabled .nil))) =
      .halt .abort :=
  program.payload.invoke_body_view stepDefinition (List.get_find?_mem _)
    stepBody (by rfl) (.cons item (.cons xs (.cons enabled .nil)))

private theorem invoke_predicate (xs : List F) (enabled : Bool) (item : F) :
    invoke table foldSpec.predicateHelper (.cons item (.cons xs (.cons enabled .nil))) =
      .done (outputs enabled) :=
  program.payload.invoke_body_view predicateDefinition (List.get_find?_mem _)
    predicateBody (by rfl) (.cons item (.cons xs (.cons enabled .nil)))

private theorem invoke_fold (xs : List F) (enabled : Bool) :
    invoke table foldHelper (inputs xs enabled) =
      denoteFold table foldSpec (inputs xs enabled) := by
  have bodyLaw : foldBody.denote (meaning F table) (inputs xs enabled).get =
      denoteFold table foldSpec (inputs xs enabled) := by
    simp only [foldBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
      Values.get, operation]
    trans (denoteFold table foldSpec (inputs xs enabled)).bind .done
    · congr 1
      funext result
      cases result
      rfl
    · exact PIR.Proc.bind_done _
  exact (program.payload.invoke_body_view foldDefinition (List.get_find?_mem _)
    foldBody (by rfl) (inputs xs enabled)).trans bodyLaw

private theorem invoke_work (xs : List F) (enabled : Bool) :
    invoke table workHelper (inputs xs enabled) =
      (denoteFold table foldSpec (inputs xs enabled)).bind
        (fun _ => .done (outputs enabled)) := by
  have bodyLaw : workBody.denote (meaning F table) (inputs xs enabled).get =
      (invoke table foldHelper (inputs xs enabled)).bind
        (fun _ => .done (outputs enabled)) := by
    simp only [workBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
      Values.get, operation]
    dsimp only [Op.results, Values.get, Environment.prepend, Environment.push]
    congr 1
    funext result
    cases result
    rfl
  exact (program.payload.invoke_body_view workDefinition (List.get_find?_mem _)
    workBody (by rfl) (inputs xs enabled)).trans (bodyLaw.trans
      (congrArg (fun action : Closed (Values (scalarAssignment F) []) =>
        action.bind fun _ => .done (outputs enabled)) (invoke_fold xs enabled)))

def process (xs : List F) (enabled : Bool) :
    Closed (Values (scalarAssignment F) [.boolean]) :=
  program.denote F (inputs xs enabled)

private theorem process_fold (xs : List F) (enabled : Bool) :
    process xs enabled =
      (denoteFold table foldSpec (inputs xs enabled)).bind
        (fun _ => .done (outputs enabled)) := by
  have bodyLaw : mainBody.denote (meaning F table) (inputs xs enabled).get =
      invoke table workHelper (inputs xs enabled) := by
    simp only [mainBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
      Values.get, operation]
    trans (invoke table workHelper (inputs xs enabled)).bind .done
    · congr 1
      funext result
      cases result with
      | cons enabled rest => cases rest; rfl
    · exact PIR.Proc.bind_done _
  exact (program.payload.denote_body_view mainBody (by rfl) (inputs xs enabled)).trans
    (bodyLaw.trans (invoke_work xs enabled))

private theorem transition (xs : List F) (enabled : Bool) (item : F)
    (state : Values (scalarAssignment F) []) :
    foldTransition table foldSpec (.cons xs .nil) (.cons enabled .nil) state item =
      if enabled then .halt .abort else .done state := by
  cases state
  cases enabled with
  | false =>
    exact foldTransition_false table foldSpec (by rfl) (.cons xs .nil)
      (.cons false .nil) .nil item (invoke_predicate xs false item)
  | true =>
    exact (foldTransition_true table foldSpec (by rfl) (.cons xs .nil)
      (.cons true .nil) .nil item (invoke_predicate xs true item)).trans
      (invoke_step xs true item)

/-- A zero-state callback still stops; the caller's Boolean is returned only
when the vector is empty or the predicate disables every step. -/
def reference (xs : List F) (enabled : Bool) :
    Closed (Values (scalarAssignment F) [.boolean]) :=
  if enabled && !xs.isEmpty then .halt .abort else .done (outputs enabled)

/-- Complete process equality, including the abort that bypasses the return. -/
theorem process_eq_reference (xs : List F) (enabled : Bool)
    (lengthValid : xs.length < indexLimit) :
    process xs enabled = reference xs enabled := by
  rw [process_fold]
  change (denoteFold table foldSpec
    ((Values.cons xs Values.nil).append
      (Values.nil.append (Values.cons enabled Values.nil)))).bind _ = _
  rw [denoteFold_pack]
  have domainAdmitted :
      (foldSpec.domain.denote (.cons xs (.nil : Values (scalarAssignment F) []))).admit =
        .returned xs := by
    simp [foldSpec, DomainSpec.denote, Finite.Domain.admit, Values.get, lengthValid]
  simp only [Finite.execute, domainAdmitted, Finite.admitThen]
  dsimp only [DomainSpec.item, scalarAssignment]
  cases enabled with
  | false =>
    rw [Finite.fold_total _ (fun state _ => state) (fun state item => transition xs false item state)]
    simp [reference, PIR.Proc.bind]
  | true =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      dsimp only [Finite.fold]
      rw [transition]
      rfl

/-- Domain failure precedes the predicate, including when it would disable every step. -/
theorem process_refuses (xs : List F) (enabled : Bool)
    (lengthInvalid : ¬ xs.length < indexLimit) :
    process xs enabled = .halt .refused := by
  rw [process_fold]
  change (denoteFold table foldSpec
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
