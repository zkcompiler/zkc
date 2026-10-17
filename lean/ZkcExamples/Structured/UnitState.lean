module

public import ZkcExamples.Structured.UnitStateData
public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.ClosedProfile

@[expose] public section

/-! Universal equations for the retained native export, including its stopping
zero-state callback. Scalar interpretation and vector admission are explicit;
the resulting equality is of complete imported logical processes. -/

namespace ZkcExamples.Structured.UnitState
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The program is computed by admission of the exact exported constructor data. -/
def program : ClosedProgram := (checkClosed UnitStateData.snapshot).toOption.get (by decide +kernel)

theorem admitted : checkClosed UnitStateData.snapshot = .ok program := by
  have accepted : (checkClosed UnitStateData.snapshot).toOption.isSome = true := by decide +kernel
  cases checked : checkClosed UnitStateData.snapshot with
  | error code => simp [checked, Except.toOption] at accepted
  | ok value => simp [program, checked, Except.toOption]

def imported : ClosedImported UnitStateData.snapshot := ⟨program, admitted⟩

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev vector : Ty := .vector "bls12-381.fr"

private abbrev foldSpec : FoldSpec :=
  ⟨⟨"items", [vector], "bls12-381.fr", .here, false⟩,
    [], [.boolean], "step", "predicate", .local⟩

private def stepBody : Region dialect [scalar, vector, .boolean] [] :=
  .letOp (.mark "body_stop") .nil .nil (.stop .abort)

private def predicateBody : Region dialect [scalar, vector, .boolean] [.boolean] :=
  .ret (.cons (.there (.there .here)) .nil)

private abbrev foldHelper : Helper := ⟨"fold", .local, [vector, .boolean], []⟩
private abbrev workHelper : Helper := ⟨"work", .local, [vector, .boolean], [.boolean]⟩

private def foldBody : Region dialect [vector, .boolean] [] :=
  .letOp (.fold foldSpec) (.cons .here (.cons (.there .here) .nil)) .nil (.ret .nil)

private def workBody : Region dialect [vector, .boolean] [.boolean] :=
  .letOp (.mark "fold") .nil .nil <|
  .letOp (.invoke foldHelper) (.cons .here (.cons (.there .here) .nil))
    .nil (.ret (.cons (.there .here) .nil))

private def mainBody : Region dialect [vector, .boolean] [.boolean] :=
  .letOp (.mark "work") .nil .nil <|
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

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

variable (F G) in
private def table : Meanings F G := program.payload.meanings F G

def inputs (xs : List F) (enabled : Bool) :
    Values (assignment F G) [.vector "bls12-381.fr", .boolean] :=
  .cons xs (.cons enabled .nil)

def outputs (enabled : Bool) : Values (assignment F G) [.boolean] :=
  .cons enabled .nil

-- Direct reduction avoids expanding the dependent admission equations.
set_option smartUnfolding false in
/-- Each invocation is justified by the named checked declaration's raw body.
The complete table is shared by all equations; callers use only these contracts. -/
private theorem invoke_step (xs : List F) (enabled : Bool) (item : F) :
    invoke (table F G) foldSpec.stepHelper (.cons item (.cons xs (.cons enabled .nil))) =
      .halt .abort :=
  Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload stepDefinition (List.get_find?_mem _)
    stepBody (by rfl) (.cons item (.cons xs (.cons enabled .nil)))

set_option smartUnfolding false in
private theorem invoke_predicate (xs : List F) (enabled : Bool) (item : F) :
    invoke (table F G) foldSpec.predicateHelper (.cons item (.cons xs (.cons enabled .nil))) =
      .done (outputs enabled) :=
  Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload predicateDefinition (List.get_find?_mem _)
    predicateBody (by rfl) (.cons item (.cons xs (.cons enabled .nil)))

set_option smartUnfolding false in
private theorem invoke_fold (xs : List F) (enabled : Bool) :
    invoke (table F G) foldHelper (inputs xs enabled) =
      Evaluation.denoteFold (table F G) foldSpec (inputs xs enabled) := by
  have bodyLaw : foldBody.denote (meaning F G (table F G)) (inputs xs enabled).get =
      Evaluation.denoteFold (table F G) foldSpec (inputs xs enabled) := by
    set_option smartUnfolding true in
      simp only [foldBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
        Values.get, Evaluation.meaning, Evaluation.operation, SiteObservations.closed, SiteObservations.silent]
    trans (Evaluation.denoteFold (table F G) foldSpec (inputs xs enabled)).bind .done
    · congr 1
      funext result
      cases result
      rfl
    · exact PIR.Proc.bind_done _
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload foldDefinition (List.get_find?_mem _)
    foldBody (by rfl) (inputs xs enabled)).trans bodyLaw

set_option smartUnfolding false in
private theorem invoke_work (xs : List F) (enabled : Bool) :
    invoke (table F G) workHelper (inputs xs enabled) =
      (Evaluation.denoteFold (table F G) foldSpec (inputs xs enabled)).bind
        (fun _ => .done (outputs enabled)) := by
  have bodyLaw : workBody.denote (meaning F G (table F G)) (inputs xs enabled).get =
      (invoke (table F G) foldHelper (inputs xs enabled)).bind
        (fun _ => .done (outputs enabled)) := by
    set_option smartUnfolding true in
      simp only [workBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
        Values.get, Evaluation.meaning, Evaluation.operation,
        SiteObservations.closed, SiteObservations.silent, PIR.Proc.bind, Environment.prepend]
    dsimp only [Op.results, Values.get, Environment.prepend, Environment.push]
    congr 1
    funext result
    cases result
    rfl
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload workDefinition (List.get_find?_mem _)
    workBody (by rfl) (inputs xs enabled)).trans (bodyLaw.trans
      (congrArg (fun action : Closed (Values (assignment F G) []) =>
        action.bind fun _ => .done (outputs enabled)) (invoke_fold xs enabled)))

set_option smartUnfolding false in
def process (xs : List F) (enabled : Bool) :
    Closed (Values (assignment F G) [.boolean]) :=
  program.denote F G (inputs xs enabled)

set_option smartUnfolding false in
private theorem process_fold (xs : List F) (enabled : Bool) :
    process (G := G) xs enabled =
      (Evaluation.denoteFold (table F G) foldSpec (inputs xs enabled)).bind
        (fun _ => .done (outputs enabled)) := by
  have bodyLaw : mainBody.denote (meaning F G (table F G)) (inputs xs enabled).get =
      invoke (table F G) workHelper (inputs xs enabled) := by
    set_option smartUnfolding true in
      simp only [mainBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
        Values.get, Evaluation.meaning, Evaluation.operation,
        SiteObservations.closed, SiteObservations.silent, PIR.Proc.bind, Environment.prepend]
    trans (invoke (table F G) workHelper (inputs xs enabled)).bind .done
    · congr 1
      funext result
      cases result with
      | cons enabled rest => cases rest; rfl
    · exact PIR.Proc.bind_done _
  exact (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload mainBody (by rfl) (inputs xs enabled)).trans
    (bodyLaw.trans (invoke_work xs enabled))

private theorem transition (xs : List F) (enabled : Bool) (item : F)
    (state : Values (assignment F G) []) :
    Evaluation.foldTransition (table F G) foldSpec (.cons xs .nil) (.cons enabled .nil) state item =
      if enabled then .halt .abort else .done state := by
  cases state
  cases enabled with
  | false =>
    exact Evaluation.foldTransition_false (table F G) foldSpec (by rfl) (.cons xs .nil)
      (.cons false .nil) .nil item (invoke_predicate xs false item)
  | true =>
    exact (Evaluation.foldTransition_true (table F G) foldSpec (by rfl) (.cons xs .nil)
      (.cons true .nil) .nil item (invoke_predicate xs true item)).trans
      (invoke_step xs true item)

/-- A zero-state callback still stops; the caller's Boolean is returned only
when the vector is empty or the predicate disables every step. -/
def reference (xs : List F) (enabled : Bool) :
    Closed (Values (assignment F G) [.boolean]) :=
  if enabled && !xs.isEmpty then .halt .abort else .done (outputs enabled)

/-- Complete process equality, including the abort that bypasses the return. -/
theorem process_eq_reference (xs : List F) (enabled : Bool)
    (lengthValid : xs.length < indexLimit) :
    process (G := G) xs enabled = reference (G := G) xs enabled := by
  rw [process_fold]
  change (Evaluation.denoteFold (table F G) foldSpec
    ((Values.cons xs Values.nil).append
      (Values.nil.append (Values.cons enabled Values.nil)))).bind _ = _
  rw [Evaluation.denoteFold_pack]
  have domainAdmitted :
      (foldSpec.domain.denote (.cons xs (.nil : Values (assignment F G) []))).admit =
        .returned xs := by
    simp [foldSpec, DomainSpec.denote, Finite.Domain.admit, Values.get, lengthValid]
  simp only [Finite.execute, domainAdmitted, Finite.admitThen]
  cases enabled with
  | false =>
    erw [Finite.fold_total _ (fun state _ => state) (fun state item => transition (G := G) xs false item state)]
    simp [reference, PIR.Proc.bind]
  | true =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      dsimp only [Finite.fold]
      rw [transition]
      rfl

/-- Domain failure precedes the predicate, including when it would disable every step. -/
theorem process_exhausted (xs : List F) (enabled : Bool)
    (lengthInvalid : ¬ xs.length < indexLimit) :
    process (G := G) xs enabled = .halt .exhausted := by
  rw [process_fold]
  change (Evaluation.denoteFold (table F G) foldSpec
    ((Values.cons xs Values.nil).append
      (Values.nil.append (Values.cons enabled Values.nil)))).bind _ = _
  rw [Evaluation.denoteFold_pack]
  simp [Finite.execute, DomainSpec.denote, foldSpec, Values.get, Finite.Domain.admit,
    lengthInvalid, Finite.admitThen, PIR.Proc.bind]

theorem process_eq_checked_reference (xs : List F) (enabled : Bool) :
    process (G := G) xs enabled =
      if xs.length < indexLimit then reference (G := G) xs enabled else .halt .exhausted := by
  split
  · exact process_eq_reference (G := G) xs enabled ‹_›
  · exact process_exhausted xs enabled ‹_›

theorem process_nil (enabled : Bool) :
    process (G := G) ([] : List F) enabled = .done (outputs enabled) := by
  simpa [reference] using
    process_eq_reference ([] : List F) enabled (by change 0 < indexLimit; decide +kernel)

theorem process_disabled (xs : List F) (lengthValid : xs.length < indexLimit) :
    process (G := G) xs false = .done (outputs false) := by
  simpa [reference] using process_eq_reference xs false lengthValid

theorem process_enabled_cons (x : F) (xs : List F)
    (lengthValid : (x :: xs).length < indexLimit) :
    process (G := G) (x :: xs) true = .halt .abort := by
  simpa [reference] using process_eq_reference (x :: xs) true lengthValid

theorem process_aborts_iff (xs : List F) (enabled : Bool)
    (lengthValid : xs.length < indexLimit) :
    process (G := G) xs enabled = .halt .abort ↔ enabled = true ∧ xs ≠ [] := by
  rw [process_eq_reference (G := G) xs enabled lengthValid]
  cases enabled <;> cases xs <;> simp [reference]

theorem process_singleton (x : F) (enabled : Bool) :
    process (G := G) [x] enabled = if enabled then .halt .abort else .done (outputs enabled) := by
  simpa [reference] using
    process_eq_reference [x] enabled (by change 1 < indexLimit; decide +kernel)

theorem process_pair (x y : F) (enabled : Bool) :
    process (G := G) [x, y] enabled = if enabled then .halt .abort else .done (outputs enabled) := by
  simpa [reference] using
    process_eq_reference [x, y] enabled (by change 2 < indexLimit; decide +kernel)

theorem exact_subject : imported.program.snapshot = UnitStateData.snapshot :=
  imported.exactSubject

set_option smartUnfolding false in
theorem imported_eq_reference (xs : List F) (enabled : Bool)
    (lengthValid : xs.length < indexLimit) :
    imported.program.denote F G (inputs xs enabled) = reference (G := G) xs enabled :=
  process_eq_reference (G := G) xs enabled lengthValid

end ZkcExamples.Structured.UnitState
