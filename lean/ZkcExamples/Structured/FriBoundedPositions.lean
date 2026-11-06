module

public import ZkcExamples.Structured.FriIndexCollections
public import Zkc.Source.Structured.CallbackPlacement

@[expose] public section

/-! The retained binding component checks the length and every coordinate
of its supplied position list. Its nested comparison runs on the actual
selected branch of the original loop. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriBoundedPositions
open Zkc.Source Zkc.Source.Structured
open FriSourceBodies FriSourceViews
attribute [local implicit_reducible] Numerical.arguments Numerical.results
  Op.arguments Op.results Op.regions

structure Admitted (xs : List Nat) : Prop where
  size : xs.length < indexLimit
  coordinates : xs.all (· < indexLimit) = true

variable {model : DomainModel} {table : Evaluation.MeaningsOn model.toCarriers closedInterface}

private theorem lengthStep (xs : List Nat) (admitted : Admitted xs) :
    (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw (fun op ↦ .call op .done)
      (.exec (.numerical .indicesLength "" "")) (.cons xs .nil) .nil (.done (.cons xs.length .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  let numeric := {model.toFieldModel with inverse := fun _ ↦ none}
  change primitiveOutcome (I := closedInterface) (Numerical.checkedEvaluateOn numeric "" "" .indicesLength
    (.cons xs .nil)) = _
  have valid : Numerical.checkValues numeric (.cons xs .nil : Values numeric.Value [.indices]) = .ok () := by
    change (do (do Numerical.size xs.length; Numerical.require (xs.all (· < indexLimit) = true))
               pure ()) = (Except.ok () : Numerical.Result Unit)
    simp [Numerical.size, Numerical.require, admitted.size, admitted.coordinates, bind, Except.bind,
      pure, Except.pure]
  simp [Numerical.checkedEvaluateOn, valid, Numerical.evaluateOn, Numerical.finish, Numerical.size,
    admitted.size, bind, Except.bind, pure, Except.pure, primitiveOutcome]
  rfl

private theorem atStep (xs : List Nat) (admitted : Admitted xs) (i : Nat) (hi : i < xs.length) :
    (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw (fun op ↦ .call op .done)
      (.exec (.numerical .indicesAt "" "")) (.cons xs (.cons i .nil)) .nil (.done (.cons xs[i] .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  let numeric := {model.toFieldModel with inverse := fun _ ↦ none}
  change primitiveOutcome (I := closedInterface) (Numerical.checkedEvaluateOn numeric "" "" .indicesAt
    (.cons xs (.cons i .nil))) = _
  have valid : Numerical.checkValues numeric
      (.cons xs (.cons i .nil) : Values numeric.Value [.indices, .index]) = .ok () := by
    change (do (do Numerical.size xs.length; Numerical.require (xs.all (· < indexLimit) = true))
               Numerical.require (i < indexLimit); pure ()) = (Except.ok () : Numerical.Result Unit)
    simp [Numerical.size, Numerical.require, admitted.size, admitted.coordinates, hi.trans admitted.size,
      bind, Except.bind, pure, Except.pure]
  simp [Numerical.checkedEvaluateOn, valid, Numerical.evaluateOn, Numerical.finish,
    List.getElem?_eq_getElem hi, pure, Except.pure, primitiveOutcome]
  rfl

def lengthLaw (model : DomainModel) : ReferenceLaw model helper24Helper.inputs helper24Helper.outputs where
  body := helper24Body
  Requires _ | .cons xs .nil => Admitted xs
  reference | .cons xs .nil => .returned (.cons xs.length .nil)
  valid _
    | .cons xs .nil, admitted => by derive_process using (exact lengthStep xs admitted)

/-- The verifier's lookup uses the same checked index primitive as the
binding scan. An in-range occurrence returns the selected list element. -/
def lookupLaw (model : DomainModel) : ReferenceLaw model helper30Helper.inputs helper30Helper.outputs where
  body := helper30Body
  Requires _ | .cons xs (.cons i .nil) => Admitted xs ∧ i < xs.length
  reference
    | .cons xs (.cons i .nil) =>
      match xs[i]? with
      | some position => .returned (.cons position .nil)
      | none => .stopped .refused
  valid _
    | .cons xs (.cons i .nil), ⟨admitted, inside⟩ => by
      simp only [List.getElem?_eq_getElem inside]
      derive_process using (exact atStep xs admitted i inside)

def lessLaw (model : DomainModel) : ReferenceLaw model helper19Helper.inputs helper19Helper.outputs where
  body := helper19Body
  Requires _ | .cons a (.cons b .nil) => a < indexLimit ∧ b < indexLimit
  reference | .cons a (.cons b .nil) => .returned (.cons (decide (a < b)) .nil)
  valid table
    | .cons a (.cons b .nil), ⟨left, right⟩ => by
      have less : (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw (fun op ↦ .call op .done)
          (.exec .indexLess) (.cons a (.cons b .nil)) .nil (.done (.cons (decide (a < b)) .nil)) := by
        apply RegionMeaning.OperationLaw.identity
        change primitiveOutcome (I := closedInterface) (checkedIndices a b _) = _
        simp [checkedIndices, left, right, primitiveOutcome]
      derive_process using (exact less)

private theorem scanStep (xs : List Nat) (bound : Nat)
    (body : Region dialect [.index, .boolean, .indices, .index] [.boolean, .indices, .index])
    (callback : ∀ i, i < xs.length → body.denote (Evaluation.meaningOn model SiteObservations.closed table)
      (Values.cons (Value := model.Value) (ty := .index) i
        (.cons (ty := .boolean) true (.cons (ty := .indices) xs (.cons (ty := .index) bound .nil)))).get =
      .done (.cons true (.cons xs (.cons bound .nil)))) :
    (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw (fun op ↦ .call op .done)
      (.loop [.boolean] [.indices, .index]) (.cons 0 (.cons xs.length (.cons true (.cons xs (.cons bound .nil)))))
      (.cons (fun args ↦ body.denote (Evaluation.meaningOn model SiteObservations.closed table) args.get) .nil)
      (.done (.cons true .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  let run : RegionFunction model.Value closedInterface
      ([.index, .boolean, .indices, .index], [.boolean, .indices, .index]) :=
    fun args ↦ body.denote (Evaluation.meaningOn model SiteObservations.closed table) args.get
  exact Evaluation.denoteLoopOn_states_of_equation run run xs.length _ (.cons xs (.cons bound .nil))
    (state := [.boolean]) (captures := [.indices, .index]) (fun _ ↦ .cons true .nil) rfl (fun _ _ ↦ rfl) callback

private theorem trueBranch {inputs outputs : List Ty} {captures : Values model.Value inputs}
    {yes no : Region dialect inputs outputs} {out : Values model.Value outputs}
    (selected : yes.denote (Evaluation.meaningOn model SiteObservations.closed table) captures.get = .done out) :
    (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw (fun op ↦ .call op .done)
      (.branch inputs outputs) (.cons true captures)
      ((Regions.cons yes (.cons no .nil)).denote (Evaluation.meaningOn model SiteObservations.closed table))
      (.done out) := RegionMeaning.OperationLaw.identity _ _ _ selected

def scanLaw (model : DomainModel) : ReferenceLaw model helper25Helper.inputs helper25Helper.outputs where
  body := helper25Body
  Requires table
    | .cons xs (.cons bound .nil) =>
        Admitted xs ∧ bound < indexLimit ∧ (∀ x ∈ xs, x < bound) ∧
          ∀ x ∈ xs, invoke table helper19Helper (.cons x (.cons bound .nil)) = .done (.cons true .nil)
  reference _ := .returned (.cons true .nil)
  valid table
    | .cons xs (.cons bound .nil), ⟨admitted, _, _, compare⟩ => by
      derive_process using (exact lengthStep xs admitted)
        summarizing
          (apply scanStep xs bound
           intro i inside
           derive_process using (exact atStep xs admitted i inside)
             summarizing
               (apply trueBranch
                derive_process using
                  (apply RegionMeaning.OperationLaw.identity
                   exact compare xs[i] (List.getElem_mem inside))))

theorem installed (xs : List Nat) (bound : Nat) (admitted : Admitted xs)
    (supported : bound < indexLimit) (within : ∀ x ∈ xs, x < bound) {I : PIR.Signature} :
    invoke (FriIndexCollections.helpers model (I := I)).closed helper25Helper (.cons xs (.cons bound .nil)) =
      .done (.cons true .nil) := by
  apply (scanLaw model).invokeOn unit.definitions unit.linked (by exact_body helper25Definition)
    (.cons xs (.cons bound .nil))
  refine ⟨admitted, supported, within, ?_⟩
  intro x member
  have less := within x member
  simpa only [lessLaw, less, decide_true, primitiveOutcome] using
    (lessLaw model).invoke unit.definitions unit.linked (by exact_body helper19Definition)
      (.cons x (.cons bound .nil)) ⟨less.trans supported, supported⟩

end ZkcExamples.Structured.FriBoundedPositions
