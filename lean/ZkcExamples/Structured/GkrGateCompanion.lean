module

public import ZkcExamples.Structured.GkrGateGoals
public import Zkc.Protocols.Multilinear.Source.CollectionEncoding
public import Zkc.Source.Structured.MapLaws

@[expose] public section

/-! Mathematical companions for the source-selected gates. The generated Goal
owns ABI packing, the full output type and the correspondence statement. -/
namespace ZkcExamples.Structured.GkrGateCompanion
open Zkc.Source Zkc.Source.Structured
open GkrGateGoals

set_option backward.isDefEq.respectTransparency false

def valueReference (model : DomainModel)
    (addWeight mulWeight left right : model.Field scalarDomain) : PIR.Outcome (Value.Output model) :=
  .returned ⟨Zkc.Protocols.AlgebraicRounds.Gate.value addWeight mulWeight left right⟩

theorem value (model : DomainModel) :
    Value.Goal model (valueReference model) (fun _ _ _ _ _ => True) := by
  intro table addWeight mulWeight left right _
  rfl

noncomputable def valueLaw (model : DomainModel) :=
  Value.law model (valueReference model) (fun _ _ _ _ _ => True) (value model)

def realizationReference (model : DomainModel)
    (addWeight mulWeight left right : model.Field scalarDomain) :
    PIR.Outcome (Realization.Output model) :=
  .returned ⟨Zkc.Protocols.AlgebraicRounds.Gate.value addWeight mulWeight left right⟩

noncomputable def realizationLibrary (model : DomainModel) :=
  forward_reference% Realization.body using (valueLaw model)

def realizationCondition (model : DomainModel) :=
  fun table (_ _ _ _ : model.Field scalarDomain) =>
    (valueLaw model).Realizes (helper := GkrSourceBodies.helper31Helper) table

/-- The direct forwarding library preserves all outcomes of the explicit
value dependency; it checks the actual scoped wrapper's complete body. -/
theorem realization (model : DomainModel) :
    Realization.Goal model (realizationReference model) (realizationCondition model) := by
  apply Realization.of_law model _ _ (realizationLibrary model) rfl
  · intro addWeight mulWeight left right; rfl
  · intro table addWeight mulWeight left right dependency; exact dependency _

noncomputable def realizationLaw (model : DomainModel) :=
  Realization.law model (realizationReference model) (realizationCondition model) (realization model)

def callbackReference (model : DomainModel)
    (addWeight mulWeight left right : model.Field scalarDomain)
    (_ _ _ _ : List (model.Field scalarDomain)) : PIR.Outcome (Callback.Output model) :=
  .returned ⟨Zkc.Protocols.AlgebraicRounds.Gate.value addWeight mulWeight left right⟩

noncomputable def callbackLibrary (model : DomainModel) :=
  forward_reference% Callback.body using (realizationLaw model)

def callbackCondition (model : DomainModel) :=
  fun table (_ _ _ _ : model.Field scalarDomain) (_ _ _ _ : List (model.Field scalarDomain)) =>
    (realizationLaw model).Realizes (helper := GkrSourceBodies.scopedHelper42Helper) table

theorem callback (model : DomainModel) :
    Callback.Goal model (callbackReference model) (callbackCondition model) := by
  apply Callback.of_law model _ _ (callbackLibrary model) rfl
  · intro addWeight mulWeight left right addWeights mulWeights lefts rights; rfl
  · intro table addWeight mulWeight left right addWeights mulWeights lefts rights dependency
    exact dependency _

noncomputable def callbackLaw (model : DomainModel) :=
  Callback.law model (callbackReference model) (callbackCondition model) (callback model)

def mapValues (model : DomainModel)
    (addWeights mulWeights lefts rights : List (model.Field scalarDomain)) (length : Nat) :=
  (List.range length).map fun index =>
    Zkc.Protocols.AlgebraicRounds.Gate.value (addWeights[index]?.getD 0)
      (mulWeights[index]?.getD 0) (lefts[index]?.getD 0) (rights[index]?.getD 0)

/-- The mathematical list reference retains strict shape admission and the
complete ordered result. Captured vectors stay in the checked callback ABI. -/
def mapReference (model : DomainModel)
    (addWeights mulWeights lefts rights : List (model.Field scalarDomain)) :
    PIR.Outcome (Map.Output model) :=
  match Evaluation.mapShape [addWeights.length, mulWeights.length, lefts.length, rights.length] with
  | .stopped reason => .stopped reason
  | .returned length => .returned ⟨mapValues model addWeights mulWeights lefts rights length⟩

noncomputable def mapLibrary (model : DomainModel) :=
  collection_reference% Map.body with_model model
    with_shape (fun addWeights mulWeights lefts rights => Evaluation.mapShape
      [addWeights.length, mulWeights.length, lefts.length, rights.length])
    with_items (fun addWeights mulWeights lefts rights index => Item.pack
      { addWeight := addWeights[index]?.getD 0, mulWeight := mulWeights[index]?.getD 0,
        left := lefts[index]?.getD 0, right := rights[index]?.getD 0 })
    with_formula (fun addWeight mulWeight left right _ _ _ _ =>
      Zkc.Protocols.AlgebraicRounds.Gate.value addWeight mulWeight left right)

noncomputable def mapCondition (model : DomainModel) := fun table =>
  Values.curry _ ((mapLibrary model).Requires table)

/-- Direct library transport discharges the generated named complete Goal.
The remaining premises are source admission and the actual callback law. -/
theorem map (model : DomainModel) :
    Map.Goal model (mapReference model) (mapCondition model) := by
  apply Map.of_law model _ _ (mapLibrary model) rfl
  · intro addWeights mulWeights lefts rights
    reference_encoding [mapLibrary, mapReference, Item.pack]
  · intro table addWeights mulWeights lefts rights dependencies; exact dependencies

noncomputable def mapLaw (model : DomainModel) :=
  Map.law model (mapReference model) (mapCondition model) (map model)

/-- Pointwise gate evaluation commutes with the shared finite vertex order,
for four arbitrary tables. No source layout or fixed wiring table is a premise. -/
theorem map_encodes (model : DomainModel) {n : Nat}
    (add mul left right : Zkc.Polynomial.Multilinear.Table (model.Field scalarDomain) n)
    (small : 2 ^ n < indexLimit) :
    mapReference model
      (List.ofFn (fun position => add (Zkc.Polynomial.Multilinear.vertex n position)))
      (List.ofFn (fun position => mul (Zkc.Polynomial.Multilinear.vertex n position)))
      (List.ofFn (fun position => left (Zkc.Polynomial.Multilinear.vertex n position)))
      (List.ofFn (fun position => right (Zkc.Polynomial.Multilinear.vertex n position))) =
      .returned ⟨List.ofFn (fun position => Zkc.Protocols.AlgebraicRounds.Gate.value
        (add (Zkc.Polynomial.Multilinear.vertex n position))
        (mul (Zkc.Polynomial.Multilinear.vertex n position))
        (left (Zkc.Polynomial.Multilinear.vertex n position))
        (right (Zkc.Polynomial.Multilinear.vertex n position)))⟩ := by
  have shape : Evaluation.mapShape [2 ^ n, 2 ^ n, 2 ^ n, 2 ^ n] = .returned (2 ^ n) :=
    Evaluation.mapShape_of_equal _ _ small (by simp)
  simp only [mapReference, mapValues, List.length_ofFn, shape]
  congr 2
  exact Evaluation.map_range_ofFn
    (fun row position => (![add, mul, left, right] : Fin 4 → _)
      row (Zkc.Polynomial.Multilinear.vertex n position)) 0
    (fun values => Zkc.Protocols.AlgebraicRounds.Gate.value
      (values 0) (values 1) (values 2) (values 3))

end ZkcExamples.Structured.GkrGateCompanion
