module

public import ZkcExamples.Structured.GkrGateGoals
public import Zkc.Protocols.Multilinear.Source.CollectionEncoding
public import Zkc.Source.Structured.MapLaws

public meta import ZkcTools.StructuredSource.ReferenceInstallation

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

noncomputable def realizationLaw (model : DomainModel) :=
  forward_reference% Realization.body using (valueLaw model)

noncomputable def callbackLaw (model : DomainModel) :=
  forward_reference% Callback.body using (realizationLaw model)

/-- One installation of the scalar dependency chain in the actual linked table. -/
structure ScalarLaws (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop where
  value : (valueLaw model).Realizes (helper := GkrSourceBodies.helper19Helper) table
  realization : (realizationLaw model).Realizes (helper := GkrSourceBodies.helper55Helper) table
  callback : (callbackLaw model).Realizes (helper := GkrSourceBodies.helper56Helper) table

theorem installScalars (model : DomainModel) (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions) :
    ScalarLaws model (closedMeaningsOn model definitions) := by
  install_reference_laws using linked with bodies

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

noncomputable def mapLaw (model : DomainModel) :=
  collection_reference% Map.body with_model model
    with_shape (fun addWeights mulWeights lefts rights => Evaluation.mapShape
      [addWeights.length, mulWeights.length, lefts.length, rights.length])
    with_items (fun addWeights mulWeights lefts rights index => Item.pack
      { addWeight := addWeights[index]?.getD 0, mulWeight := mulWeights[index]?.getD 0,
        left := lefts[index]?.getD 0, right := rights[index]?.getD 0 })
    with_formula (fun addWeight mulWeight left right _ _ _ _ =>
      Zkc.Protocols.AlgebraicRounds.Gate.value addWeight mulWeight left right)

theorem map_reference (model : DomainModel)
    (addWeights mulWeights lefts rights : List (model.Field scalarDomain)) :
    (mapLaw model).reference (Map.Inputs.pack { addWeights, mulWeights, lefts, rights }) =
      Map.encodeOutcome model (mapReference model addWeights mulWeights lefts rights) := by
  reference_encoding [mapLaw, mapReference, Item.pack]

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
