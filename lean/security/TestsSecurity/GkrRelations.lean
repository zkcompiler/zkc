module

public import ZkcSecurity.Bindings.Gkr.Relations
public import TestsSecurity.GkrEncoding

@[expose] public section

namespace TestsSecurity.GkrRelations
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Realizations.Gkr
open Zkc.Polynomial Zkc.Polynomial.Multilinear

abbrev model := ringModel ℚ ℚ
abbrev domain := "bls12-381.fr"

def outputRelation : Relation :=
  ⟨"CircuitOutputs", .privateDef, "gkr.circuit/0", "outputs", "0",
    Relations.outputInputs domain, [.boolean],
    ["parameter", "parameter", "parameter", "parameter", "parameter", "parameter", "statement"],
    none, [.field domain]⟩

def outputBinding : (Relations.registry model).Binding outputRelation where
  instantiation := {
    inputs := Relations.outputInputs domain
    purposes := outputRelation.purposes
    holds := Relations.outputMeaning model domain }
  selected := rfl
  inputs := rfl
  outputs := rfl
  purposes := rfl
  opaqueKind := by decide +kernel
  noFormula := rfl

def outputArguments (outputs : List ℚ) : Values model.Value outputRelation.inputs :=
  .cons [7] (.cons [0] (.cons [0] (.cons 0 (.cons 0 (.cons 0 (.cons outputs .nil))))))

theorem correct_output : outputBinding.Holds (outputArguments [7]) :=
  GkrEncoding.valid_empty

theorem wrong_output : ¬ outputBinding.Holds (outputArguments [8]) :=
  GkrEncoding.changed_output

/-- A different proof record cannot replace circuit evaluation with a predicate
that accepts the wrong output. The registry was fixed before this evidence. -/
theorem wrong_output_any_evidence
    (evidence : (Relations.registry model).Binding outputRelation) :
    ¬ evidence.Holds (outputArguments [8]) := by
  intro accepted
  exact wrong_output ((evidence.unique_meaning outputBinding _).mp accepted)

example : ((Relations.registry model).resolve outputRelation).isSome = true := by
  decide +kernel

example : ((Relations.registry model).resolve
    { outputRelation with staticArguments := [.field domain, .natural "4"] }).isSome = false := by
  decide +kernel

example : ((Relations.registry model).resolve
    { outputRelation with purposes := List.replicate 7 "parameter" }).isSome = false := by
  decide +kernel

example : ((Relations.shapeFamily model).instantiate
    [.field domain, .natural "04", .natural "4"]).isNone = true := by
  decide +kernel

def twoValues (low high : ℚ) : Table ℚ 1 :=
  ofVector (fun i => [low, high][i.val]'(by simp))

theorem twoValues_decoded (low high : ℚ) :
    ofList? 1 [low, high] = some (twoValues low high) := rfl

/-- At an off-cube challenge the product of extensions differs from the
extension of the Boolean pointwise product. The registry retains the former. -/
theorem off_cube_product : Relations.Residual [0, 1] [0, 0] [0, 1] [0, 0] [2] (4 : ℚ) := by
  rw [Relations.residual_restricted (remaining := 0) [0, 1] [0, 0] [0, 1] [0, 0] [2] 4
    (twoValues 0 1) (twoValues 0 0) (twoValues 0 1) (twoValues 0 0)
    (twoValues_decoded 0 1) (twoValues_decoded 0 0)
    (twoValues_decoded 0 1) (twoValues_decoded 0 0)]
  decide +kernel

theorem product_table_refused : ¬ Relations.Residual [0, 1] [0, 0] [0, 1] [0, 0] [2] (2 : ℚ) := by
  rw [Relations.residual_restricted (remaining := 0) [0, 1] [0, 0] [0, 1] [0, 0] [2] 2
    (twoValues 0 1) (twoValues 0 0) (twoValues 0 1) (twoValues 0 0)
    (twoValues_decoded 0 1) (twoValues_decoded 0 0)
    (twoValues_decoded 0 1) (twoValues_decoded 0 0)]
  decide +kernel

theorem empty_cube_refused : ¬ Relations.Residual [] [0] [0] [0] [] (0 : ℚ) := by
  intro accepted
  have impossible := Relations.residual_nonempty accepted
  exact Nat.not_lt_zero _ impossible

theorem overlong_prefix_refused :
    ¬ Relations.Residual [0, 1] [0, 0] [0, 1] [0, 0] [0, 1] (0 : ℚ) := by
  intro accepted
  have bound := Relations.residual_prefix_le (twoValues 0 1) (twoValues_decoded 0 1) accepted
  norm_num at bound

#print axioms correct_output
#print axioms wrong_output_any_evidence
#print axioms Relations.residual_restricted
#print axioms off_cube_product
#print axioms product_table_refused
#print axioms overlong_prefix_refused

end TestsSecurity.GkrRelations
