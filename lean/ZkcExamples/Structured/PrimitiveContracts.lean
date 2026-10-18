module

public import ZkcExamples.Structured.PrimitiveLibraryConsumers

@[expose] public section

/-! Conditional contracts on exact typed views of the three admitted original
wrappers. The full-table process equations supply the contracts; the separate
raw equalities retain their original-source subject and ordered ports. -/
namespace ZkcExamples.Structured.PrimitiveContracts
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary PrimitiveLibraryConsumers
-- Local transparency options below elaborate dependent source-view aliases;
-- every resulting equation is still checked by the kernel.
set_option smartUnfolding false

private theorem environment_inputs {F G : Type}
    (env : Environment (assignment F G) [vector, .index, .index]) :
    @Eq (Environment (assignment F G) [vector, .index, .index])
      (inputs (env .here) (env (.there .here)) (env (.there (.there .here)))).get env := by
  funext type reference
  cases reference with
  | here => rfl
  | there reference => cases reference with
    | here => rfl
    | there reference => cases reference with
      | here => rfl
      | there reference => cases reference

/-- Representation premises belong to the caller, not to field reduction. -/
def Representable {F G : Type} (env : Environment (assignment F G) [vector, .index, .index]) : Prop :=
  (env .here).length < indexLimit ∧ env (.there .here) < indexLimit ∧
    env (.there (.there .here)) < indexLimit

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem shape_contract : PrimitiveShapeViews.entryBody.Contract
    (meaning F G (PrimitiveShapeViews.program.payload.meanings F G)) Representable
    (fun env values => values.get .here =
      decide (HasShape (env .here) (env (.there .here)) (env (.there (.there .here))))) := by
  intro env valid
  refine ⟨boolResult (decide (HasShape (env .here) (env (.there .here))
    (env (.there (.there .here))))), ?_, rfl⟩
  have viewed := Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    PrimitiveShapeViews.program.payload PrimitiveShapeViews.entryBody PrimitiveShapeViews.entry_exact
    (inputs (env .here) (env (.there .here)) (env (.there (.there .here))))
  have equation := viewed.symm.trans (Shape.process_equation (G := G) (env .here) (env (.there .here))
    (env (.there (.there .here))) valid.1 valid.2.1 valid.2.2)
  rw [environment_inputs] at equation
  exact equation

set_option backward.isDefEq.respectTransparency false in
/-- A valid table constructor preserves vector, dimension and columns exactly. -/
theorem table_contract : PrimitiveTableViews.entryBody.Contract
    (meaning F G (PrimitiveTableViews.program.payload.meanings F G))
    (fun env => Representable env ∧
      HasShape (env .here) (env (.there .here)) (env (.there (.there .here))))
    (fun env values => values =
      inputs (env .here) (env (.there .here)) (env (.there (.there .here)))) := by
  intro env valid
  refine ⟨inputs (env .here) (env (.there .here)) (env (.there (.there .here))), ?_, rfl⟩
  have viewed := Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    PrimitiveTableViews.program.payload PrimitiveTableViews.entryBody PrimitiveTableViews.entry_exact
    (inputs (env .here) (env (.there .here)) (env (.there (.there .here))))
  have equation := viewed.symm.trans (Table.process_equation (G := G) (env .here) (env (.there .here))
    (env (.there (.there .here))) valid.1.1 valid.1.2.1 valid.1.2.2)
  rw [environment_inputs, ite_eq_left valid.2] at equation
  exact equation

set_option backward.isDefEq.respectTransparency false in
/-- The full table-then-halves wrapper returns two contiguous shaped tables.
Neither result may be discarded or reordered in this postcondition. -/
theorem halves_contract : PrimitiveHalvesViews.entryBody.Contract
    (meaning F G (PrimitiveHalvesViews.program.payload.meanings F G))
    (fun env => Representable env ∧
      HasShape (env .here) (env (.there .here)) (env (.there (.there .here))) ∧
        0 < env (.there .here))
    (fun env values =>
      values = .cons ((env .here).take ((env .here).length / 2))
        (.cons ((env .here).drop ((env .here).length / 2)) .nil) ∧
      HasShape (values.get .here) (env (.there .here) - 1) (env (.there (.there .here))) ∧
      HasShape (values.get (.there .here)) (env (.there .here) - 1) (env (.there (.there .here))) ∧
      values.get .here ++ values.get (.there .here) = env .here) := by
  intro env valid
  refine ⟨.cons ((env .here).take ((env .here).length / 2))
    (.cons ((env .here).drop ((env .here).length / 2)) .nil), ?_, rfl, ?_⟩
  · have viewed := Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
      PrimitiveHalvesViews.program.payload PrimitiveHalvesViews.entryBody PrimitiveHalvesViews.entry_exact
      (inputs (env .here) (env (.there .here)) (env (.there (.there .here))))
    have equation := viewed.symm.trans (Halves.process_equation (G := G) (env .here) (env (.there .here))
      (env (.there (.there .here))) valid.1.1 valid.1.2.1 valid.1.2.2)
    rw [environment_inputs, ite_eq_left valid.2.1, ite_eq_left valid.2.2,
      ite_eq_left (valid.2.1.split_valid valid.2.2)] at equation
    exact equation
  · exact valid.2.1.halves valid.2.2

end ZkcExamples.Structured.PrimitiveContracts
