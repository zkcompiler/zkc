import ZkcClean.Relation

/-! Obligation (3): reuse of the source component specification.

The corollaries compose obligation (2) with upstream
`Air.Flat.Component.weakSoundness` and `Air.Flat.Table.weakSoundness`. Their
actual `Assumptions` remain hypotheses and may constrain `Environment.data`.
The `FullGuarantees` premise is not assumed: the export admits no interaction
at any depth, which discharges it (and makes `FullRequirements` hold) as stated
separately below. The conclusion is the source `Spec` per row. It concerns no
machine execution, channel balance, STARK reduction or Fiat-Shamir property.
-/

set_option autoImplicit false

namespace ZkcClean

open Zkc.Relation

variable {F : Type} [FiniteField F]

/-- The channel-free guarantee simplification. -/
theorem guarantees_of_export {component : Air.Flat.Component F} {artifact : Artifact}
    (exported : exportComponent component = .ok artifact) (env : Environment F) :
    component.operations.FullGuarantees env ∧ component.operations.FullRequirements env := by
  have admitted := exportComponent_ok exported
  simp [Operations.FullGuarantees, Operations.FullRequirements, admitted.noInteractions]

theorem table_guarantees_of_export (table : Air.Flat.Table F) {artifact : Artifact}
    (exported : exportComponent table.component = .ok artifact) :
    table.Guarantees ∧ table.Requirements :=
  ⟨fun _ _ => (guarantees_of_export exported _).1,
    fun _ _ => (guarantees_of_export exported _).2⟩

/-- Row form: the zkc relation and the component's actual assumptions on one
row, with that row's `Environment.data`, give the component's specification. -/
theorem row_spec {component : Air.Flat.Component F} {artifact : Artifact}
    (exported : exportComponent component = .ok artifact)
    {cs : List (AIR.Constraint F 0 artifact.width)} (decoded : artifact.decode F = some cs)
    {height : Nat} (statement : Fin 0 → F) (trace : Fin (height + 1) → Fin artifact.width → F)
    (holds : (AIR.family cs height).holds statement trace)
    (row : Fin (height + 1)) (data : ProverData F)
    (assumptions : component.Assumptions (rowEnvironment (trace row) data)) :
    component.Spec (rowEnvironment (trace row) data) :=
  (Air.Flat.Component.weakSoundness assumptions
    ((holds_iff exported decoded statement trace data).mp holds row)
    (guarantees_of_export exported _).1).1

/-- Table form: Clean's actual table assumptions and the zkc relation on the
table's rows give upstream `Table.Spec` and `Table.Requirements`. -/
theorem table_spec (table : Air.Flat.Table F) {artifact : Artifact}
    (exported : exportComponent table.component = .ok artifact)
    {cs : List (AIR.Constraint F 0 artifact.width)} (decoded : artifact.decode F = some cs)
    {height : Nat} (length : table.table.length = height + 1)
    (widthEq : table.width = artifact.width) (statement : Fin 0 → F)
    (assumptions : table.Assumptions)
    (holds : (AIR.family cs height).holds statement (tableTrace table length widthEq)) :
    table.Spec ∧ table.Requirements :=
  Air.Flat.Table.weakSoundness assumptions
    ((table_holds_iff table exported decoded length widthEq statement).mp holds)
    (table_guarantees_of_export table exported).1

end ZkcClean
