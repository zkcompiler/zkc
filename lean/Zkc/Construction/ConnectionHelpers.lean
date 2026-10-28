module

public import Zkc.Construction.ConnectionCalculations

@[expose] public section

/-! Finite structural bindings for retained nominal helpers. The complete
source declaration fold fixes bodies and captured dependency prefixes. A
target program must carry exactly those declarations, and a checked index
selects the complete helper key. There is no result law or root equation. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionHelpers
open Zkc.Source Zkc.Source.Structured NormalForm

/-- A finite source-owned/helper-owned association, checked by reduction. -/
structure Binding (definitions : List CheckedDefinition) (helper : Helper) (program : Program) where
  entry : Fin definitions.length
  key : (definitions.get entry).helper = helper
  declarations : program.payload.definitions = definitions

/-- Pure certificates leave tables arbitrary. A nonempty source closure is
interpreted by its actual component/closed declaration fold, in every model.
This equation fixes tables; it does not assert any helper result or totality. -/
def TablesMatch (model : DomainModel) (definitions : List CheckedDefinition)
    (tables : Tables model (Occurrence.signature model.toCarriers)) : Prop :=
  ∀ _ : Fin definitions.length,
    tables = definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩

theorem Binding.present {definitions : List CheckedDefinition} {helper : Helper} {program : Program}
    (binding : Binding definitions helper program) :
    helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
  rw [binding.declarations, ← binding.key]
  exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩

theorem Binding.tables {model : DomainModel} {definitions : List CheckedDefinition}
    {helper : Helper} {program : Program} (binding : Binding definitions helper program)
    {tables : Tables model (Occurrence.signature model.toCarriers)}
    (matched : TablesMatch model definitions tables) :
    tables = program.payload.definitions.foldl
      (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩ := by
  rw [binding.declarations]
  exact matched binding.entry

end Zkc.Construction.ConnectionHelpers
