import Zkc.Source.Structured.InputAdmission

/-! Representation checks descend through aggregate values. These are logical
ABI premises; no byte encoding or native execution correspondence is inferred. -/
namespace Tests.StructuredInputAdmission
open Zkc.Source Zkc.Source.Structured

private abbrev carriers := uniformCarriers Nat Nat
private def fields : ProductFields := .cons .index (.cons (.vector "F") .nil)
private def row : Ty := .product "test::Row" "row" fields

example : inputRepresentable (carriers := carriers) row none := by
  simp [row, inputRepresentable]

example : inputRepresentable (carriers := carriers) row (some (7, [1, 2], ())) := by
  change 7 < indexLimit ∧ 2 < indexLimit ∧ True
  decide +kernel

example : ¬ inputRepresentable (carriers := carriers) row (some (indexLimit, [], ())) := by
  simp [row, fields, inputRepresentable, productRepresentable]

example : ¬ inputRepresentable (carriers := carriers) (.sequence row)
    (some [(0, [], ()), (indexLimit, [], ())]) := by
  intro admitted
  have member := admitted.2 (indexLimit, [], ())
    (List.mem_cons_of_mem _ List.mem_cons_self)
  exact Nat.lt_irrefl indexLimit member.1

example (index : Nat) (values : List Nat) :
    inputRepresentable (carriers := carriers) row (some (index, values, ())) ↔
      index < indexLimit ∧ values.length < indexLimit := by
  simp [row, fields, inputRepresentable, productRepresentable]

example (rows : List (carriers.Value row)) :
    inputRepresentable (carriers := carriers) (.sequence row) (some rows) ↔
      rows.length < indexLimit ∧ ∀ value ∈ rows,
        value.1 < indexLimit ∧ value.2.1.length < indexLimit := by
  simp [row, fields, inputRepresentable, productRepresentable]

-- Logical service handles are not u64 index inputs.
example : inputRepresentable (carriers := carriers) (.service "random")
    (some indexLimit) := by
  simp [inputRepresentable]

end Tests.StructuredInputAdmission
