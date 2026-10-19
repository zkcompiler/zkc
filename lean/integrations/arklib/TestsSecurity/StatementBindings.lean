import ZkcSecurity.FiatShamir.Binding

/-! Controls for statement bindings: determination transfers from policy statements to model
statements through a functional relation, and fails without functionality.

A policy statement is a raw table of naturals, bound as one event; the model statement it
denotes is the table's sum. The relation is functional, so equal initial histories, each
followed by any events, have equal model statements (`summed_determines`), and choosing the
one-entry table for every sum gives determined model histories (`summed_determined`). A
relation that lets one table denote every bound on its sum is not functional, and two model
statements share one initial history (`bounded_not_determines`). -/

namespace TestsSecurity.StatementBindings
open ZkcSecurity.FiatShamir

/-- One event binding the whole table. -/
def tableCodec : BindingCodec (List ℕ) (List ℕ) where
  encode table := [table]
  injective first second same := by simpa using same
  prefixFree statement other rest same := by simpa using congrArg List.length same

/-- A table denotes its sum. -/
def summed : StatementBinding (List ℕ) ℕ (List ℕ) where
  codec := tableCodec
  models table sum := sum = table.sum
  functional _ _ _ first second := first.trans second.symm

theorem summed_determines (table other : List ℕ) (rest otherRest : List (List ℕ))
    (same : tableCodec.encode table ++ rest = tableCodec.encode other ++ otherRest) :
    table.sum = other.sum :=
  summed.determines table other table.sum other.sum rest otherRest rfl rfl same

theorem summed_determined : Typed.Determined fun sum : ℕ => tableCodec.encode [sum] :=
  summed.determined_represent (fun sum => [sum]) fun sum => by simp [summed]

/-- A false sum, at the table level. -/
theorem summed_false (table : List ℕ) :
    summed.falsePolicy (fun sum => sum ≠ 0) table ↔ table.sum ≠ 0 :=
  summed.falsePolicy_iff _ table table.sum rfl

/-- Every bound on the sum: not functional. -/
def bounded (table : List ℕ) (bound : ℕ) : Prop := table.sum ≤ bound

theorem bounded_not_determines :
    ¬ ∀ (table other : List ℕ) (model otherModel : ℕ) (rest otherRest : List (List ℕ)),
      bounded table model → bounded other otherModel →
        tableCodec.encode table ++ rest = tableCodec.encode other ++ otherRest → model = otherModel := by
  intro determines
  have := determines [] [] 0 1 [] [] (by simp [bounded]) (by simp [bounded]) rfl
  exact absurd this (by decide)

end TestsSecurity.StatementBindings

#print axioms ZkcSecurity.FiatShamir.StatementBinding.determines
#print axioms ZkcSecurity.FiatShamir.StatementBinding.determined_represent
#print axioms ZkcSecurity.FiatShamir.StatementBinding.falsePolicy_iff
#print axioms TestsSecurity.StatementBindings.summed_determined
#print axioms TestsSecurity.StatementBindings.bounded_not_determines
