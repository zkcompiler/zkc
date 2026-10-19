import ZkcSecurity.FiatShamir.Binding
import ZkcTools.DeclarationAudit

/-! Controls for statement bindings: determination transfers from policy statements to model
statements through a functional relation, and fails without functionality.

A policy statement is a raw table of naturals, bound as one event; the model statement it
denotes is the table's sum. The relation is functional, so equal initial histories, each
followed by any events, have equal model statements (`summed_determines`), and choosing the
one-entry table for every sum gives determined model histories (`summed_determined`). A
relation that lets one table denote every bound on its sum is not functional, and two model
statements share one initial history (`bounded_not_determines`).

Coverage. With the empty relation every policy statement is unmapped and none is false in the
model (`empty_unmapped`, `empty_never_false`), so the modeled event says nothing about the
application: a validator that accepts every table accepts a table whose sum is nonzero, an
application-false statement the modeled event cannot see (`empty_accepted_unseen`). Coverage holds
only through unmapped statements (`empty_covers`), and the rejection of unmapped statements that
the endpoint then requires fails for that validator (`empty_not_rejected`).

Registry citations. A reported assumption cites a registry entry of the obligation's own
category: the collision-bounded identity entry is found by its identifier (`collision_cited`),
and the statement-determination entry, of another category, cannot stand for it
(`determination_not_collision`). -/

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

/-- The empty relation: no table denotes a sum. -/
def empty : StatementBinding (List ℕ) ℕ (List ℕ) where
  codec := tableCodec
  models _ _ := False
  functional _ _ _ denotes _ := denotes.elim

theorem empty_unmapped (table : List ℕ) : empty.Unmapped table := fun _ denotes => denotes

theorem empty_never_false (falseModel : ℕ → Prop) (table : List ℕ) :
    ¬ empty.falsePolicy falseModel table :=
  empty.not_falsePolicy_of_unmapped falseModel table (empty_unmapped table)

/-- A validator that accepts every table. -/
def acceptsAll (_ : List ℕ) : Bool := true

/-- The application calls a table false when its sum is nonzero. -/
def applicationFalse (table : List ℕ) : Prop := table.sum ≠ 0

/-- An accepted application-false statement that the modeled event does not see. -/
theorem empty_accepted_unseen :
    applicationFalse [1] ∧ acceptsAll [1] = true ∧ ¬ empty.falsePolicy (fun sum => sum ≠ 0) [1] :=
  ⟨by simp [applicationFalse], rfl, empty_never_false _ _⟩

theorem empty_covers : empty.Covers (fun sum => sum ≠ 0) applicationFalse :=
  fun table _ => .inr (empty_unmapped table)

/-- The rejection of unmapped statements fails for the accepting validator. -/
theorem empty_not_rejected : ¬ ∀ table, empty.Unmapped table → acceptsAll table = false :=
  fun rejects => absurd (rejects [1] (empty_unmapped [1])) (by decide)

/-- The collision-bounded identity entry, cited by its identifier. -/
theorem collision_cited :
    ∃ entry, registryEntry "binding.collision-bounded-identity" = some entry ∧
      entry.category = .binding .collisionBoundedIdentity := by
  refine ⟨_, rfl, rfl⟩

/-- An assumed collision bound cites its registry entry. -/
def assumedCollision (claim : Prop) :
    ObligationStatus (.binding .collisionBoundedIdentity) claim :=
  ObligationStatus.cite "binding.collision-bounded-identity" _ rfl rfl

/-- The statement-determination entry has another category and cannot be cited for the
collision bound. -/
theorem determination_not_collision (entry : ZkcSecurity.Registry.Entry)
    (found : registryEntry "binding.statement-determination" = some entry) :
    entry.category ≠ .binding .collisionBoundedIdentity := by
  have same : entry.category = .binding .statementDetermination := by
    rw [show registryEntry "binding.statement-determination" = some
      ⟨"binding.statement-determination", .binding .statementDetermination,
        some `Zkc.Transcript.Determined,
        "The initial transcript of a statement, followed by any events, determines the \
        statement, malformed statements included."⟩ from rfl] at found
    cases found
    rfl
  rw [same]
  decide

end TestsSecurity.StatementBindings

run_cmd ZkcTools.DeclarationAudit.checkCurrent "STATEMENT-BINDINGS-AXIOM-PASS"
