import ZkcSecurity.FiatShamir.Binding

/-! Controls for binding codecs and the typed public-value binding event.

A raw Sumcheck statement is what the prover outputs: the table values, the
claimed sum and the round count, with no check that the table has `2 ^ count`
entries. Its canonical row binds the table as a vector, the claim as a scalar
and the round count as a count, and its initial history is one binding event.
Because the row is injective on every raw statement, malformed ones included,
the histories determine the statement (`determined`). A well-formed statement,
a two-entry table at one round, and a malformed one, the same table at two
rounds, are told apart (`malformed_separated`); so are any two counts of one
table (`counts_separated`), and statements whose tables differ only by a
trailing entry (`prefix_separated`).

A codec that binds the table entries one event each, without a count or a
length, is injective on statements of one table length but not prefix-free
across lengths: a two-entry table's history is a prefix of a three-entry
table's, and `Typed.Determined` fails (`unprefixed_not_determined`). -/

namespace TestsSecurity.BindingCodecs
open ZkcSecurity.FiatShamir
open Zkc.Construction (PublicValue Row PublicBinding)

/-- A raw Sumcheck statement, as the prover outputs it. -/
structure RawStatement (F : Type) where
  raw : List F
  claim : F
  count : ℕ

variable {F : Type}

/-- The canonical row: the table, the claim and the round count, in input order. -/
def row (statement : RawStatement F) : Row F :=
  [("table", .vector statement.raw), ("claim", .scalar statement.claim),
    ("rounds", .count statement.count)]

theorem row_injective : Function.Injective (row (F := F)) := by
  rintro ⟨raw, claim, count⟩ ⟨raw', claim', count'⟩ same
  simp only [row, List.cons.injEq, Prod.mk.injEq, PublicValue.vector.injEq,
    PublicValue.scalar.injEq, PublicValue.count.injEq, true_and, and_true] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  rfl

/-- Transcript events: a typed public-value binding or a challenge occurrence. -/
inductive Event (F : Type) where
  | binding (event : PublicBinding F)
  | challenge (round : ℕ)

/-- The initial history of a statement: one binding event. -/
def initial (statement : RawStatement F) : List (Event F) :=
  [.binding ⟨"sumcheck", row statement⟩]

theorem determined : Typed.Determined (initial (F := F)) :=
  determined_single Event.binding (fun _ _ same => by cases same; rfl) "sumcheck" row row_injective

/-- A two-entry table at one round is well formed (`2 = 2 ^ 1`); at two rounds it
is malformed (`2 ≠ 2 ^ 2`). The two statements have distinct histories. -/
theorem malformed_separated (first second claim : F) :
    initial ⟨[first, second], claim, 1⟩ ≠ initial ⟨[first, second], claim, 2⟩ := by
  intro same
  have := determined _ _ [] [] (by simpa using same)
  simp at this

theorem counts_separated (raw : List F) (claim : F) {count other : ℕ} (different : count ≠ other) :
    initial ⟨raw, claim, count⟩ ≠ initial ⟨raw, claim, other⟩ := by
  intro same
  have := congrArg RawStatement.count (determined _ _ [] [] (by simpa using same))
  exact different this

theorem prefix_separated (raw : List F) (claim last : F) (count : ℕ) :
    initial ⟨raw, claim, count⟩ ≠ initial ⟨raw ++ [last], claim, count⟩ := by
  intro same
  have := congrArg RawStatement.raw (determined _ _ [] [] (by simpa using same))
  simp at this

/-- One event per table entry, with no count and no length. -/
def unprefixed (statement : RawStatement F) : List (Event F) :=
  statement.raw.map fun value => .binding ⟨"entry", [("value", .scalar value)]⟩

theorem unprefixed_not_determined (zero : F) :
    ¬ Typed.Determined (unprefixed (F := F)) := by
  intro determines
  have same := determines ⟨[zero, zero], zero, 1⟩ ⟨[zero, zero, zero], zero, 1⟩
    [.binding ⟨"entry", [("value", .scalar zero)]⟩] [] (by simp [unprefixed])
  have := congrArg (fun statement : RawStatement F => statement.raw.length) same
  simp at this

end TestsSecurity.BindingCodecs
