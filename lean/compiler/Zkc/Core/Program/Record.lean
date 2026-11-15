module

public import Zkc.Core.Program.Vocabulary

@[expose] public section

/-!
The record of a run: its fields, each named by a label, and their values.
-/

namespace Zkc.Core

/-! ## The record of a run -/

mutual
  /-- The type of a field: a value, an option of an arm, a collection of a loop, the record
  of a callee or of a block. -/
  inductive FTy (V : Vocabulary) where
    | val (τ : V.Ty)
    | opt (a : FTy V)
    | many (a : FTy V)
    | record (fs : Fields V)
  /-- The fields of the record of a run, each with its name, in order. -/
  inductive Fields (V : Vocabulary) where
    | nil
    | cons (name : Label) (a : FTy V) (rest : Fields V)
end

mutual
  @[reducible] def FTy.Val {V : Vocabulary} (M : Model V) : FTy V → Type
    | .val τ => M.Val τ
    | .opt a => Option (a.Val M)
    | .many a => List (a.Val M)
    | .record fs => fs.Val M
  @[reducible] def Fields.Val {V : Vocabulary} (M : Model V) : Fields V → Type
    | .nil => Unit
    | .cons _ a rest => a.Val M × rest.Val M
end

namespace Fields

def append {V : Vocabulary} : Fields V → Fields V → Fields V
  | .nil, gs => gs
  | .cons name a rest, gs => .cons name a (rest.append gs)

def map {V : Vocabulary} (w : FTy V → FTy V) : Fields V → Fields V
  | .nil => .nil
  | .cons name a rest => .cons name (w a) (rest.map w)

end Fields

mutual
  /-- The values of a field are valid: a value as the model says, an option and a collection
  when what they have is, a record when its fields are. -/
  def FTy.Valid {V : Vocabulary} (M : Model V) : (a : FTy V) → a.Val M → Prop
    | .val τ, v => M.Valid τ v
    | .opt a, v => ∀ x, v = some x → FTy.Valid M a x
    | .many a, vs => ∀ x, x ∈ vs → FTy.Valid M a x
    | .record fs, vs => Fields.Valid M fs vs
  /-- The values of a record are valid. -/
  def Fields.Valid {V : Vocabulary} (M : Model V) : (fs : Fields V) → fs.Val M → Prop
    | .nil, _ => True
    | .cons _ a rest, (x, xs) => FTy.Valid M a x ∧ Fields.Valid M rest xs
end

/-- Two records agree at every field before the one with the name, each field as a whole
value: records, options and collections included. -/
def Fields.agreeBefore {V : Vocabulary} (M : Model V) (name : Label) :
    (fs : Fields V) → fs.Val M → fs.Val M → Prop
  | .nil, _, _ => True
  | .cons n _ rest, (x, xs), (y, ys) =>
      n = name ∨ (x = y ∧ Fields.agreeBefore M name rest xs ys)

/-- Two records differ at the field with the name. -/
def Fields.differAt {V : Vocabulary} (M : Model V) (name : Label) :
    (fs : Fields V) → fs.Val M → fs.Val M → Prop
  | .nil, _, _ => False
  | .cons n (.val _) rest, (x, xs), (y, ys) =>
      (n = name ∧ x ≠ y) ∨ (n ≠ name ∧ Fields.differAt M name rest xs ys)
  | .cons n _ rest, (_, xs), (_, ys) => n ≠ name ∧ Fields.differAt M name rest xs ys

/-- Two records fork at a field: they agree before it and differ at it. This is the restricted
fork of records: the target is a value field at the top of the record. The fork of two runs in
the order of their events is `Fork` on events. -/
def Fields.Fork {V : Vocabulary} (M : Model V) (name : Label) (fs : Fields V)
    (x y : fs.Val M) : Prop :=
  fs.agreeBefore M name x y ∧ fs.differAt M name x y

end Zkc.Core
