module

public import Zkc.Core.Program.Vocabulary

@[expose] public section

namespace Zkc.Core

mutual
  /-- Change only the names of nominal types in a core type. -/
  def Ty.mapNominal {A B : Type} (f : A → B) : Ty A → Ty B
    | .bool => .bool
    | .nat => .nat
    | .fin n => .fin n
    | .seq item size => .seq (item.mapNominal f) size
    | .tuple items => .tuple (items.mapNominal f)
    | .record key linear fields => .record key linear (fields.mapNominal f)
    | .variant key alternatives => .variant key (alternatives.mapNominal f)
    | .nominal key => .nominal (f key)
  def Tys.mapNominal {A B : Type} (f : A → B) : Tys A → Tys B
    | .nil => .nil
    | .cons head tail => .cons (head.mapNominal f) (tail.mapNominal f)
end

/-- Project-declared pure primitives may consume both standard and project types.
The project supplies their closed signatures at semantic keys and a literal policy for its
own types. Standard operations, domains, and sampling laws keep their original owners. -/
structure PurePrimitives (V : Vocabulary) (T R : Type) where
  signature : R → Option (List (Ty (Sum V.TypeKey T)) × List (Ty (Sum V.TypeKey T)))
  literal : T → Nat → Bool := fun _ _ => false
  linear : T → Bool := fun _ => false

namespace PurePrimitives
variable {V : Vocabulary} {T R : Type}

abbrev baseType (type : V.Ty) : Ty (Sum V.TypeKey T) := type.mapNominal Sum.inl

def baseRow (sig : RowSignature V.TypeKey V.RowKey) : RowSignature (Sum V.TypeKey T) (Sum V.RowKey R) :=
  ⟨sig.ins.map baseType, sig.outs.map baseType, match sig.kind with
    | .pure => .pure
    | .restricted domain => .restricted (.inl domain)⟩

def row (primitives : PurePrimitives V T R) :
    Sum V.RowKey R → Option (RowSignature (Sum V.TypeKey T) (Sum V.RowKey R))
  | .inl k => (V.row k).map baseRow
  | .inr k => (primitives.signature k).map fun (ins, outs) => ⟨ins, outs, .pure⟩

/-- A restriction on a standard operation is still decided by its standard domain row
after linking. A project declaration cannot supply that domain or shadow the operation. -/
theorem decided (primitives : PurePrimitives V T R) (key sig domain)
    (present : primitives.row key = some sig) (restricted : sig.kind = .restricted domain) :
    primitives.row domain = some ⟨sig.ins, [.bool], .pure⟩ := by
  cases key with
  | inl k =>
    cases h : V.row k with
    | none => simp [row, h] at present
    | some original =>
      simp only [row, h, Option.map_some, Option.some.injEq] at present
      subst sig
      cases hk : original.kind with
      | pure => simp [baseRow, hk] at restricted
      | restricted d =>
        simp [baseRow, hk] at restricted
        subst domain
        simp [row, V.decided k original d h hk, baseRow, baseType, Ty.mapNominal]
  | inr k =>
    cases h : primitives.signature k with
    | none => simp [row, h] at present
    | some signature =>
      obtain ⟨ins, outs⟩ := signature
      simp only [row, h, Option.map_some, Option.some.injEq] at present
      subst sig
      cases restricted

/-- The vocabulary linked with the primitives. It is reducible, so that the types of its keys
are the types that it names to a tactic, which compares types without unfolding more: a key
written in a program is then a key of the vocabulary as it stands. -/
@[reducible] def vocabulary [DecidableEq T] [DecidableEq R] (primitives : PurePrimitives V T R) :
    Vocabulary where
  TypeKey := Sum V.TypeKey T
  RowKey := Sum V.RowKey R
  LawKey := V.LawKey
  row := primitives.row
  law k := (V.law k).map fun sig => ⟨sig.ins.map baseType, baseType sig.out⟩
  literal := Sum.elim V.literal primitives.literal
  linear := Sum.elim V.linear primitives.linear
  decided := primitives.decided

end PurePrimitives
end Zkc.Core
