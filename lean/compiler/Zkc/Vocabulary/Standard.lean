module

public import Zkc.Vocabulary.Keys

@[expose] public section

/-!
The vocabulary: the signature and the kind of each row at its key, the literals of each nominal
type, and the types that a law is uniform on.
-/

namespace Zkc.Vocabulary

open Zkc.Core (RowSignature LawSignature RowKind Tys)

/-- The signature of a pure row. -/
abbrev pure (ins outs : List Ty) : Option (RowSignature TypeKey RowKey) := some ⟨ins, outs, .pure⟩

/-- A row of a field at its key. -/
def fieldRow (field : Field) : FieldRow → Among → Option (RowSignature TypeKey RowKey)
  | .add, .all => pure [field.ty, field.ty] [field.ty]
  | .sub, .all => pure [field.ty, field.ty] [field.ty]
  | .mul, .all => pure [field.ty, field.ty] [field.ty]
  | .mul, .nonzero => pure [field.units, field.units] [field.units]
  | .neg, .all => pure [field.ty] [field.ty]
  | .neg, .nonzero => pure [field.units] [field.units]
  | .inverse, .nonzero => pure [field.units] [field.units]
  | .pow, .all => pure [field.ty, .nat] [field.ty]
  | .pow, .nonzero => pure [field.units, .nat] [field.units]
  | .equal, .all => pure [field.ty, field.ty] [.bool]
  | .isNonzero, .all => pure [field.ty] [.bool]
  | .nonzero, .all => some ⟨[field.ty], [field.units], .restricted (.field .isNonzero field .all)⟩
  | .fromNonzero, .nonzero => pure [field.units] [field.ty]
  | .fromNat, .all => pure [.nat] [field.ty]
  | .toNat, .all =>
      match field.over with
      | none => pure [field.ty] [.fin field.order]
      | some _ => none
  | .components, .all => pure [field.ty] [.seq field.prime.ty (some field.dimension)]
  | .fromComponents, .all => pure [.seq field.prime.ty (some field.dimension)] [field.ty]
  | .embed, among =>
      match field.over, among with
      | some (base, _), .all => pure [base.ty] [field.ty]
      | some (base, _), .nonzero => pure [base.units] [field.units]
      | none, _ => none
  | .coefficients, .all =>
      match field.over with
      | some (base, degree) => pure [field.ty] [.seq base.ty (some degree)]
      | none => none
  | .fromCoefficients, .all =>
      match field.over with
      | some (base, degree) => pure [.seq base.ty (some degree)] [field.ty]
      | none => none
  | .root, .all => pure [.fin (field.twoAdicity + 1)] [field.units]
  | _, _ => none

/-- A row of a group at a field or a group. -/
def groupRow (atom : Atom) : GroupRow → Option (RowSignature TypeKey RowKey)
  | .zero => pure [] [atom.ty]
  | .add => pure [atom.ty, atom.ty] [atom.ty]
  | .sub => pure [atom.ty, atom.ty] [atom.ty]
  | .neg => pure [atom.ty] [atom.ty]
  | .scale => pure [atom.ty, atom.scalar.ty] [atom.ty]
  | .equal => pure [atom.ty, atom.ty] [.bool]
  | .generator =>
      match atom with
      | .group .g1 => pure [] [atom.ty]
      | .group .g2 => pure [] [atom.ty]
      | _ => none

/-- A row of collections of an element, of a size or of any length. -/
def seqRow (item : Element) (size : Option Nat) : SeqRow → Option (RowSignature TypeKey RowKey)
  | .add => size.bind fun _ => pure [.seq item.ty size, .seq item.ty size] [.seq item.ty size]
  | .sub => size.bind fun _ => pure [.seq item.ty size, .seq item.ty size] [.seq item.ty size]
  | .scale => size.bind fun _ => pure [.seq item.ty size, item.scalar.ty] [.seq item.ty size]
  | .sum => pure [.seq item.ty size] [item.ty]
  | .product =>
      match item with
      | .atom (.field _) => pure [.seq item.ty size] [item.ty]
      | _ => none
  | .inner => size.bind fun _ => pure [.seq item.ty size, .seq item.scalar.ty size] [item.ty]
  | .equal => pure [.seq item.ty size, .seq item.ty size] [.bool]

/-- A hash of bytes. -/
def hashRow : Hash → Option (RowSignature TypeKey RowKey)
  | .sha256 => pure [.seq byte none] [.seq byte (some 32)]
  | .keccak256 => pure [.seq byte none] [.seq byte (some 32)]
  | .shake128 count => pure [.seq byte none] [.seq byte (some count)]
  | .shake256 count => pure [.seq byte none] [.seq byte (some count)]

/-- The signature and the kind of a row; none where the row has no instance. -/
def row : RowKey → Option (RowSignature TypeKey RowKey)
  | .field name field among => fieldRow field name among
  | .group name atom => groupRow atom name
  | .seq name item size => seqRow item size name
  | .hash hash => hashRow hash
  | .pair => pure [CurveGroup.g1.ty, CurveGroup.g2.ty] [CurveGroup.gt.ty]

/-- Whether a natural is a literal of a nominal type: of a field, a number below the
characteristic; of its elements that are not zero, such a number that is not zero; a group has
none. -/
def literal : TypeKey → Nat → Bool
  | .field field, n => decide (n < field.characteristic)
  | .nonzero field, n => decide (0 < n ∧ n < field.characteristic)
  | .group _, _ => false

mutual
  /-- A type is a law: it is finite and has a value. -/
  def isLaw : Ty → Bool
    | .bool => true
    | .nat => false
    | .fin bound => decide (0 < bound)
    | .seq item (some size) => size == 0 || isLaw item
    | .seq _ none => false
    | .tuple items => allLaws items
    | .record .. => false
    | .variant .. => false
    | .nominal .. => true
  /-- Every type is a law. -/
  def allLaws : Tys TypeKey → Bool
    | .nil => true
    | .cons head rest => isLaw head && allLaws rest
end

/-- The signature of a law: the uniform one, on a type that is a law. -/
def law : LawKey → Option (LawSignature TypeKey)
  | .uniform type => if isLaw type then some ⟨[], type⟩ else none

/-! ## The law of restricted rows -/

/-- A signature that `pure` gives is not restricted. -/
theorem pure_kind {ins outs : List Ty} {signature : RowSignature TypeKey RowKey} {domain : RowKey}
    (found : pure ins outs = some signature) (kind : signature.kind = .restricted domain) :
    False := by
  simp only [pure, Option.some.injEq] at found
  subst found
  cases kind

/-- The domain row of a restricted row is pure, has the same inputs and gives one truth value. -/
theorem decided (key : RowKey) (signature : RowSignature TypeKey RowKey) (domain : RowKey)
    (found : row key = some signature) (kind : signature.kind = .restricted domain) :
    row domain = some ⟨signature.ins, [.bool], .pure⟩ := by
  cases key with
  | field name field among =>
      simp only [row] at found
      cases name <;> cases among <;> simp only [fieldRow] at found <;>
        first
          | exact (pure_kind found kind).elim
          | (cases found; done)
          | (split at found <;> first | exact (pure_kind found kind).elim | cases found)
          | (cases found; cases kind; rfl)
  | group name atom =>
      simp only [row] at found
      cases name <;> simp only [groupRow] at found <;>
        first
          | exact (pure_kind found kind).elim
          | (split at found <;> first | exact (pure_kind found kind).elim | cases found)
  | seq name item size =>
      simp only [row] at found
      cases name <;> cases size <;> simp only [seqRow, Option.bind] at found <;>
        first
          | exact (pure_kind found kind).elim
          | cases found
          | (split at found <;> first | exact (pure_kind found kind).elim | cases found)
  | hash hash =>
      simp only [row] at found
      cases hash <;> exact (pure_kind found kind).elim
  | pair => exact (pure_kind found kind).elim

/-- The vocabulary. -/
def standard : Core.Vocabulary where
  TypeKey := TypeKey
  RowKey := RowKey
  LawKey := LawKey
  row := row
  law := law
  literal := literal
  decided := decided

end Zkc.Vocabulary

#print axioms Zkc.Vocabulary.decided
