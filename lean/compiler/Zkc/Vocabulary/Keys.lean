module

public import Zkc.Core.Program.Vocabulary

@[expose] public section

/-!
The keys of the vocabulary: which nominal type, which row and which law is meant.

A key says everything that tells one type, row or law from another: which field, which group,
at the elements of a field or at those that are not zero, the element and the size of a
collection, how many bytes a hash gives, the type that a law is uniform on. So a key has no
argument beside it, and a row that has no instance at a key has no signature there.
-/

namespace Zkc.Vocabulary

open Zkc.Core (Key)

/-! ## Fields and groups -/

/-- The fields. -/
inductive Field where
  /-- The prime field of order `2^31 - 2^24 + 1`. -/
  | koalaBear
  /-- Its extension of degree four. -/
  | koalaBear4
  /-- The scalar field of BLS12-381. -/
  | bls12381Fr
deriving DecidableEq, Repr

/-- The groups of BLS12-381. -/
inductive CurveGroup where
  | g1
  | g2
  | gt
deriving DecidableEq, Repr

namespace Field

/-- The characteristic. -/
def characteristic : Field → Nat
  | .koalaBear => 2130706433
  | .koalaBear4 => 2130706433
  | .bls12381Fr =>
      52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- The field that an extension is over, with its degree; none for a prime field. -/
def over : Field → Option (Field × Nat)
  | .koalaBear => none
  | .koalaBear4 => some (.koalaBear, 4)
  | .bls12381Fr => none

/-- The prime field. -/
def prime : Field → Field
  | .koalaBear => .koalaBear
  | .koalaBear4 => .koalaBear
  | .bls12381Fr => .bls12381Fr

/-- The dimension over the prime field. -/
def dimension : Field → Nat
  | .koalaBear => 1
  | .koalaBear4 => 4
  | .bls12381Fr => 1

/-- The number of elements. -/
def order (field : Field) : Nat := field.characteristic ^ field.dimension

/-- The largest `k` with a root of unity of order `2^k`. -/
def twoAdicity : Field → Nat
  | .koalaBear => 24
  | .koalaBear4 => 26
  | .bls12381Fr => 32

end Field

/-! ## Types -/

/-- The nominal types. -/
inductive TypeKey where
  /-- The elements of a field. -/
  | field (field : Field)
  /-- The elements of a field that are not zero. -/
  | nonzero (field : Field)
  /-- The elements of a group. -/
  | group (group : CurveGroup)
deriving DecidableEq, Repr

/-- The types over the vocabulary's nominal types. -/
abbrev Ty : Type := Core.Ty TypeKey

/-- The type of a field's elements. -/
def Field.ty (field : Field) : Ty := .nominal (.field field)

/-- The type of a field's elements that are not zero. -/
def Field.units (field : Field) : Ty := .nominal (.nonzero field)

/-- The type of a group's elements. -/
def CurveGroup.ty (group : CurveGroup) : Ty := .nominal (.group group)

/-- A byte. -/
abbrev byte : Ty := .fin 256

/-- A type whose values are added and scaled: a field or a group. -/
inductive Atom where
  | field (field : Field)
  | group (group : CurveGroup)
deriving DecidableEq, Repr

/-- The type. -/
def Atom.ty : Atom → Ty
  | .field f => f.ty
  | .group g => g.ty

/-- The field of the scalars: a field's own, a group's scalar field. -/
def Atom.scalar : Atom → Field
  | .field f => f
  | .group _ => .bls12381Fr

/-- The element of a collection that a row of collections is at: a field, a group, or a sized
collection of such elements. -/
inductive Element where
  | atom (atom : Atom)
  | sized (item : Element) (size : Nat)
deriving DecidableEq, Repr

/-- The type. -/
def Element.ty : Element → Ty
  | .atom a => a.ty
  | .sized item size => .seq item.ty (some size)

/-- The field of the scalars of an element. -/
def Element.scalar : Element → Field
  | .atom a => a.scalar
  | .sized item _ => item.scalar

/-! ## Rows -/

/-- Whether a row of a field is at its elements or at those that are not zero. -/
inductive Among where
  | all
  | nonzero
deriving DecidableEq, Repr

/-- The rows of a field. -/
inductive FieldRow where
  | add | sub | mul | neg | inverse | pow | equal
  /-- Whether an element is not zero: the domain row of `nonzero`. -/
  | isNonzero
  /-- An element that is not zero, as one: restricted to those. -/
  | nonzero
  /-- An element that is not zero, as an element. -/
  | fromNonzero
  | fromNat | toNat | components | fromComponents
  | embed | coefficients | fromCoefficients
  | root
deriving DecidableEq, Repr

/-- The rows of a group, and of a field as a group. -/
inductive GroupRow where
  | zero | add | sub | neg | scale | equal | generator
deriving DecidableEq, Repr

/-- The rows of collections. -/
inductive SeqRow where
  | add | sub | scale | sum | product | inner | equal
deriving DecidableEq, Repr

/-- The hashes of bytes; an extendable one with the number of bytes that it gives. -/
inductive Hash where
  | sha256
  | keccak256
  | shake128 (count : Nat)
  | shake256 (count : Nat)
deriving DecidableEq, Repr

/-- The rows. -/
inductive RowKey where
  | field (row : FieldRow) (field : Field) (among : Among)
  | group (row : GroupRow) (atom : Atom)
  /-- A row of collections of an element: of a size, or of any length. -/
  | seq (row : SeqRow) (item : Element) (size : Option Nat)
  | hash (hash : Hash)
  /-- The pairing of BLS12-381. -/
  | pair
deriving DecidableEq, Repr

/-! ## Laws -/

/-- The sampling laws: the uniform one on a type. -/
inductive LawKey where
  | uniform (type : Ty)
deriving DecidableEq

end Zkc.Vocabulary
