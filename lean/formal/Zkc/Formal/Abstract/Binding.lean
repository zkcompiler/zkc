module

@[expose] public section

/-! What the nominal types and the rows of a package are in an arithmetic.

A package names its nominal types and its operation rows by rows of the vocabulary. A binding
says, by position, which nominal type is the scalars and which the points, and which row is
which operation of the arithmetic. It is computed from the names of the package's rows
(`Zkc.Formal.Bls12381.bindingOf`), so no author writes one.
-/

set_option autoImplicit false

namespace Zkc.Formal

/-- What a nominal type of a package is in an arithmetic. -/
inductive Kind where
  | scalar
  | point
  | other
  deriving DecidableEq, Repr, Inhabited

/-- What a row of a package computes in an arithmetic. -/
inductive Row where
  | fieldAdd
  | fieldSub
  | fieldMul
  | fieldEqual
  | groupAdd
  | groupScale
  | groupEqual
  | seqSum
  | seqAdd
  | seqSub
  | seqScale
  | other
  deriving DecidableEq, Repr, Inhabited

/-- The kinds of the nominal types and of the rows of a package, by position. -/
structure Binding where
  types : List Kind
  rows : List Row
  deriving Repr, Inhabited

namespace Binding

/-- The kind of a nominal type; a type that the binding does not list is no scalar and no
point. -/
def kind (binding : Binding) (type : Nat) : Kind := binding.types.getD type .other

/-- What a row is; a row that the binding does not list is none of the arithmetic. -/
def row (binding : Binding) (index : Nat) : Row := binding.rows.getD index .other

end Binding

end Zkc.Formal
