module

@[expose] public section

/-! Typed public-value binding events.

A host binds a statement before the first request. Its typed public-value
binding event (`PublicBinding Scalar`) is the application context with a row of
the statement's public values, each labelled by its input (`Row Scalar`). A
public value (`PublicValue Scalar`) is a scalar, a vector whose length is part
of the value, an index with its bound, or a count. Equal events have equal rows
by constructor injectivity, so a count is never confused with a vector's
length, nor a vector with another's prefix.

These are binding representations: an index is not required to lie below its
bound, and a row is not required to be in canonical order. Validity and
canonical order are established separately, by the statement's own checks and
by the codec that builds the row; keeping malformed values representable is
what lets a codec bind every statement a prover can output. The construction
model's transcript events embed these events (`Zkc.Construction.Event`), and
`ZkcSecurity.FiatShamir.Binding` derives statement determination from them.
-/

set_option autoImplicit false

namespace Zkc.Construction

mutual
  /-- A typed public value a statement binds. -/
  inductive PublicValue (Scalar : Type) where
    /-- One scalar, a field or group element. -/
    | scalar (value : Scalar)
    /-- A vector of scalars; its length is part of the value. -/
    | vector (values : List Scalar)
    /-- An index with its bound. The representation does not require `value < bound`;
    validity is established separately. -/
    | index (bound value : Nat)
    /-- A count, such as a number of rounds. -/
    | count (value : Nat)
    /-- Ordered logical elements; this is not a canonical byte encoding. -/
    | sequence (values : PublicValues Scalar)
    /-- Nominal identity, constructor and ordered components are all retained. -/
    | product (identity constructor : String) (components : PublicValues Scalar)
    deriving DecidableEq, Repr

  /-- A heterogeneous logical component list, mutually defined to retain exact equality. -/
  inductive PublicValues (Scalar : Type) where
    | nil
    | cons (head : PublicValue Scalar) (tail : PublicValues Scalar)
    deriving DecidableEq, Repr
end

def PublicValues.ofList {Scalar : Type} : List (PublicValue Scalar) → PublicValues Scalar
  | [] => .nil
  | value :: values => .cons value (ofList values)

theorem PublicValues.ofList_injective {Scalar : Type} :
    Function.Injective (PublicValues.ofList (Scalar := Scalar)) := by
  intro first second same
  induction first generalizing second with
  | nil => cases second <;> simp_all [ofList]
  | cons value values ih =>
    cases second with
    | nil => simp [ofList] at same
    | cons other others =>
      have parts := PublicValues.cons.inj same
      have head := parts.1
      have tail := ih parts.2
      cases head
      cases tail
      rfl

/-- A row: the statement's public values, each labelled by its input. The type
does not enforce an order; the codec that builds a row from a statement
establishes the canonical one. -/
abbrev Row (Scalar : Type) := List (String × PublicValue Scalar)

/-- The typed public-value binding event: the application context and a row of
the statement's public values. -/
structure PublicBinding (Scalar : Type) where
  context : String
  row : Row Scalar
  deriving DecidableEq, Repr

end Zkc.Construction
