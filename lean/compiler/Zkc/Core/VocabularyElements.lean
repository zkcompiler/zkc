module

public import Zkc.Core.Vocabulary
public import Zkc.Core.Concrete

@[expose] public section

/-! The arithmetic of the element types of the vocabulary.

What the values of a type are and how they are computed is read from the vocabulary's entry for
the type, never from its name alone:

- a type whose arithmetic is a prime field is the naturals below its `Order`: one
  implementation for `koala-bear` and `bls12-381.fr`, an element a number;
- an extension is the polynomials over its `Base`, a prime field, modulo
  `x^Degree - nonresidue`: an element is its `Degree` coefficients, lowest first;
- `bls12-381.g1` is the group of `Concrete`: a point is its two coordinates, or no datum for
  the point at infinity; its scalar acts by its natural below the order.
-/

set_option autoImplicit false

namespace Zkc.Core.Vocabulary

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-! ## Arithmetic -/

/-- `base ^ exponent` modulo `modulus`, by squaring, one bit of the exponent per step. -/
def powerModulo (base exponent modulus : Nat) : Nat :=
  go (exponent.log2 + 1) (base % modulus) exponent (1 % modulus)
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, _, result => result
    | steps + 1, square, remaining, result =>
      let result := if remaining % 2 == 1 then result * square % modulus else result
      go steps (square * square % modulus) (remaining / 2) result

/-- How the values of a type are computed. -/
inductive Element where
  | prime (order : Nat)
  /-- Polynomials over the prime field of `base` modulo `x^degree - nonresidue`. -/
  | extension (base degree nonresidue : Nat)
  | curve
  deriving Repr, Inhabited, BEq

/-- The element arithmetic of a closed type, read from its entry. -/
def elementOf (table : Table) : Closed → Option Element
  | .nonzero field => elementOf table field
  | .row name => do
    let entry ← table.type? name
    match entry.arithmetic with
    | .primeField =>
      let (_, order) ← entry.naturalMembers.find? (·.1 == "Order")
      return .prime order
    | .extension nonresidue =>
      let (_, degree) ← entry.naturalMembers.find? (·.1 == "Degree")
      let (_, base) ← entry.typeMembers.find? (·.1 == "Base")
      let .row baseName := base | none
      let baseEntry ← table.type? baseName
      unless baseEntry.arithmetic == .primeField do none
      let (_, order) ← baseEntry.naturalMembers.find? (·.1 == "Order")
      return .extension order degree nonresidue
    | .curveG1 => return .curve
    | .none => none
  | _ => none

namespace Extension

/-- The coefficients of an element: `degree` numbers. -/
def coefficients (degree : Nat) (datum : Datum) : List Nat :=
  let items := datum.items.map Datum.toNat
  (List.range degree).map fun index => items.getD index 0

def ofCoefficients (values : List Nat) : Datum := .sequence (values.map .number)

def add (order : Nat) (a b : List Nat) : List Nat := (a.zip b).map fun (x, y) => (x + y) % order

def neg (order : Nat) (a : List Nat) : List Nat := a.map fun x => (order - x % order) % order

/-- The product modulo `x^degree - nonresidue`: a term `x^(degree + i)` is `nonresidue · x^i`. -/
def mul (order degree nonresidue : Nat) (a b : List Nat) : List Nat := Id.run do
  let mut product : Array Nat := Array.replicate (2 * degree) 0
  for i in [0:degree] do
    for j in [0:degree] do
      product := product.modify (i + j) (· + a.getD i 0 * b.getD j 0)
  return (List.range degree).map fun i =>
    (product[i]! + nonresidue * product[i + degree]!) % order

def one (degree : Nat) : List Nat := (List.range degree).map fun i => if i == 0 then 1 else 0

/-- A power by squaring. -/
def pow (order degree nonresidue : Nat) (base : List Nat) (exponent : Nat) : List Nat :=
  go (exponent.log2 + 1) base exponent (one degree)
where
  go : Nat → List Nat → Nat → List Nat → List Nat
    | 0, _, _, result => result
    | steps + 1, square, remaining, result =>
      let result := if remaining % 2 == 1 then mul order degree nonresidue result square else result
      go steps (mul order degree nonresidue square square) (remaining / 2) result

end Extension

/-- The zero of an element type. -/
def Element.zero : Element → Datum
  | .prime _ => .number 0
  | .extension _ degree _ => Extension.ofCoefficients ((List.range degree).map fun _ => 0)
  | .curve => Datum.ofPoint none

/-- The image of a natural in a field. -/
def Element.ofNat : Element → Nat → Datum
  | .prime order, value => .number (value % order)
  | .extension order degree _, value =>
    Extension.ofCoefficients ((List.range degree).map fun i => if i == 0 then value % order else 0)
  | .curve, _ => Datum.ofPoint none

/-- The negation of the BLS12-381 G1 point. -/
def negatePoint : Concrete.Point → Concrete.Point
  | none => none
  | some (x, y) => some (x, (Concrete.baseModulus - y) % Concrete.baseModulus)

def Element.add : Element → Datum → Datum → Datum
  | .prime order, a, b => .number ((a.toNat + b.toNat) % order)
  | .extension order degree _, a, b =>
    Extension.ofCoefficients (Extension.add order (Extension.coefficients degree a)
      (Extension.coefficients degree b))
  | .curve, a, b => Datum.ofPoint (Concrete.addPoints a.toPoint b.toPoint)

def Element.neg : Element → Datum → Datum
  | .prime order, a => .number ((order - a.toNat % order) % order)
  | .extension order degree _, a =>
    Extension.ofCoefficients (Extension.neg order (Extension.coefficients degree a))
  | .curve, a => Datum.ofPoint (negatePoint a.toPoint)

def Element.sub (element : Element) (a b : Datum) : Datum := element.add a (element.neg b)

/-- The product of two field elements; for the group, nothing. -/
def Element.mul : Element → Datum → Datum → Datum
  | .prime order, a, b => .number (a.toNat * b.toNat % order)
  | .extension order degree nonresidue, a, b =>
    Extension.ofCoefficients (Extension.mul order degree nonresidue
      (Extension.coefficients degree a) (Extension.coefficients degree b))
  | .curve, _, _ => Datum.ofPoint none

def Element.pow : Element → Datum → Nat → Datum
  | .prime order, a, exponent => .number (powerModulo a.toNat exponent order)
  | .extension order degree nonresidue, a, exponent =>
    Extension.ofCoefficients (Extension.pow order degree nonresidue
      (Extension.coefficients degree a) exponent)
  | .curve, a, _ => a

/-- The inverse of a nonzero field element: its power to the order of the field less 2. -/
def Element.inverse : Element → Datum → Datum
  | .prime order, a => .number (powerModulo a.toNat (order - 2) order)
  | .extension order degree nonresidue, a =>
    Extension.ofCoefficients (Extension.pow order degree nonresidue
      (Extension.coefficients degree a) (order ^ degree - 2))
  | .curve, a => a

/-- The action of a scalar, given by its natural. -/
def Element.scale (element : Element) (a : Datum) (scalar : Datum) : Datum :=
  match element with
  | .curve => Datum.ofPoint (Concrete.scalePoint a.toPoint (scalar.toNat % Concrete.scalarModulus))
  | field => field.mul a scalar

def Element.isZero (element : Element) (a : Datum) : Bool := element.add a (element.zero) == element.zero

def Element.equal (element : Element) (a b : Datum) : Bool :=
  match element with
  | .curve => a.toPoint == b.toPoint
  | field => field.isZero (field.sub a b)

/-- Whether a point is of the group G1: on the curve, with coordinates below the characteristic
of the base field, and of an order that divides the order of the group. -/
def inGroup (point : Concrete.Point) : Bool :=
  Concrete.onCurve point && Concrete.scalePoint point Concrete.scalarModulus == none

/-- Whether a datum is a value of the element type: a number below the order of a prime field,
as many such numbers as the degree of an extension, a point of the group G1. -/
def Element.valid : Element → Datum → Bool
  | .prime order, .number value => value < order
  | .extension order degree _, .sequence items =>
    items.length == degree && items.all fun
      | .number value => value < order
      | .sequence _ => false
  | .curve, datum => match datum with
    | .sequence [] => true
    | .sequence [.number _, .number _] => inGroup datum.toPoint
    | _ => false
  | _, _ => false

end Zkc.Core.Vocabulary
