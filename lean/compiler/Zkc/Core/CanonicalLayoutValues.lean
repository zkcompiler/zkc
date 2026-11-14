module

public import Zkc.Core.CanonicalLayoutLaws

public section

/-! The values that the canonical layout writes.

Under the laws of the canonical layout (`Layout.Canonical.laws`) a value is writable when the
layout writes it (`writes`): its type has a format and its datum is of the domain of the
format. The serialize step asks that every value that the prover sends is writable. This
module says what that is for the types that messages have, and which values that the rows of
the model compute are writable.

- `writes_bool`, `writes_nat`, `writes_index`: every `bool`, every `nat` and every index is
  written.
- `writes_prime`: of a prime field of the vocabulary the layout writes the elements, the
  numbers below the order. `writes_point`: of the group G1 it writes the data that are points
  of the group.
- The carrier of a nominal type is every datum, so a value of the type of a field or of the
  group need not be written: the order of a prime field is a value of its type that is not
  (`writes_prime_order`). That every value that a protocol sends is writable is a property of
  the protocol and of its inputs, and typing does not give it.
- A row of the arithmetic of a prime field (`elementRows`) gives an element, whatever data it
  is given: its result is reduced modulo the order (`apply_arithmetic_valid`). So in the model
  of a package a value that such a row returns is written (`model_arithmetic_writes`), and so
  is the value of a literal of a prime field (`literal_writes`).

- The row `group.scale` of the group G1 gives the multiple of a point (`model_scale_point`),
  and the layout writes it exactly when it is a point of the group (`model_scale_writes`).

Nothing here says that a sum or a multiple of points of the group is of the group: that is a
fact of the arithmetic of the curve, which this package does not prove. So that a protocol
sends only writable points is an obligation of the protocol with that fact as its premise:
`GroupClosedUnderMultiples` names the fact for multiples, and with it the layout writes the
multiple that `group.scale` gives of a point of the group (`model_scale_writes_of_group`). A
value that a protocol sends as it received it (an input of the entry, a reply of a sampler) is
written when the input or the reply is a value of its type in the sense of `validInput`; the
model does not constrain either.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-! ## What the layout writes of a type -/

namespace Vocabulary

theorem closedOf_bool (types : Array CatalogueRow) : closedOf types .bool = some .bool := by
  simp [closedOf, typeParts, closedOf.go]

theorem closedOf_nat (types : Array CatalogueRow) : closedOf types .nat = some .nat := by
  simp [closedOf, typeParts, closedOf.go]

theorem closedOf_fin (types : Array CatalogueRow) (bound : Nat) :
    closedOf types (.fin bound) = some (.index bound) := by
  simp [closedOf, typeParts, closedOf.go]

/-- The layout writes every `bool`. -/
theorem writes_bool (table : Table) (package : Raw.Package) (value : Bool) :
    writes table package .bool value = true := by
  simp only [writes, messageFormat, closedOf_bool, Option.bind_some, formatOf, numbers,
    Format.through, Concrete.toDatum, Datum.ofBool, asNumber, Format.below_domain]
  cases value <;> rfl

/-- The layout writes every `nat`. -/
theorem writes_nat (table : Table) (package : Raw.Package) (value : Nat) :
    writes table package .nat value = true := by
  simp only [writes, messageFormat, closedOf_nat, Option.bind_some, formatOf, numbers,
    Format.through, Concrete.toDatum, asNumber, Format.natural]

/-- The layout writes every index. -/
theorem writes_index (table : Table) (package : Raw.Package) (bound : Nat) (value : Fin bound) :
    writes table package (.fin bound) value = true := by
  simp only [writes, messageFormat, closedOf_fin, Option.bind_some, formatOf, numbers,
    Format.through, Concrete.toDatum, asNumber, Format.below_domain, value.isLt, decide_true]

/-- A leaf that is a prime field: the arithmetic of its type is that of the naturals below
the order, and its width holds the order. -/
theorem leafOf_prime {table : Table} {name : String} {order width : Nat}
    (leaf : leafOf table name = some (.prime order width)) :
    elementOf table (.row name) = some (.prime order) ∧ order ≤ 256 ^ width := by
  unfold leafOf at leaf
  split at leaf
  · rename_i found element
    split at leaf
    · split at leaf
      · rename_i holds
        cases leaf
        exact ⟨element, holds⟩
      · cases leaf
    · cases leaf
  · split at leaf
    · split at leaf <;> cases leaf
    · cases leaf
  · cases leaf
  · cases leaf

/-- A datum is an element of a prime field exactly when it is a number below the order. -/
theorem prime_valid_iff {order : Nat} {value : Datum} :
    (Element.prime order).valid value = true ↔
      ∃ number, value = .number number ∧ number < order := by
  cases value with
  | number found => simp [Element.valid]
  | sequence items => simp [Element.valid]

/-- What the layout writes of a prime field of the vocabulary: the elements, the numbers below
the order. -/
theorem writes_prime {table : Table} {package : Raw.Package} {row : Nat} {name : String}
    {order width : Nat}
    (closedIs : closedOf package.types.toArray (.nominal row) = some (.row name))
    (leaf : leafOf table name = some (.prime order width)) (value : Datum) :
    writes table package (.nominal row) value = (Element.prime order).valid value := by
  have holds := (leafOf_prime leaf).2
  simp only [writes, messageFormat, closedIs, Option.bind_some, formatOf, leaf, Leaf.format,
    numbers, Format.through, Concrete.toDatum, Format.number]
  cases value with
  | number found =>
    simp only [asNumber, Element.valid]
    by_cases below : found < order
    · have fits : found < 256 ^ width := by omega
      simp [below, fits]
    · simp [below]
  | sequence items => rfl

/-- The order of a prime field is a datum that the layout does not write: a value of the
carrier of the field that is no element. -/
theorem writes_prime_order {table : Table} {package : Raw.Package} {row : Nat} {name : String}
    {order width : Nat}
    (closedIs : closedOf package.types.toArray (.nominal row) = some (.row name))
    (leaf : leafOf table name = some (.prime order width)) :
    writes table package (.nominal row) (Datum.number order) = false := by
  rw [writes_prime closedIs leaf]
  simp [Element.valid]

/-- What the layout writes of the group G1: the data that are points of the group. -/
theorem writes_point {table : Table} {package : Raw.Package} {row : Nat} {name : String}
    (closedIs : closedOf package.types.toArray (.nominal row) = some (.row name))
    (leaf : leafOf table name = some .curve) (value : Datum) :
    writes table package (.nominal row) value =
      match asPoint value with
      | some point => inGroup point
      | none => false := by
  simp only [writes, messageFormat, closedIs, Option.bind_some, formatOf, leaf, Leaf.format,
    Format.through, Concrete.toDatum, pointFormat]
  cases asPoint value <;> rfl

/-! ## The values that the arithmetic of a prime field gives -/

/-- A step of the power by squaring keeps its result below the modulus. -/
private theorem powerModulo_go_lt {modulus : Nat} (positive : 0 < modulus) :
    ∀ (steps square remaining result : Nat), result < modulus →
      powerModulo.go modulus steps square remaining result < modulus
  | 0, _, _, _, below => below
  | steps + 1, square, remaining, result, below => by
    unfold powerModulo.go
    apply powerModulo_go_lt positive
    split
    · exact Nat.mod_lt _ positive
    · exact below

/-- A power modulo a positive modulus is below the modulus. -/
theorem powerModulo_lt (base exponent : Nat) {modulus : Nat} (positive : 0 < modulus) :
    powerModulo base exponent modulus < modulus :=
  powerModulo_go_lt positive _ _ _ _ (Nat.mod_lt _ positive)

/-- The rows of the arithmetic of an element type that give one element of the type. -/
@[expose] def elementRows : List String :=
  ["field.add", "field.sub", "field.mul", "field.neg", "field.pow", "field.inverse",
    "field.from_nat", "group.zero", "group.add", "group.sub", "group.neg", "group.scale",
    "ring.mul", "ring.pow"]

/-- A row of the arithmetic of a prime field with a positive order gives one element of the
field, a number below the order, whatever data it is given. -/
theorem apply_arithmetic_valid {table : Table} {name : String} {closed : Closed} {order : Nat}
    (arithmetic : name ∈ elementRows) (element : elementOf table closed = some (.prime order))
    (positive : 0 < order) {inputs results : List Datum}
    (applied : apply table name [.type closed] inputs = .ok results) :
    ∃ result, results = [result] ∧ (Element.prime order).valid result = true := by
  have reads : (typeArgument [Value.type closed] 0).bind (elementOf table) =
      some (.prime order) := by
    simp [typeArgument, element]
  simp only [elementRows, List.mem_cons, List.not_mem_nil, or_false] at arithmetic
  unfold apply at applied
  simp only [reads, bind, Except.bind, pure, Except.pure] at applied
  split at applied
  · rename_i isNonzero
    subst isNonzero
    exact absurd arithmetic (by decide)
  split at applied
  · rename_i isNonzero
    subst isNonzero
    exact absurd arithmetic (by decide)
  split at applied
  all_goals first
    | exact absurd arithmetic (by decide)
    | cases applied
  all_goals
    exact ⟨_, rfl, by
      simp [Element.valid, Element.add, Element.sub, Element.neg, Element.mul, Element.pow,
        Element.inverse, Element.zero, Element.scale, Element.ofNat, Nat.mod_lt _ positive,
        powerModulo_lt _ _ positive, positive]⟩

/-! ## The values that the rows of the model give -/

/-- No row of the arithmetic of an element type has the name of a row of a suite. -/
private theorem arithmetic_not_suite {name : String} (arithmetic : name ∈ elementRows)
    (member : String)
    (differs : (elementRows.all fun row =>
      Vocabulary.table.modules.all fun entry => row != entry.row ++ "." ++ member) = true) :
    merlinSuite? Vocabulary.table name member = none :=
  merlinSuite?_none name member (List.all_eq_true.mp differs name arithmetic)

/-- A row of the arithmetic of an element type is computed by the arithmetic of the type: no
row of a suite, of the layout or of a hash has its name. -/
private theorem applyRow_arithmetic {name : String} (arithmetic : name ∈ elementRows)
    (arguments : List Value) (inputs : List Datum) :
    applyRow Vocabulary.table name arguments inputs =
      apply Vocabulary.table name arguments inputs := by
  have start := arithmetic_not_suite arithmetic "start" (by decide +kernel)
  have absorb := arithmetic_not_suite arithmetic "absorb" (by decide +kernel)
  have derive := arithmetic_not_suite arithmetic "derive" (by decide +kernel)
  have other : name ≠ "layout.canonical.take" := by
    rintro rfl
    exact absurd arithmetic (by decide)
  have none : applyBytes Vocabulary.table name arguments inputs = none := by
    unfold applyBytes applyWritten
    simp only [other, start, derive, absorb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    split <;> first | rfl | exact absurd arithmetic (by decide)
  unfold applyRow
  simp only [none]
  split <;> first | rfl | exact absurd arithmetic (by decide)

/-- In the model of a package, a row of the arithmetic of a prime field with a positive order
gives an element of the field, whatever values it is given. -/
theorem model_arithmetic_valid {package : Raw.Package} {row : Nat} {operation : Operation}
    {name : String} {closed : Closed} {order : Nat}
    (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = name) (arithmetic : name ∈ elementRows)
    (read : argumentsOf package.types.toArray operation.identity = some [.type closed])
    (element : elementOf Vocabulary.table closed = some (.prime order)) (positive : 0 < order)
    {inputs : List Ty} {output : Nat} (populated : Ty.allPopulated [.nominal output] = true)
    (arguments : Values Concrete.Value inputs) :
    (Element.prime order).valid
      (((model Vocabulary.table package).pure ⟨row, inputs, [.nominal output]⟩ populated
        arguments).get .here) = true := by
  rw [model_pure Vocabulary.table package row inputs [.nominal output] populated arguments found,
    applyOperation_read _ read, named, applyRow_arithmetic arithmetic]
  cases applied : apply Vocabulary.table name [.type closed]
      (Concrete.toData inputs arguments) with
  | error failure =>
    show (Element.prime order).valid (Datum.number 0) = true
    simp [Element.valid, positive]
  | ok results =>
    obtain ⟨result, rfl, valid⟩ := apply_arithmetic_valid arithmetic element positive applied
    show (Element.prime order).valid
      (((Concrete.ofData [.nominal output] [result]).getD _).get .here) = true
    rw [Concrete.ofData_nominal]
    exact valid

/-- In the model of a package, the layout writes the value that a row of the arithmetic of a
prime field with a positive order gives, whatever values the row is given. -/
theorem model_arithmetic_writes {package : Raw.Package} {row output : Nat} {operation : Operation}
    {name field : String} {order width : Nat}
    (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = name) (arithmetic : name ∈ elementRows)
    (read : argumentsOf package.types.toArray operation.identity = some [.type (.row field)])
    (closedIs : closedOf package.types.toArray (.nominal output) = some (.row field))
    (leaf : leafOf Vocabulary.table field = some (.prime order width)) (positive : 0 < order)
    {inputs : List Ty} (populated : Ty.allPopulated [.nominal output] = true)
    (arguments : Values Concrete.Value inputs) :
    writes Vocabulary.table package (.nominal output)
      (((model Vocabulary.table package).pure ⟨row, inputs, [.nominal output]⟩ populated
        arguments).get .here) = true := by
  exact (writes_prime closedIs leaf _).trans
    (model_arithmetic_valid found named arithmetic read (leafOf_prime leaf).1 positive populated
      arguments)

/-- In the model of a package, the layout writes the value of a literal of a prime field with
a positive order: the literal is read modulo the order. -/
theorem literal_writes {package : Raw.Package} {row : Nat} {field : String} {order width : Nat}
    (closedIs : closedOf package.types.toArray (.nominal row) = some (.row field))
    (leaf : leafOf Vocabulary.table field = some (.prime order width)) (positive : 0 < order)
    (data : List Nat) :
    writes Vocabulary.table package (.nominal row)
      ((model Vocabulary.table package).literal row data) = true := by
  have valid : (Element.prime order).valid
      (literalDatum Vocabulary.table package.types.toArray row data) = true := by
    simp [literalDatum, closedIs, (leafOf_prime leaf).1, Element.ofNat, Element.valid,
      Nat.mod_lt _ positive]
  exact (writes_prime closedIs leaf _).trans valid

/-! ## The multiple of a point that the row of the group gives -/

/-- A leaf that is the group G1: the arithmetic of its type is that of the curve. -/
theorem leafOf_curve {table : Table} {name : String} (leaf : leafOf table name = some .curve) :
    elementOf table (.row name) = some .curve := by
  unfold leafOf at leaf
  split at leaf
  · split at leaf
    · split at leaf <;> cases leaf
    · cases leaf
  · split at leaf
    · split at leaf <;> cases leaf
    · cases leaf
  · rename_i element
    exact element
  · cases leaf

/-- The row `group.scale` of the group G1 on two data gives the multiple of the point that
the first is, by the number that the second is, reduced modulo the order of the group. -/
theorem apply_scale_point {table : Table} {name : String} {closed : Closed}
    (named : name = "group.scale") (element : elementOf table closed = some .curve)
    (point multiplier : Datum) :
    apply table name [.type closed] [point, multiplier] =
      .ok [Datum.ofPoint
        (Concrete.scalePoint point.toPoint (multiplier.toNat % Concrete.scalarModulus))] := by
  have reads : (typeArgument [Value.type closed] 0).bind (elementOf table) = some .curve := by
    simp [typeArgument, element]
  unfold apply
  simp only [reads, bind, Except.bind, pure, Except.pure]
  split
  · rename_i isNonzero
    exact absurd (isNonzero.symm.trans named) (by decide)
  split
  · rename_i isNonzero
    exact absurd (isNonzero.symm.trans named) (by decide)
  split
  all_goals first
    | exact absurd named (by decide)
    | (injections
       subst_vars
       rfl)
    | exact absurd rfl
        ((by assumption : ∀ (a s : Datum), _ = "group.scale" → [point, multiplier] = [a, s] →
          False) point multiplier named)

/-- In the model of a package, the row `group.scale` of the group G1 gives the multiple of the
point that its first input is, by the number that its second input is, reduced modulo the
order of the group. -/
theorem model_scale_point {package : Raw.Package} {row : Nat} {operation : Operation}
    {closed : Closed} (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "group.scale")
    (read : argumentsOf package.types.toArray operation.identity = some [.type closed])
    (element : elementOf Vocabulary.table closed = some .curve) {base scalar : Ty} {output : Nat}
    (populated : Ty.allPopulated [.nominal output] = true)
    (arguments : Values Concrete.Value [base, scalar]) :
    ((model Vocabulary.table package).pure ⟨row, [base, scalar], [.nominal output]⟩ populated
      arguments).get .here =
        Datum.ofPoint (Concrete.scalePoint (Concrete.toDatum base (arguments.get .here)).toPoint
          ((Concrete.toDatum scalar (arguments.tail.get .here)).toNat %
            Concrete.scalarModulus)) := by
  rw [model_pure Vocabulary.table package row [base, scalar] [.nominal output] populated
    arguments found, applyOperation_read _ read, named, applyRow_arithmetic (by decide)]
  have data : Concrete.toData [base, scalar] arguments =
      [Concrete.toDatum base (arguments.get .here),
        Concrete.toDatum scalar (arguments.tail.get .here)] := rfl
  rw [data, apply_scale_point rfl element]
  show ((Concrete.ofData [.nominal output] [_]).getD _).get .here = _
  rw [Concrete.ofData_nominal]
  rfl

/-- In the model of a package, the layout writes the multiple that the row `group.scale` of
the group G1 gives exactly when the multiple is a point of the group. That a multiple of a
point of the group is of the group is a fact of the arithmetic of the curve, which this
package does not prove. -/
theorem model_scale_writes {package : Raw.Package} {row output : Nat} {operation : Operation}
    {group : String} (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "group.scale")
    (read : argumentsOf package.types.toArray operation.identity = some [.type (.row group)])
    (closedIs : closedOf package.types.toArray (.nominal output) = some (.row group))
    (leaf : leafOf Vocabulary.table group = some .curve) {base scalar : Ty}
    (populated : Ty.allPopulated [.nominal output] = true)
    (arguments : Values Concrete.Value [base, scalar]) :
    writes Vocabulary.table package (.nominal output)
      (((model Vocabulary.table package).pure ⟨row, [base, scalar], [.nominal output]⟩ populated
        arguments).get .here) =
      inGroup (Concrete.scalePoint (Concrete.toDatum base (arguments.get .here)).toPoint
        ((Concrete.toDatum scalar (arguments.tail.get .here)).toNat %
          Concrete.scalarModulus)) := by
  refine (writes_point closedIs leaf _).trans ?_
  rw [model_scale_point found named read (leafOf_curve leaf) populated arguments,
    views_point.view_image]

/-- What the statements about a protocol that sends a multiple of a point take as a hypothesis
of the group G1: a multiple of a point of the group is a point of the group. It says that the
multiple is on the curve and that the order of the group times the multiple is the point at
infinity: the sum of two points of the curve is on the curve, and the multiples of a point
commute. These are facts of the arithmetic of the curve, which this package, without a
mathematics library, does not prove. Multiples of the generator that the kernel computes are
its executable check. -/
structure GroupClosedUnderMultiples : Prop where
  multiple_inGroup : ∀ (point : Concrete.Point) (multiplier : Nat), inGroup point = true →
    inGroup (Concrete.scalePoint point multiplier) = true

/-- In the model of a package, the layout writes the multiple that the row `group.scale` of the
group G1 gives of a datum that is a point of the group, whatever the multiplier, when the
multiples of a point of the group are of the group. A datum that is no point is read as the
point at infinity (`Datum.toPoint`). -/
theorem model_scale_writes_of_group (closed : GroupClosedUnderMultiples) {package : Raw.Package}
    {row output : Nat} {operation : Operation} {group : String}
    (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "group.scale")
    (read : argumentsOf package.types.toArray operation.identity = some [.type (.row group)])
    (closedIs : closedOf package.types.toArray (.nominal output) = some (.row group))
    (leaf : leafOf Vocabulary.table group = some .curve) {base scalar : Ty}
    (populated : Ty.allPopulated [.nominal output] = true)
    (arguments : Values Concrete.Value [base, scalar])
    (ofGroup : inGroup (Concrete.toDatum base (arguments.get .here)).toPoint = true) :
    writes Vocabulary.table package (.nominal output)
      (((model Vocabulary.table package).pure ⟨row, [base, scalar], [.nominal output]⟩ populated
        arguments).get .here) = true :=
  (model_scale_writes found named read closedIs leaf populated arguments).trans
    (closed.multiple_inGroup _ _ ofGroup)

end Vocabulary

end Zkc.Core
