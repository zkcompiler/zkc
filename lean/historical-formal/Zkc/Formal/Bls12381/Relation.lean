module

public import Zkc.Formal.Bls12381.Arithmetic
public import Zkc.Formal.Abstract.Provider
public import Zkc.Formal.Relation.Protocol

@[expose] public section

/-! The model that runs, related to the model of the arithmetic of BLS12-381.

For a package whose rows are the vocabulary's:

- `bindingOf` reads from the names of the package's rows which nominal type is the scalar field
  and which the group G1, and which row is which operation. No author writes a binding.
- `relation` relates the two models: a scalar to every datum whose number has its residue, and
  a point of the group to every datum that reads as it. It is not one to one.
- `respected`: every row that fits (`fitted`) respects the relation. A row fits when it is a row
  of the arithmetic at the scalar field or at the group, with the typed signature of that
  operation, or a law of scalars. This is proved once per row of the vocabulary, for every
  package; at a package the kernel evaluates which rows fit.
- `covered_scalar`: every datum is related to a scalar, so every reply of the model that runs
  to a law of scalars has a related reply of the arithmetic.

With the relation theorem (`program_related`) a statement proved of a package's protocol in the
arithmetic holds of it in the model that runs, when the rows that the program uses fit.
-/

set_option autoImplicit false

namespace Zkc.Formal.Bls12381

open Zkc.Source Zkc.Core Zkc.Core.Concrete

/-! ## The binding of a package -/

/-- The row of the vocabulary that is the scalar field. -/
def scalarName : String := "bls12-381.fr"

/-- The row of the vocabulary that is the group. -/
def pointName : String := "bls12-381.g1"

/-- What a nominal type of a package is, by the name of its row. -/
def kindOf (row : CatalogueRow) : Kind :=
  if row.name.toString = scalarName then .scalar
  else if row.name.toString = pointName then .point
  else .other

/-- What a row of a package is, by its name and its static arguments, with the size that a row
of a sized collection names. -/
def rowOf (types : Array CatalogueRow) (operation : Operation) : Row × Nat :=
  match operation.identity.name.toString, Vocabulary.argumentsOf types operation.identity with
  | "field.add", some [.type (.row "bls12-381.fr")] => (.fieldAdd, 0)
  | "field.sub", some [.type (.row "bls12-381.fr")] => (.fieldSub, 0)
  | "field.mul", some [.type (.row "bls12-381.fr")] => (.fieldMul, 0)
  | "field.equal", some [.type (.row "bls12-381.fr")] => (.fieldEqual, 0)
  | "group.add", some [.type (.row "bls12-381.g1")] => (.groupAdd, 0)
  | "group.scale", some [.type (.row "bls12-381.g1")] => (.groupScale, 0)
  | "group.equal", some [.type (.row "bls12-381.g1")] => (.groupEqual, 0)
  | "seq.sum", some [.type (.row "bls12-381.fr"), .natural size] => (.seqSum, size)
  | "seq.add", some [.type (.row "bls12-381.fr"), .natural size] => (.seqAdd, size)
  | "seq.sub", some [.type (.row "bls12-381.fr"), .natural size] => (.seqSub, size)
  | "seq.scale", some [.type (.row "bls12-381.fr"), .natural size] => (.seqScale, size)
  | _, _ => (.other, 0)

/-- The name and the static arguments of a row that `rowOf` reads as an operation. -/
abbrev Named (types : Array CatalogueRow) (operation : Operation) (name : String)
    (statics : List Vocabulary.Value) : Prop :=
  operation.identity.name.toString = name ∧
    Vocabulary.argumentsOf types operation.identity = some statics

theorem rowOf_named (types : Array CatalogueRow) (operation : Operation) :
    match rowOf types operation with
    | (.fieldAdd, _) => Named types operation "field.add" [.type (.row "bls12-381.fr")]
    | (.fieldSub, _) => Named types operation "field.sub" [.type (.row "bls12-381.fr")]
    | (.fieldMul, _) => Named types operation "field.mul" [.type (.row "bls12-381.fr")]
    | (.fieldEqual, _) => Named types operation "field.equal" [.type (.row "bls12-381.fr")]
    | (.groupAdd, _) => Named types operation "group.add" [.type (.row "bls12-381.g1")]
    | (.groupScale, _) => Named types operation "group.scale" [.type (.row "bls12-381.g1")]
    | (.groupEqual, _) => Named types operation "group.equal" [.type (.row "bls12-381.g1")]
    | (.seqSum, size) =>
        Named types operation "seq.sum" [.type (.row "bls12-381.fr"), .natural size]
    | (.seqAdd, size) =>
        Named types operation "seq.add" [.type (.row "bls12-381.fr"), .natural size]
    | (.seqSub, size) =>
        Named types operation "seq.sub" [.type (.row "bls12-381.fr"), .natural size]
    | (.seqScale, size) =>
        Named types operation "seq.scale" [.type (.row "bls12-381.fr"), .natural size]
    | (.other, _) => True := by
  unfold rowOf
  split
  all_goals
    first
    | exact True.intro
    | (rename_i same
       split at same
       all_goals cases same <;> exact ⟨by assumption, by assumption⟩)

/-- The binding of a package: the kinds of its nominal types and of its rows. -/
def bindingOf (package : Raw.Package) : Binding :=
  ⟨package.types.map kindOf,
    package.operations.map fun operation => (rowOf package.types.toArray operation).1⟩

theorem bindingOf_row {package : Raw.Package} {index : Nat} {operation : Operation}
    (found : package.operations[index]? = some operation) :
    (bindingOf package).row index = (rowOf package.types.toArray operation).1 := by
  simp [bindingOf, Binding.row, List.getD, found]

/-! ## The relation -/

section Relation

variable (closed : Vocabulary.GroupClosedUnderMultiples) (laws : CurveLaws)

/-- A scalar is related to every datum whose number has its residue, and a point of the group
to every datum that reads as it. -/
def Kind.Related : (kind : Kind) → kind.Carrier (arithmetic closed laws) → Datum → Prop
  | .scalar, (value : Fin order), datum => value.val = datum.toNat % order
  | .point, (value : GroupPoint), datum => datum.toPoint = value.point
  | .other, _, _ => True

/-- The relation of the model of the arithmetic of a package to the model that runs. -/
def relation (package : Raw.Package) :
    Carriers (provider (arithmetic closed laws) (bindingOf package))
      (Vocabulary.model Vocabulary.table package) :=
  fun row value datum => Kind.Related closed laws ((bindingOf package).kind row) value datum

variable {closed laws}

theorem related_asScalar {kind : Kind} (isScalar : kind = .scalar)
    {value : kind.Carrier (arithmetic closed laws)} {datum : Datum}
    (related : Kind.Related closed laws kind value datum) :
    (kind.asScalar (arithmetic closed laws) value).val = datum.toNat % order := by
  subst isScalar
  exact related

theorem related_ofScalar {kind : Kind} (isScalar : kind = .scalar) {scalar : Fin order}
    {datum : Datum} (same : scalar.val = datum.toNat % order) :
    Kind.Related closed laws kind (kind.ofScalar (arithmetic closed laws) scalar) datum := by
  subst isScalar
  exact same

theorem related_asPoint {kind : Kind} (isPoint : kind = .point)
    {value : kind.Carrier (arithmetic closed laws)} {datum : Datum}
    (related : Kind.Related closed laws kind value datum) :
    datum.toPoint = (kind.asPoint (arithmetic closed laws) value).point := by
  subst isPoint
  exact related

theorem related_ofPoint {kind : Kind} (isPoint : kind = .point) {point : GroupPoint}
    {datum : Datum} (same : datum.toPoint = point.point) :
    Kind.Related closed laws kind (kind.ofPoint (arithmetic closed laws) point) datum := by
  subst isPoint
  exact same

/-- Every datum is related to a scalar: the residue of its number. -/
theorem covered_scalar (package : Raw.Package) {type : Nat}
    (isScalar : (bindingOf package).kind type = .scalar) :
    Covered (relation closed laws package) (.nominal type) := fun datum =>
  ⟨((bindingOf package).kind type).ofScalar (arithmetic closed laws)
      ⟨datum.toNat % order, Nat.mod_lt _ (by decide)⟩,
    related_ofScalar isScalar rfl⟩

end Relation

/-! ## Facts of data -/

theorem toPoint_ofPoint : ∀ point : Concrete.Point, (Datum.ofPoint point).toPoint = point
  | none => rfl
  | some (_, _) => rfl

/-- The difference of two residues is zero exactly when they are equal. -/
theorem difference_zero {modulus first second : Nat} (positive : 0 < modulus) :
    ((first + (modulus - second % modulus) % modulus) % modulus + 0) % modulus = 0 ↔
      first % modulus = second % modulus := by
  have firstBelow := Nat.mod_lt first positive
  have secondBelow := Nat.mod_lt second positive
  rw [Nat.add_zero, Nat.mod_mod, Nat.add_mod, Nat.mod_mod]
  generalize first % modulus = left at firstBelow ⊢
  generalize second % modulus = right at secondBelow ⊢
  by_cases zero : right = 0
  · subst zero
    rw [Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt firstBelow]
  · have within : modulus - right < modulus := by omega
    rw [Nat.mod_eq_of_lt within]
    by_cases least : right ≤ left
    · have reduced : (left + (modulus - right)) % modulus = left - right := by
        rw [show left + (modulus - right) = (left - right) + modulus by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [reduced]
      omega
    · have reduced : (left + (modulus - right)) % modulus = left + (modulus - right) :=
        Nat.mod_eq_of_lt (by omega)
      rw [reduced]
      omega

/-- The difference of two residues, as the residues compute it and as the model that runs
does. -/
theorem sub_residue (modulus first second : Nat) :
    ((modulus - second % modulus) + first % modulus) % modulus =
      (first + (modulus - second % modulus) % modulus) % modulus % modulus := by
  rw [Nat.mod_mod]
  conv => lhs; rw [Nat.add_mod, Nat.mod_mod, Nat.add_comm]
  conv => rhs; rw [Nat.add_mod, Nat.mod_mod]

/-! ## The rows that fit, and their respect of the relation -/

/-- A row of a package fits: it is a row of the arithmetic at the scalar field or at the group,
and its typed signature is that of the operation, at nominal types of the kinds that the
operation takes and gives; or it is a law whose output is a scalar. -/
def fitsRow (package : Raw.Package) (operations : List OperationSignature) (index : Nat) : Bool :=
  match package.operations[index]?, operations[index]? with
  | some operation, some signature =>
    let is (kind : Kind) (type : Nat) : Bool := decide ((bindingOf package).kind type = kind)
    match rowOf package.types.toArray operation, signature with
    | (.fieldAdd, _), ⟨[.nominal first, .nominal second], [.nominal output], .pure⟩ =>
        is .scalar first && is .scalar second && is .scalar output
    | (.fieldSub, _), ⟨[.nominal first, .nominal second], [.nominal output], .pure⟩ =>
        is .scalar first && is .scalar second && is .scalar output
    | (.fieldMul, _), ⟨[.nominal first, .nominal second], [.nominal output], .pure⟩ =>
        is .scalar first && is .scalar second && is .scalar output
    | (.fieldEqual, _), ⟨[.nominal first, .nominal second], [.bool], .pure⟩ =>
        is .scalar first && is .scalar second
    | (.groupAdd, _), ⟨[.nominal first, .nominal second], [.nominal output], .pure⟩ =>
        is .point first && is .point second && is .point output
    | (.groupScale, _), ⟨[.nominal base, .nominal multiplier], [.nominal output], .pure⟩ =>
        is .point base && is .scalar multiplier && is .point output
    | (.groupEqual, _), ⟨[.nominal first, .nominal second], [.bool], .pure⟩ =>
        is .point first && is .point second
    | _, ⟨_, [.nominal output], .sampling⟩ => is .scalar output
    | _, _ => false
  | _, _ => false

/-- The rows of a package that fit. -/
def fitted (package : Raw.Package) (operations : List OperationSignature) : List Nat :=
  (List.range operations.length).filter (fitsRow package operations)

section Respected

variable {closed : Vocabulary.GroupClosedUnderMultiples} {laws : CurveLaws}
  {package : Raw.Package}

local notation "A" => arithmetic closed laws
local notation "R" => relation closed laws package
local notation "B" => bindingOf package

/-- The relation at a nominal type is the relation of its kind. -/
theorem related_nominal {type : Nat} {value : (B).kind type |>.Carrier A} {datum : Datum} :
    Related R (.nominal type) value datum ↔
      Kind.Related closed laws ((B).kind type) value datum := by
  simp only [Related, relation]

/-- An operation of two scalars respects the relation when it agrees with the operation of the
model that runs on residues. -/
theorem scalarBinary_related {compute : Fin order → Fin order → Fin order}
    {combine : Datum → Datum → Datum}
    (agrees : ∀ (x y : Fin order) (a b : Datum), x.val = a.toNat % order →
      y.val = b.toNat % order → (compute x y).val = (combine a b).toNat % order)
    {first second output : Nat} (isFirst : (B).kind first = .scalar)
    (isSecond : (B).kind second = .scalar) (isOutput : (B).kind output = .scalar)
    (populated : Ty.allPopulated [.nominal output] = true)
    (x : Ty.Value (Carrier A B) (.nominal first)) (y : Ty.Value (Carrier A B) (.nominal second))
    (a b : Datum) (sameFirst : Related R (.nominal first) x a)
    (sameSecond : Related R (.nominal second) y b) :
    ValuesRelated (Related R)
      (scalarBinary A B compute [.nominal first, .nominal second] [.nominal output] populated
        (.cons x (.cons y .nil)))
      (.cons (ty := Ty.nominal output) (combine a b) .nil) := by
  refine ValuesRelated.cons (related := Related R) ?_ ValuesRelated.nil
  exact related_nominal.mpr (related_ofScalar isOutput
    (agrees _ _ a b (related_asScalar isFirst (related_nominal.mp sameFirst))
      (related_asScalar isSecond (related_nominal.mp sameSecond))))

/-- Equality of two data that are numbers. -/
theorem number_beq (first second : Nat) :
    (Datum.number first == Datum.number second) = decide (first = second) :=
  decide_eq_decide.mpr ⟨Datum.number.inj, congrArg Datum.number⟩

/-- Equality of two scalars is the equality that the model that runs computes on residues. -/
theorem scalarEqual_related {first second : Nat} (isFirst : (B).kind first = .scalar)
    (isSecond : (B).kind second = .scalar) (populated : Ty.allPopulated [.bool] = true)
    (x : Ty.Value (Carrier A B) (.nominal first)) (y : Ty.Value (Carrier A B) (.nominal second))
    (a b : Datum) (sameFirst : Related R (.nominal first) x a)
    (sameSecond : Related R (.nominal second) y b) :
    ValuesRelated (Related R)
      (scalarEqual A B [.nominal first, .nominal second] [.bool] populated
        (.cons x (.cons y .nil)))
      (.cons (ty := Ty.bool) ((Vocabulary.Element.prime order).equal a b) .nil) := by
  refine ValuesRelated.cons (related := Related R) ?_ ValuesRelated.nil
  have sameFirst : (((B).kind first).asScalar A x).val = a.toNat % order :=
    related_asScalar isFirst (related_nominal.mp sameFirst)
  have sameSecond : (((B).kind second).asScalar A y).val = b.toNat % order :=
    related_asScalar isSecond (related_nominal.mp sameSecond)
  have equal : (Vocabulary.Element.prime order).equal a b =
      decide (a.toNat % order = b.toNat % order) := by
    show (Datum.number (((a.toNat + (order - b.toNat % order) % order) % order + 0) % order) ==
      Datum.number 0) = _
    rw [number_beq]
    exact decide_eq_decide.mpr (difference_zero (by decide))
  show decide (((B).kind first).asScalar A x = ((B).kind second).asScalar A y) =
    (Vocabulary.Element.prime order).equal a b
  rw [equal]
  refine decide_eq_decide.mpr ?_
  rw [← sameFirst, ← sameSecond]
  exact Fin.val_inj.symm

/-- The sum of two points is the sum that the model that runs computes. -/
theorem pointBinary_related {first second output : Nat} (isFirst : (B).kind first = .point)
    (isSecond : (B).kind second = .point) (isOutput : (B).kind output = .point)
    (populated : Ty.allPopulated [.nominal output] = true)
    (x : Ty.Value (Carrier A B) (.nominal first)) (y : Ty.Value (Carrier A B) (.nominal second))
    (a b : Datum) (sameFirst : Related R (.nominal first) x a)
    (sameSecond : Related R (.nominal second) y b) :
    ValuesRelated (Related R)
      (pointBinary A B [.nominal first, .nominal second] [.nominal output] populated
        (.cons x (.cons y .nil)))
      (.cons (ty := Ty.nominal output) (Vocabulary.Element.curve.add a b) .nil) := by
  refine ValuesRelated.cons (related := Related R) ?_ ValuesRelated.nil
  have sameFirst : a.toPoint = (((B).kind first).asPoint A x).point :=
    related_asPoint isFirst (related_nominal.mp sameFirst)
  have sameSecond : b.toPoint = (((B).kind second).asPoint A y).point :=
    related_asPoint isSecond (related_nominal.mp sameSecond)
  refine related_nominal.mpr (related_ofPoint isOutput ?_)
  show (Datum.ofPoint (addPoints a.toPoint b.toPoint)).toPoint =
    addPoints (((B).kind first).asPoint A x).point (((B).kind second).asPoint A y).point
  rw [toPoint_ofPoint, sameFirst, sameSecond]

/-- The multiple of a point is the multiple that the model that runs computes. -/
theorem pointScale_related {base multiplier output : Nat} (isBase : (B).kind base = .point)
    (isMultiplier : (B).kind multiplier = .scalar) (isOutput : (B).kind output = .point)
    (populated : Ty.allPopulated [.nominal output] = true)
    (x : Ty.Value (Carrier A B) (.nominal base)) (y : Ty.Value (Carrier A B) (.nominal multiplier))
    (a b : Datum) (sameFirst : Related R (.nominal base) x a)
    (sameSecond : Related R (.nominal multiplier) y b) :
    ValuesRelated (Related R)
      (pointScale A B [.nominal base, .nominal multiplier] [.nominal output] populated
        (.cons x (.cons y .nil)))
      (.cons (ty := Ty.nominal output) (Vocabulary.Element.curve.scale a b) .nil) := by
  refine ValuesRelated.cons (related := Related R) ?_ ValuesRelated.nil
  have sameBase : a.toPoint = (((B).kind base).asPoint A x).point :=
    related_asPoint isBase (related_nominal.mp sameFirst)
  have sameMultiplier : (((B).kind multiplier).asScalar A y).val = b.toNat % order :=
    related_asScalar isMultiplier (related_nominal.mp sameSecond)
  refine related_nominal.mpr (related_ofPoint isOutput ?_)
  show (Datum.ofPoint (scalePoint a.toPoint (b.toNat % Concrete.scalarModulus))).toPoint =
    scalePoint (((B).kind base).asPoint A x).point (((B).kind multiplier).asScalar A y).val
  rw [toPoint_ofPoint, sameBase, sameMultiplier, Vocabulary.scalarModulus_eq]

/-- Equality of two points is the equality that the model that runs computes. -/
theorem pointEqual_related {first second : Nat} (isFirst : (B).kind first = .point)
    (isSecond : (B).kind second = .point) (populated : Ty.allPopulated [.bool] = true)
    (x : Ty.Value (Carrier A B) (.nominal first)) (y : Ty.Value (Carrier A B) (.nominal second))
    (a b : Datum) (sameFirst : Related R (.nominal first) x a)
    (sameSecond : Related R (.nominal second) y b) :
    ValuesRelated (Related R)
      (pointEqual A B [.nominal first, .nominal second] [.bool] populated
        (.cons x (.cons y .nil)))
      (.cons (ty := Ty.bool) (Vocabulary.Element.curve.equal a b) .nil) := by
  refine ValuesRelated.cons (related := Related R) ?_ ValuesRelated.nil
  have sameFirst : a.toPoint = (((B).kind first).asPoint A x).point :=
    related_asPoint isFirst (related_nominal.mp sameFirst)
  have sameSecond : b.toPoint = (((B).kind second).asPoint A y).point :=
    related_asPoint isSecond (related_nominal.mp sameSecond)
  show ((((B).kind first).asPoint A x).point == (((B).kind second).asPoint A y).point) =
    (a.toPoint == b.toPoint)
  rw [sameFirst, sameSecond]

/-! ### What the operations of the field compute on residues -/

theorem add_agrees (x y : Fin order) (a b : Datum) (first : x.val = a.toNat % order)
    (second : y.val = b.toNat % order) :
    (x + y).val = ((Vocabulary.Element.prime order).add a b).toNat % order := by
  show (x + y).val = (a.toNat + b.toNat) % order % order
  rw [Fin.val_add, first, second, Nat.mod_mod, ← Nat.add_mod]

theorem sub_agrees (x y : Fin order) (a b : Datum) (first : x.val = a.toNat % order)
    (second : y.val = b.toNat % order) :
    (x - y).val = ((Vocabulary.Element.prime order).sub a b).toNat % order := by
  show (x - y).val = (a.toNat + (order - b.toNat % order) % order) % order % order
  rw [Fin.sub_def]
  show ((order - y.val) + x.val) % order = _
  rw [first, second]
  exact sub_residue order a.toNat b.toNat

theorem mul_agrees (x y : Fin order) (a b : Datum) (first : x.val = a.toNat % order)
    (second : y.val = b.toNat % order) :
    (x * y).val = ((Vocabulary.Element.prime order).mul a b).toNat % order := by
  show (x * y).val = a.toNat * b.toNat % order % order
  rw [Fin.val_mul, first, second, Nat.mod_mod, ← Nat.mul_mod]

end Respected

/-- Related values, read through equations. -/
theorem related_through {closed : Vocabulary.GroupClosedUnderMultiples} {laws : CurveLaws}
    {package : Raw.Package} {types : List Ty}
    {values results : Values (Ty.Value (Carrier (arithmetic closed laws) (bindingOf package))) types}
    {images data : Values Concrete.Value types} (abstract : values = results)
    (concrete : images = data)
    (related : ValuesRelated (Related (relation closed laws package)) results data) :
    ValuesRelated (Related (relation closed laws package)) values images :=
  abstract ▸ concrete ▸ related

section Rows

variable {closed : Vocabulary.GroupClosedUnderMultiples} {laws : CurveLaws}
  {package : Raw.Package} {index : Nat} {operation : Operation} {size : Nat}
  (found : package.operations[index]? = some operation)

include found

/-- The row `field.add` respects the relation. -/
theorem fieldAdd_respected (isRow : rowOf package.types.toArray operation = (.fieldAdd, size))
    {first second output : Nat} (isFirst : (bindingOf package).kind first = .scalar)
    (isSecond : (bindingOf package).kind second = .scalar)
    (isOutput : (bindingOf package).kind output = .scalar) :
    RowRespected (relation closed laws package)
      ⟨index, [.nominal first, .nominal second], [.nominal output]⟩ .pure := by
  have named := rowOf_named package.types.toArray operation
  have bound := bindingOf_row found
  rw [isRow] at named bound
  intro populated values images same
  match values, images, same with
  | .cons x (.cons y .nil), .cons a (.cons b .nil), same =>
    exact related_through (congrFun (provider_fieldAdd _ _ populated bound) _)
      (Vocabulary.model_fieldAdd found named.2 Vocabulary.element_bls12381Fr named.1 populated a b)
      (scalarBinary_related add_agrees isFirst isSecond isOutput populated x y a b (same _ Var.here)
        (same _ (Var.there Var.here)))

/-- The row `field.sub` respects the relation. -/
theorem fieldSub_respected (isRow : rowOf package.types.toArray operation = (.fieldSub, size))
    {first second output : Nat} (isFirst : (bindingOf package).kind first = .scalar)
    (isSecond : (bindingOf package).kind second = .scalar)
    (isOutput : (bindingOf package).kind output = .scalar) :
    RowRespected (relation closed laws package)
      ⟨index, [.nominal first, .nominal second], [.nominal output]⟩ .pure := by
  have named := rowOf_named package.types.toArray operation
  have bound := bindingOf_row found
  rw [isRow] at named bound
  intro populated values images same
  match values, images, same with
  | .cons x (.cons y .nil), .cons a (.cons b .nil), same =>
    exact related_through (congrFun (provider_fieldSub _ _ populated bound) _)
      (Vocabulary.model_fieldSub found named.2 Vocabulary.element_bls12381Fr named.1 populated a b)
      (scalarBinary_related sub_agrees isFirst isSecond isOutput populated x y a b (same _ Var.here)
        (same _ (Var.there Var.here)))

/-- The row `field.mul` respects the relation. -/
theorem fieldMul_respected (isRow : rowOf package.types.toArray operation = (.fieldMul, size))
    {first second output : Nat} (isFirst : (bindingOf package).kind first = .scalar)
    (isSecond : (bindingOf package).kind second = .scalar)
    (isOutput : (bindingOf package).kind output = .scalar) :
    RowRespected (relation closed laws package)
      ⟨index, [.nominal first, .nominal second], [.nominal output]⟩ .pure := by
  have named := rowOf_named package.types.toArray operation
  have bound := bindingOf_row found
  rw [isRow] at named bound
  intro populated values images same
  match values, images, same with
  | .cons x (.cons y .nil), .cons a (.cons b .nil), same =>
    exact related_through (congrFun (provider_fieldMul _ _ populated bound) _)
      (Vocabulary.model_fieldMul found named.2 Vocabulary.element_bls12381Fr named.1 populated a b)
      (scalarBinary_related mul_agrees isFirst isSecond isOutput populated x y a b (same _ Var.here)
        (same _ (Var.there Var.here)))

/-- The row `field.equal` respects the relation. -/
theorem fieldEqual_respected (isRow : rowOf package.types.toArray operation = (.fieldEqual, size))
    {first second : Nat} (isFirst : (bindingOf package).kind first = .scalar)
    (isSecond : (bindingOf package).kind second = .scalar) :
    RowRespected (relation closed laws package)
      ⟨index, [.nominal first, .nominal second], [.bool]⟩ .pure := by
  have named := rowOf_named package.types.toArray operation
  have bound := bindingOf_row found
  rw [isRow] at named bound
  intro populated values images same
  match values, images, same with
  | .cons x (.cons y .nil), .cons a (.cons b .nil), same =>
    exact related_through (congrFun (provider_fieldEqual _ _ populated bound) _)
      (Vocabulary.model_fieldEqual found named.2 Vocabulary.element_bls12381Fr named.1 populated a b)
      (scalarEqual_related isFirst isSecond populated x y a b (same _ Var.here)
        (same _ (Var.there Var.here)))

/-- The row `group.add` respects the relation. -/
theorem groupAdd_respected (isRow : rowOf package.types.toArray operation = (.groupAdd, size))
    {first second output : Nat} (isFirst : (bindingOf package).kind first = .point)
    (isSecond : (bindingOf package).kind second = .point)
    (isOutput : (bindingOf package).kind output = .point) :
    RowRespected (relation closed laws package)
      ⟨index, [.nominal first, .nominal second], [.nominal output]⟩ .pure := by
  have named := rowOf_named package.types.toArray operation
  have bound := bindingOf_row found
  rw [isRow] at named bound
  intro populated values images same
  match values, images, same with
  | .cons x (.cons y .nil), .cons a (.cons b .nil), same =>
    exact related_through (congrFun (provider_groupAdd _ _ populated bound) _)
      (Vocabulary.model_groupAdd found named.2 Vocabulary.element_bls12381G1 named.1 populated a b)
      (pointBinary_related isFirst isSecond isOutput populated x y a b (same _ Var.here)
        (same _ (Var.there Var.here)))

/-- The row `group.scale` respects the relation. -/
theorem groupScale_respected (isRow : rowOf package.types.toArray operation = (.groupScale, size))
    {first second output : Nat} (isFirst : (bindingOf package).kind first = .point)
    (isSecond : (bindingOf package).kind second = .scalar)
    (isOutput : (bindingOf package).kind output = .point) :
    RowRespected (relation closed laws package)
      ⟨index, [.nominal first, .nominal second], [.nominal output]⟩ .pure := by
  have named := rowOf_named package.types.toArray operation
  have bound := bindingOf_row found
  rw [isRow] at named bound
  intro populated values images same
  match values, images, same with
  | .cons x (.cons y .nil), .cons a (.cons b .nil), same =>
    exact related_through (congrFun (provider_groupScale _ _ populated bound) _)
      (Vocabulary.model_groupScale found named.2 Vocabulary.element_bls12381G1 named.1 populated a b)
      (pointScale_related isFirst isSecond isOutput populated x y a b (same _ Var.here)
        (same _ (Var.there Var.here)))

/-- The row `group.equal` respects the relation. -/
theorem groupEqual_respected (isRow : rowOf package.types.toArray operation = (.groupEqual, size))
    {first second : Nat} (isFirst : (bindingOf package).kind first = .point)
    (isSecond : (bindingOf package).kind second = .point) :
    RowRespected (relation closed laws package)
      ⟨index, [.nominal first, .nominal second], [.bool]⟩ .pure := by
  have named := rowOf_named package.types.toArray operation
  have bound := bindingOf_row found
  rw [isRow] at named bound
  intro populated values images same
  match values, images, same with
  | .cons x (.cons y .nil), .cons a (.cons b .nil), same =>
    exact related_through (congrFun (provider_groupEqual _ _ populated bound) _)
      (Vocabulary.model_groupEqual found named.2 Vocabulary.element_bls12381G1 named.1 populated a b)
      (pointEqual_related isFirst isSecond populated x y a b (same _ Var.here)
        (same _ (Var.there Var.here)))

end Rows

/-- Every row of a package that fits respects the relation. -/
theorem respected (closed : Vocabulary.GroupClosedUnderMultiples) (laws : CurveLaws)
    (package : Raw.Package) (operations : List OperationSignature) :
    RowsRespected (relation closed laws package) operations (fitted package operations) := by
  intro inputs outputs kind row member
  obtain ⟨index, valid⟩ := row
  have fit : fitsRow package operations index = true := (List.mem_filter.mp member).2
  unfold fitsRow at fit
  split at fit
  · rename_i operation signature found typed
    split at fit
    · -- `field.add`
      rename_i isRow
      cases Option.some.inj (typed.symm.trans valid)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      exact fieldAdd_respected found isRow fit.1.1 fit.1.2 fit.2
    · -- `field.sub`
      rename_i isRow
      cases Option.some.inj (typed.symm.trans valid)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      exact fieldSub_respected found isRow fit.1.1 fit.1.2 fit.2
    · -- `field.mul`
      rename_i isRow
      cases Option.some.inj (typed.symm.trans valid)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      exact fieldMul_respected found isRow fit.1.1 fit.1.2 fit.2
    · -- `field.equal`
      rename_i isRow
      cases Option.some.inj (typed.symm.trans valid)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      exact fieldEqual_respected found isRow fit.1 fit.2
    · -- `group.add`
      rename_i isRow
      cases Option.some.inj (typed.symm.trans valid)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      exact groupAdd_respected found isRow fit.1.1 fit.1.2 fit.2
    · -- `group.scale`
      rename_i isRow
      cases Option.some.inj (typed.symm.trans valid)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      exact groupScale_respected found isRow fit.1.1 fit.1.2 fit.2
    · -- `group.equal`
      rename_i isRow
      cases Option.some.inj (typed.symm.trans valid)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
      exact groupEqual_respected found isRow fit.1 fit.2
    · -- a law of scalars
      cases Option.some.inj (typed.symm.trans valid)
      simp only [decide_eq_true_eq] at fit
      intro output member
      cases List.mem_singleton.mp member
      exact covered_scalar package fit
    · exact absurd fit Bool.false_ne_true
  · exact absurd fit Bool.false_ne_true

end Zkc.Formal.Bls12381
