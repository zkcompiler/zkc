module

public import Zkc.Core.Facts
public import Zkc.Core.Elaborate

public section

/-! The shape of an `if` from its raw regions.

The check of facts gives the result of an `if` a shape when one of its two regions is one
`literal` of a `bool` and the return of that value (`LocalOp.branchShape`). It reads the
typed regions. The same form is recognized on raw regions (`Raw.LocalRegion.literalBool`),
and a raw region that elaborates is recognized exactly when its typed region is. The shape
of a raw instruction (`Raw.LocalStep.branchShape`) is therefore the shape that the check
computes for the instruction it elaborates to.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The shape that the check of facts gives the result of a raw instruction beyond the one
of its operation: that of an `if` whose regions return literals, read on the raw regions.
A region of an `if` has one input per capture. -/
@[expose] def Raw.LocalStep.branchShape : Raw.LocalStep → Option Shape
  | .conditional condition captures _ onTrue onFalse =>
      branchShapeOf condition (onTrue.literalBool captures.length)
        (onFalse.literalBool captures.length)
  | _ => none

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- The `bool` that an operation is the literal of. -/
@[expose] def LocalOp.literalBool : LocalOp operations functions deployed → Option Bool
  | .literal (.bool value) => some value
  | _ => none

/-- A region returns one value, the newest of its context, and does nothing else. -/
@[expose] def returnsNewest {Γ out : List Ty} :
    Region (LocalDialect operations functions deployed) Γ out → Bool
  | .ret (.cons reference .nil) => decide (reference.index = 0)
  | _ => false

/-- The literal that an instruction and the rest of its region return is the literal of the
instruction, when the rest returns its value and nothing else. -/
theorem literalReturn_eq {Γ : List Ty} : ∀ (op : LocalOp operations functions deployed)
    {out : List Ty}
    (rest : Region (LocalDialect operations functions deployed) (bindAll Γ op.results) out),
    literalReturn op rest = cond (returnsNewest rest) op.literalBool none
  | .literal (.bool _), _, .ret (.cons _ .nil) => rfl
  | .literal (.bool _), _, .ret .nil => rfl
  | .literal (.bool _), _, .ret (.cons _ (.cons _ _)) => rfl
  | .literal (.bool _), _, .stop _ => rfl
  | .literal (.bool _), _, .letOp .. => rfl
  | .literal (.bool _), _, .bind .. => rfl
  | .literal (.nat _), _, rest => by cases returnsNewest rest <;> rfl
  | .literal (.fin ..), _, rest => by cases returnsNewest rest <;> rfl
  | .literal (.nominal ..), _, rest => by cases returnsNewest rest <;> rfl
  | .literal (.bytes _), _, rest => by cases returnsNewest rest <;> rfl
  | .op .., _, rest => by cases returnsNewest rest <;> rfl
  | .call .., _, rest => by cases returnsNewest rest <;> rfl
  | .conditional .., _, rest => by cases returnsNewest rest <;> rfl
  | .match .., _, rest => by cases returnsNewest rest <;> rfl
  | .loop .., _, rest => by cases returnsNewest rest <;> rfl
  | .guard _, _, rest => by cases returnsNewest rest <;> rfl
  | .builtin _, _, rest => by cases returnsNewest rest <;> rfl

/-- The typed literal of a raw one is a `bool` exactly when the raw one is. -/
theorem elaborateLiteral_literalBool (raw : Raw.Literal) (literal : Literal)
    (found : elaborateLiteral raw = some literal) :
    (LocalOp.literal literal : LocalOp operations functions deployed).literalBool =
      (Raw.LocalStep.literal raw).literalBool := by
  cases raw with
  | nat value =>
      have same : some (Literal.nat value) = some literal := found
      cases same
      rfl
  | bool value =>
      have same : some (Literal.bool value) = some literal := found
      cases same
      rfl
  | nominal row data =>
      have same : some (Literal.nominal row data) = some literal := found
      cases same
      rfl
  | fin bound value =>
      simp only [elaborateLiteral] at found
      split at found
      · cases Option.some.inj found
        rfl
      · cases found
  | bytes data =>
      simp only [elaborateLiteral] at found
      split at found
      · cases Option.some.inj found
        rfl
      · cases found

variable (typeTable : TypeTable) (rows : Scope operations) (callees : Scope functions)

/-- The operation of a raw instruction is the literal of a `bool` exactly when the
instruction is. -/
theorem elaborateLocalStep_literalBool (typeOf : Nat → Option Ty)
    (instruction : Raw.LocalStep) (elaborated : LocalElaborated operations functions deployed)
    (accepted : elaborateLocalStep typeTable rows callees deployed typeOf instruction =
      .ok elaborated) :
    elaborated.op.literalBool = instruction.literalBool := by
  cases instruction with
  | literal value =>
      simp only [elaborateLocalStep] at accepted
      split at accepted
      · rename_i literal found
        cases accepted
        exact elaborateLiteral_literalBool value literal found
      · cases accepted
  | _ =>
      simp only [elaborateLocalStep] at accepted
      repeat' split at accepted
      all_goals first
        | (cases accepted; rfl)
        | cases accepted

/-- A raw region that elaborates returns the value with the newest number and nothing else
exactly when its typed region returns the newest value and nothing else. -/
theorem elaborateLocalRegion_returnsNewest {Γ out : List Ty} (scope : Scope Γ)
    (raw : Raw.LocalRegion) (region : Region (LocalDialect operations functions deployed) Γ out)
    (accepted : elaborateLocalRegion typeTable rows callees deployed Γ scope out raw =
      .ok region) :
    returnsNewest region = raw.returnsOnly (scope.depth - 1) := by
  cases raw with
  | ret values =>
      simp only [elaborateLocalRegion] at accepted
      split at accepted
      · rename_i operands found
        cases accepted
        have numbered := Scope.numbers_operands? scope values operands found
        cases operands with
        | nil =>
            cases numbered
            rfl
        | cons reference rest =>
            cases rest with
            | nil =>
                cases numbered
                have bound := reference.index_lt
                rw [← scope.counted] at bound
                show decide (reference.index = 0) =
                  Nat.beq (Scope.number scope.depth reference) (scope.depth - 1)
                cases same : Nat.beq (Scope.number scope.depth reference) (scope.depth - 1) with
                | true =>
                    have equal := Nat.eq_of_beq_eq_true same
                    simp only [Scope.number, Scope.position] at equal
                    exact decide_eq_true (by omega)
                | false =>
                    refine decide_eq_false fun zero => ?_
                    have equal : Scope.number scope.depth reference = scope.depth - 1 := by
                      simp only [Scope.number, Scope.position, zero]
                      omega
                    rw [equal, Nat.beq_refl] at same
                    cases same
            | cons second others =>
                cases numbered
                rfl
      · cases accepted
  | stop reason =>
      simp only [elaborateLocalRegion] at accepted
      cases accepted
      rfl
  | step instruction next =>
      simp only [elaborateLocalRegion] at accepted
      repeat' split at accepted
      all_goals first
        | (cases accepted; rfl)
        | cases accepted
  | block outputs body next =>
      simp only [elaborateLocalRegion] at accepted
      repeat' split at accepted
      all_goals first
        | (cases accepted; rfl)
        | cases accepted

/-- A raw region that elaborates is recognized as the return of a `bool` literal exactly
when its typed region is, with the same literal. `scope.depth` is the number of the
region's inputs when the region is closed. -/
theorem literalBool_elaborate {Γ out : List Ty} (scope : Scope Γ) (raw : Raw.LocalRegion)
    (region : Region (LocalDialect operations functions deployed) Γ out)
    (accepted : elaborateLocalRegion typeTable rows callees deployed Γ scope out raw =
      .ok region) :
    literalBool region = raw.literalBool scope.depth := by
  cases raw with
  | ret values =>
      simp only [elaborateLocalRegion] at accepted
      split at accepted <;> cases accepted
      rfl
  | stop reason =>
      simp only [elaborateLocalRegion] at accepted
      cases accepted
      rfl
  | block outputs body next =>
      simp only [elaborateLocalRegion] at accepted
      repeat' split at accepted
      all_goals first
        | (cases accepted; rfl)
        | cases accepted
  | step instruction next =>
      simp only [elaborateLocalRegion] at accepted
      split at accepted
      · rename_i op bodies values step
        split at accepted
        · rename_i arguments rest found restOk
          cases accepted
          have literal := elaborateLocalStep_literalBool typeTable rows callees scope.type?
            instruction ⟨op, bodies, values⟩ step
          have returned := elaborateLocalRegion_returnsNewest typeTable rows callees
            (scope.bindAll op.results) next rest restOk
          show literalReturn op rest = cond (next.returnsOnly scope.depth) instruction.literalBool none
          rw [literalReturn_eq, returned, ← literal]
          cases found' : op.literalBool with
          | none => cases next.returnsOnly _ <;> cases next.returnsOnly _ <;> rfl
          | some value =>
              have single : op.results = [.bool] := by
                cases op with
                | literal constant =>
                    cases constant with
                    | bool flag => rfl
                    | _ => cases found'
                | _ => cases found'
              rw [Scope.depth_bindAll, single]
              rfl
        · cases accepted
        · cases accepted
      · cases accepted

/-- The shape of a raw instruction is the shape that the check of facts gives the operation
it elaborates to, on its operands and its typed regions. -/
theorem branchShape_elaborate (typeOf : Nat → Option Ty) (instruction : Raw.LocalStep)
    (elaborated : LocalElaborated operations functions deployed)
    (accepted : elaborateLocalStep typeTable rows callees deployed typeOf instruction =
      .ok elaborated) :
    LocalOp.branchShape elaborated.op elaborated.operands elaborated.bodies =
      instruction.branchShape := by
  cases instruction with
  | conditional condition captures outputs onTrue onFalse =>
      simp only [elaborateLocalStep] at accepted
      split at accepted
      · rename_i captureTypes filled typed _
        split at accepted
        · rename_i whenTrue whenFalse trueOk falseOk
          cases accepted
          have depth : (Scope.empty.bindAll captureTypes : Scope (bindAll [] captureTypes)).depth =
              captures.length := by
            rw [Scope.depth_bindAll]
            show 0 + captureTypes.length = _
            rw [Nat.zero_add]
            exact typesWith_length typeOf captures captureTypes typed
          have first := literalBool_elaborate typeTable rows callees _ onTrue whenTrue trueOk
          have second := literalBool_elaborate typeTable rows callees _ onFalse whenFalse falseOk
          rw [depth] at first second
          show branchShapeOf condition (literalBool whenTrue) (literalBool whenFalse) = _
          rw [first, second]
          rfl
        · cases accepted
        · cases accepted
      · cases accepted
      · cases accepted
  | _ =>
      simp only [elaborateLocalStep] at accepted
      repeat' split at accepted
      all_goals first
        | (cases accepted; rfl)
        | cases accepted

end Local

end Zkc.Core
