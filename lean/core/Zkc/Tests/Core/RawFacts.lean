import Zkc.Tests.Core.Facts
import Zkc.Core.RawFacts

/-! Kernel checks for the shape of an `if` read on its raw regions.

The check of facts reads the regions of an `if` as typed regions; `Raw.LocalStep.branchShape`
reads them as raw ones. For every instruction of every function of `fixtures/facts.json` and
of `fixtures/facts-unjustified.json`, at every depth, the kernel evaluates both and they are
equal. Among them:

- `first_is_one` and `first_or_zero`: an `if` whose second region is the literal `false` and
  the return of it, a conjunction of the condition;
- `empty_or_one`: an `if` whose first region is the literal `true` and the return of it, a
  disjunction of the condition;
- `minus`, `inside`, `joined`: an `if` whose regions return a `nat` literal or a computed
  value, with no shape;
- in the second package, an `if` whose second region returns the literal `true`, with no
  shape.

Three regions that differ from the form by one thing each are not recognized: a literal
`false` followed by the return of a capture, a `nat` literal, and a literal after another
instruction.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace RawFacts

mutual
  /-- The shape of each raw instruction of a region, each followed by those of its nested
  regions, in order. -/
  def rawStep : Raw.LocalStep → List (Option Shape)
    | .conditional condition captures outputs onTrue onFalse =>
        (Raw.LocalStep.conditional condition captures outputs onTrue onFalse).branchShape ::
          (rawRegion onTrue ++ rawRegion onFalse)
    | .match _ _ _ _ arms => none :: rawArms arms
    | .loop _ _ _ _ body => none :: rawRegion body
    | _ => [none]

  def rawRegion : Raw.LocalRegion → List (Option Shape)
    | .step instruction next => rawStep instruction ++ rawRegion next
    | .block _ body next => rawRegion body ++ rawRegion next
    | _ => []

  def rawArms : Raw.LocalArms → List (Option Shape)
    | .none => []
    | .arm region rest => rawRegion region ++ rawArms rest
end

section Typed

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

mutual
  /-- The shape that the check gives each instruction of a typed region, each followed by
  those of its nested regions, in order. -/
  def typedRegion : {Γ out : List Ty} →
      Region (LocalDialect operations functions deployed) Γ out → List (Option Shape)
    | Γ, _, .letOp op arguments bodies next =>
        LocalOp.branchShape op (Scope.numbers Γ.length arguments) bodies ::
          (typedRegions bodies ++ typedRegion next)
    | _, _, .bind body next => typedRegion body ++ typedRegion next
    | _, _, _ => []

  def typedRegions : {signatures : List (List Ty × List Ty)} →
      Regions (LocalDialect operations functions deployed) signatures → List (Option Shape)
    | _, .nil => []
    | _, .cons body tail => typedRegion body ++ typedRegions tail
end

end Typed

/-- The shapes of the raw functions of a package, in program order. -/
def rawShapes (package : Raw.Package) : List (List (Option Shape)) :=
  package.functions.map fun function =>
    match function.body with
    | some body => rawRegion body
    | none => []

/-- The shapes that the check gives the typed functions, in program order. -/
def typedShapes {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → Functions typeTable operations functions →
      List (List (Option Shape))
  | _, .nil => []
  | _, .snoc earlier definition _ => typedShapes earlier ++ [typedRegion definition.body]
  | _, .opaque earlier _ _ => typedShapes earlier ++ [[]]

/-- The shapes that are present. -/
def present (shapes : List (Option Shape)) : List Shape := shapes.filterMap id

/-! ## The raw and the typed recognitions agree -/

kernel_refl passing_agree :
    typedShapes Facts.typed.program.functions equals rawShapes Facts.raw
kernel_refl failing_agree :
    typedShapes Facts.unguardedTyped.program.functions equals rawShapes Facts.unguarded

/-! ## The shapes of the functions that pass -/

-- `first_is_one`, `first_or_zero`: the second region returns the literal `false`.
kernel_refl first_is_one : ((rawShapes Facts.raw)[23]?).map present equals some [.conjunct 3]
kernel_refl first_or_zero : ((rawShapes Facts.raw)[24]?).map present equals some [.conjunct 3]
-- `empty_or_one`: the first region returns the literal `true`.
kernel_refl empty_or_one : ((rawShapes Facts.raw)[25]?).map present equals some [.disjunct 3]
-- `minus`, `inside`: neither region returns a `bool` literal.
kernel_refl minus : ((rawShapes Facts.raw)[7]?).map present equals some []
kernel_refl inside : ((rawShapes Facts.raw)[15]?).map present equals some []

-- Every other function of the two packages has an `if` without a shape, or none.
kernel_refl passing_shapes :
    ((rawShapes Facts.raw).map present).filter (fun shapes => !shapes.isEmpty) equals
      [[.conjunct 3], [.conjunct 3], [.disjunct 3]]
kernel_refl failing_shapes :
    ((rawShapes Facts.unguarded).map present).filter (fun shapes => !shapes.isEmpty) equals []

/-! ## Regions that are and are not the form -/

/-- The literal `value` and the return of it, in a region of two inputs. -/
def literalRegion (value : Bool) : Raw.LocalRegion := .step (.literal (.bool value)) (.ret [2])

kernel_refl literal_false : (literalRegion false).literalBool 2 equals some false
kernel_refl literal_true : (literalRegion true).literalBool 2 equals some true
-- The same region among three inputs returns its last input, not the literal.
kernel_refl other_inputs : (literalRegion false).literalBool 3 equals none
-- A literal `false` and the return of a capture.
kernel_refl returns_capture :
    (Raw.LocalRegion.step (.literal (.bool false)) (.ret [0])).literalBool 2 equals none
-- A `nat` literal.
kernel_refl nat_literal :
    (Raw.LocalRegion.step (.literal (.nat 0)) (.ret [2])).literalBool 2 equals none
-- A literal after another instruction.
kernel_refl second_instruction :
    (Raw.LocalRegion.step (.builtin .boolNot [0])
      (.step (.literal (.bool false)) (.ret [3]))).literalBool 2 equals none
-- Two returned values.
kernel_refl two_values :
    (Raw.LocalRegion.step (.literal (.bool false)) (.ret [2, 0])).literalBool 2 equals none

-- The second region decides first: both literals give a conjunction.
kernel_refl both_literals :
    (Raw.LocalStep.conditional 0 [0, 1] [.bool] (literalRegion true)
      (literalRegion false)).branchShape equals some (.conjunct 0)
kernel_refl only_true :
    (Raw.LocalStep.conditional 0 [0, 1] [.bool] (literalRegion true) (.ret [1])).branchShape
      equals some (.disjunct 0)
-- The literal `true` in the second region and `false` in the first give no shape.
kernel_refl swapped :
    (Raw.LocalStep.conditional 0 [0, 1] [.bool] (literalRegion false)
      (literalRegion true)).branchShape equals none

/-- An instruction that elaborates has the shape that the check computes for it. -/
theorem agrees {operations : List OperationSignature} {functions : List FunctionHeader}
    {deployed : Bool} (typeTable : TypeTable) (rows : Scope operations)
    (callees : Scope functions) (typeOf : Nat → Option Ty) (instruction : Raw.LocalStep)
    (elaborated : LocalElaborated operations functions deployed)
    (accepted : elaborateLocalStep typeTable rows callees deployed typeOf instruction =
      .ok elaborated) :
    LocalOp.branchShape elaborated.op elaborated.operands elaborated.bodies =
      instruction.branchShape :=
  branchShape_elaborate typeTable rows callees typeOf instruction elaborated accepted

#print axioms agrees
#print axioms literalBool_elaborate

end RawFacts
