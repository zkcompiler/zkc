import Zkc.Core.Transform.Step
import Zkc.Tests.Vocabulary.Table

/-!
The standard vocabulary through the core: functions over it elaborated (`elabFn` against
`standard`, typed by `typeFn`) and their facts checked (`TypedFn.check`), by the kernel.

A function that applies a row of each family elaborates, and one that names a key at which the
row has no instance is refused by the rule `row` at its place. The restricted row
`field.nonzero` is accepted after a guard on `field.is_nonzero` of the same operand (`x != 0`,
as the reference writes it) and refused without it, with the whole refusal. A literal of each
kind of nominal type is elaborated or refused.
-/

namespace Zkc.Vocabulary.CoreTests

open Zkc.Core
open TableTests (koalaBear koalaBearUnits koalaBear4 fr g1 g2 gt bytes sizedBytes)

/-- The place of an instruction of the function with the key 1. -/
def at_ (instruction : Nat) : Place := ⟨⟨1⟩, [], some ⟨instruction⟩, none⟩

/-- The refusal of the body of a function with the key 1 and no callee; nothing when it
elaborates. -/
def refusal (ins outs : List standard.Ty) (canStop : Bool)
    (body : Region (LocalRaw standard) Unit) : Option (ProgramRefusal standard) :=
  match elabFn [] ⟨⟨1⟩, ins, outs, canStop, none⟩ body with
  | .ok _ => none
  | .error refusal => some refusal

/-- What the check of facts says of the body of a function with the key 1 and no callee
(`typeFn`, `TypedFn.check`): its refusals, or the bounds of its loops; nothing when the body does
not elaborate. -/
def verdict (ins outs : List standard.Ty) (canStop : Bool)
    (body : Region (LocalRaw standard) Unit) :
    Option (List (ProgramRefusal standard) ⊕ List (Place × Nat)) :=
  match typeFn [] ⟨⟨1⟩, ins, outs, canStop, none⟩ body with
  | .ok f =>
      match f.check with
      | .ok bounds => some (.inr bounds)
      | .error refusals => some (.inl refusals)
  | .error _ => none

/-! ## A row of each family -/

/-- `x + y` on `koala-bear`. -/
example : refusal [koalaBear, koalaBear] [koalaBear] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.row (.field .add .koalaBear .all)) [0, 1]] [2]) = none := by
  decide +kernel

/-- `p * s` on `bls12-381.g1`. -/
example : refusal [g1, fr] [g1] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.row (.group .scale (.group .g1))) [0, 1]] [2]) = none := by
  decide +kernel

/-- `⟪a, b⟫` on `[koala-bear; 3]`. -/
example : refusal [.seq koalaBear (some 3), .seq koalaBear (some 3)] [koalaBear] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.row (.seq .inner (.atom (.field .koalaBear)) (some 3))) [0, 1]]
      [2]) = none := by
  decide +kernel

/-- `Sha256::hash(data)`. -/
example : refusal [bytes] [sizedBytes 32] false
    (.mk [0] [.op ⟨1⟩ [1] (.row (.hash .sha256)) [0]] [1]) = none := by
  decide +kernel

/-- `Bls12381::pair(a, b)`. -/
example : refusal [g1, g2] [gt] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.row .pair) [0, 1]] [2]) = none := by
  decide +kernel

/-- `to_nat` at the extension, which is no prime field: no instance, refused by the rule
`row`. -/
example : refusal [koalaBear4] [.nat] false
    (.mk [0] [.op ⟨1⟩ [1] (.row (.field .toNat .koalaBear4 .all)) [0]] [1]) =
    some ⟨.row, at_ 1, .operation (.row (.field .toNat .koalaBear4 .all))⟩ := by
  decide +kernel

/-- `generator` at the target group: no instance. -/
example : refusal [] [gt] false
    (.mk [] [.op ⟨1⟩ [0] (.row (.group .generator (.group .gt))) []] [0]) =
    some ⟨.row, at_ 1, .operation (.row (.group .generator (.group .gt)))⟩ := by
  decide +kernel

/-! ## The restricted row `field.nonzero` -/

abbrev isNonzero : LocalRaw standard := .row (.field .isNonzero .koalaBear .all)
abbrev toNonzero : LocalRaw standard := .row (.field .nonzero .koalaBear .all)
abbrev negation : LocalRaw standard := .owned .boolNot [] []

/-- `x != 0` is `field.is_nonzero(x)`: a guard on it justifies `field.nonzero(x)`. -/
example : verdict [koalaBear] [koalaBearUnits] true (.mk [0] [
    .op ⟨1⟩ [10] isNonzero [0],
    .guard ⟨2⟩ () 10 .refused,
    .op ⟨3⟩ [11] toNonzero [0]] [11]) = some (.inr []) := by
  decide +kernel

/-- `x == 0` is `bool.not(field.is_nonzero(x))`: a guard on its negation justifies
`field.nonzero(x)` too. -/
example : verdict [koalaBear] [koalaBearUnits] true (.mk [0] [
    .op ⟨1⟩ [10] isNonzero [0],
    .op ⟨2⟩ [11] negation [10],
    .op ⟨3⟩ [12] negation [11],
    .guard ⟨4⟩ () 12 .refused,
    .op ⟨5⟩ [13] toNonzero [0]] [13]) = some (.inr []) := by
  decide +kernel

/-- Without the guard, `field.nonzero(x)` is refused: its domain row at its operand is not
known true. -/
example : verdict [koalaBear] [koalaBearUnits] false (.mk [0] [
    .op ⟨1⟩ [10] toNonzero [0]] [10]) =
    some (.inl [⟨.domain, at_ 1,
      .unjustified toNonzero (.holds (.apply isNonzero [0])) [none]⟩]) := by
  decide +kernel

/-- A guard on another operand justifies nothing of this one. -/
example : verdict [koalaBear, koalaBear] [koalaBearUnits] true (.mk [0, 1] [
    .op ⟨1⟩ [10] isNonzero [1],
    .guard ⟨2⟩ () 10 .refused,
    .op ⟨3⟩ [11] toNonzero [0]] [11]) =
    some (.inl [⟨.domain, at_ 3,
      .unjustified toNonzero (.holds (.apply isNonzero [0])) [none]⟩]) := by
  decide +kernel

/-! ## Literals -/

/-- A literal of a field below its characteristic, and at it. -/
example : refusal [] [koalaBear] false
    (.mk [] [.op ⟨1⟩ [0] (.literal koalaBear [2130706432]) []] [0]) = none := by
  decide +kernel
example : refusal [] [koalaBear] false
    (.mk [] [.op ⟨1⟩ [0] (.literal koalaBear [2130706433]) []] [0]) =
    some ⟨.literal, at_ 1, .operation (.literal koalaBear [2130706433])⟩ := by
  decide +kernel

/-- A literal of the elements that are not zero: 1, and not 0. -/
example : refusal [] [koalaBearUnits] false
    (.mk [] [.op ⟨1⟩ [0] (.literal koalaBearUnits [1]) []] [0]) = none := by
  decide +kernel
example : refusal [] [koalaBearUnits] false
    (.mk [] [.op ⟨1⟩ [0] (.literal koalaBearUnits [0]) []] [0]) =
    some ⟨.literal, at_ 1, .operation (.literal koalaBearUnits [0])⟩ := by
  decide +kernel

/-- A group has no literal; its zero is the row `group.zero`. -/
example : refusal [] [g1] false (.mk [] [.op ⟨1⟩ [0] (.literal g1 [0]) []] [0]) =
    some ⟨.literal, at_ 1, .operation (.literal g1 [0])⟩ := by
  decide +kernel
example : refusal [] [g1] false
    (.mk [] [.op ⟨1⟩ [0] (.row (.group .zero (.group .g1))) []] [0]) = none := by
  decide +kernel

end Zkc.Vocabulary.CoreTests
