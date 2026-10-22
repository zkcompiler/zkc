module

public import Zkc.Source.Structured.Algebra
public import Zkc.Semantics.Execution

@[expose] public section

/-! Logical list and checked u64 equations. These do not model allocation or
observer work capacity. Stops reuse PIR.Outcome; there is no primitive executor. -/

namespace Zkc.Source.Structured

/-- Convert a local return-or-stop to the existing process meaning. -/
def primitiveOutcome {I : PIR.Signature} {A : Type} : PIR.Outcome A → PIR.Process I A
  | .returned value => .done value
  | .stopped reason => .halt reason

/-- Arithmetic ingress is checked even for comparisons and unused results. -/
def checkedIndices {A : Type} (a b : Nat) (result : PIR.Outcome A) : PIR.Outcome A :=
  if a < indexLimit ∧ b < indexLimit then result else .stopped .refused

def Primitive.evaluate {F G : Type} [CommRing F] [DecidableEq F] :
    (primitive : Primitive) → Values (assignment F G) primitive.arguments →
      PIR.Outcome (Values (assignment F G) primitive.results)
  | .indexConstant n, .nil =>
      if n < indexLimit then .returned (.cons n .nil) else .stopped .refused
  | .indexEqual, .cons a (.cons b .nil) =>
      checkedIndices a b (.returned (.cons (decide (a = b)) .nil))
  | .indexLess, .cons a (.cons b .nil) =>
      checkedIndices a b (.returned (.cons (decide (a < b)) .nil))
  | .indexAdd, .cons a (.cons b .nil) =>
      checkedIndices a b (if a + b < indexLimit then .returned (.cons (a + b) .nil)
        else .stopped .refused)
  | .indexMul, .cons a (.cons b .nil) =>
      checkedIndices a b (if a * b < indexLimit then .returned (.cons (a * b) .nil)
        else .stopped .refused)
  | .indexSub, .cons a (.cons b .nil) =>
      checkedIndices a b (if b ≤ a then .returned (.cons (a - b) .nil) else .stopped .refused)
  | .indexDiv, .cons a (.cons b .nil) =>
      checkedIndices a b (if b = 0 then .stopped .refused else .returned (.cons (a / b) .nil))
  | .indexMod, .cons a (.cons b .nil) =>
      checkedIndices a b (if b = 0 then .stopped .refused else .returned (.cons (a % b) .nil))
  | .vectorEmpty _, .nil => .returned (.cons [] .nil)
  | .vectorLength _, .cons xs .nil =>
      if xs.length < indexLimit then .returned (.cons xs.length .nil) else .stopped .exhausted
  | .vectorSum _, .cons xs .nil => .returned (.cons (xs.foldl (· + ·) 0) .nil)
  | .vectorSplit _, .cons xs .nil =>
      if xs.length > 0 ∧ xs.length % 2 = 0 then
        .returned (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
      else .stopped .refused
  | .vectorAppend _, .cons xs (.cons x .nil) => .returned (.cons (xs ++ [x]) .nil)
  | .vectorEqual _, .cons xs (.cons ys .nil) => .returned (.cons (decide (xs = ys)) .nil)
  | .fieldEqual _, .cons x (.cons y .nil) => .returned (.cons (decide (x = y)) .nil)

attribute [local simp] Primitive.evaluate

end Zkc.Source.Structured
