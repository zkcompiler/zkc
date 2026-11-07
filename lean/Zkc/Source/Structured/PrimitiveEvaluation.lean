module

public import Zkc.Source.Structured.NumericalEvaluation
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

def Primitive.evaluateOn (model : FieldModel) :
    (primitive : Primitive) → Values model.Value primitive.arguments →
      PIR.Outcome (Values model.Value primitive.results)
  | .booleanNot => fun
    | .cons value .nil => .returned (.cons (!value) .nil)
  | .sequenceEmpty _ => fun
    | .nil => .returned (.cons [] .nil)
  | .sequenceAppend _ => fun
    | .cons values (.cons value .nil) => .returned (.cons (values ++ [value]) .nil)
  | .sequenceLength _ => fun
    | .cons values .nil =>
      if values.length < indexLimit then .returned (.cons values.length .nil)
      else .stopped .exhausted
  | .sequenceAt _ => fun
    | .cons values (.cons index .nil) =>
      match values[index]? with
      | some value => .returned (.cons value .nil)
      | none => .stopped .refused
  -- Restrict each fixed operation to its declared capability dependencies.
  -- This makes inverse transfer structural rather than an assumption about all operations.
  | .numerical op d base => fun args => Numerical.checkedEvaluateOn
      { model with inverse := if op.usesInverse then model.inverse else fun _ ↦ none }
      d base op args
  | .binaryConstant d bits => fun
    | .nil => Numerical.finish do
      return .cons (← Numerical.binaryValue { model with inverse := fun _ ↦ none } d bits) .nil
  | .indexConstant n => fun
    | .nil =>
      if n < indexLimit then .returned (.cons n .nil) else .stopped .refused
  | .indexEqual => fun
    | .cons a (.cons b .nil) =>
      checkedIndices a b (.returned (.cons (decide (a = b)) .nil))
  | .indexLess => fun
    | .cons a (.cons b .nil) =>
      checkedIndices a b (.returned (.cons (decide (a < b)) .nil))
  | .indexAdd => fun
    | .cons a (.cons b .nil) =>
      checkedIndices a b (if a + b < indexLimit then .returned (.cons (a + b) .nil)
        else .stopped .refused)
  | .indexMul => fun
    | .cons a (.cons b .nil) =>
      checkedIndices a b (if a * b < indexLimit then .returned (.cons (a * b) .nil)
        else .stopped .refused)
  | .indexSub => fun
    | .cons a (.cons b .nil) =>
      checkedIndices a b (if b ≤ a then .returned (.cons (a - b) .nil) else .stopped .refused)
  | .indexDiv => fun
    | .cons a (.cons b .nil) =>
      checkedIndices a b (if b = 0 then .stopped .refused else .returned (.cons (a / b) .nil))
  | .indexMod => fun
    | .cons a (.cons b .nil) =>
      checkedIndices a b (if b = 0 then .stopped .refused else .returned (.cons (a % b) .nil))
  | .vectorEmpty _ => fun
    | .nil => .returned (.cons [] .nil)
  | .vectorLength _ => fun
    | .cons xs .nil =>
      if xs.length < indexLimit then .returned (.cons xs.length .nil) else .stopped .exhausted
  | .vectorSum _ => fun
    | .cons xs .nil => .returned (.cons (xs.foldl (· + ·) 0) .nil)
  | .vectorSplit _ => fun
    | .cons xs .nil =>
      if xs.length > 0 ∧ xs.length % 2 = 0 then
        .returned (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
      else .stopped .refused
  | .vectorAppend _ => fun
    | .cons xs (.cons x .nil) => .returned (.cons (xs ++ [x]) .nil)
  | .vectorEqual _ => fun
    | .cons xs (.cons ys .nil) => .returned (.cons (decide (xs = ys)) .nil)
  | .fieldEqual _ => fun
    | .cons x (.cons y .nil) => .returned (.cons (decide (x = y)) .nil)

/-- The uniform interpretation is the exact ring-only specialization. -/
abbrev Primitive.evaluate {F G : Type} [CommRing F] [DecidableEq F] :=
  Primitive.evaluateOn (ringFieldModel F G)

attribute [local simp] Primitive.evaluateOn Primitive.evaluate

end Zkc.Source.Structured
