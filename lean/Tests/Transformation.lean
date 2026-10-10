import Zkc.Compiler.Arithmetic.Horner
import Zkc.Compiler.Checking
import Mathlib.Data.ZMod.Basic

/-! A checked changed algorithm with retained captures, control and failed state.
The expected target is written independently of the transformation function.
-/

set_option autoImplicit false

namespace Tests.Transformation

open Zkc.Source Zkc.Compiler Zkc.Source.Arithmetic
open Zkc.Compiler.Arithmetic

abbrev context : List Ty := [.boolean, .scalar, .scalar, .scalar, .scalar]

def input : RawProgram Ty Op :=
  .branch 0
    (.letOp .quadratic [1, 2, 3, 4]
      (.iterate 3 .scalar 0 (.letOp .invoke [0] (.ret 0))
        (.letOp .add [0, 3] (.ret 0))))
    (.stop .reject)

def source : Program language context .scalar :=
  (input.elaborate (language := language) context .scalar).toOption.get (by decide)

def expected : RawProgram Ty Op :=
  .branch 0
    (.letOp .multiply [3, 4]
      (.letOp .add [3, 0]
        (.letOp .multiply [0, 6]
          (.letOp .add [4, 0]
            (.iterate 3 .scalar 0 (.letOp .invoke [0] (.ret 0))
              (.letOp .add [0, 6] (.ret 0)))))))
    (.stop .reject)

abbrev interface (F : Type) : PIR.Signature := ⟨F, fun _ => F⟩
def invoke {F : Type} (value : F) : PIR.Proc (interface F) F := .call value .done

def backend {F : Type} [Semiring F] [DecidableEq F] : PIR.Handler (interface F) Nat F :=
  fun value state =>
    ⟨if value = 0 then .stopped .abort else .returned (value + 1), state + 1, [value]⟩

example : (lower (Horner.rewrite source)).erase = expected := by decide

example : (checkDirect source expected).isSome = false := by decide

example : (checkTransformation
    (Horner.rule (invoke (F := ZMod 5)) backend context .scalar) source () expected).isSome = true := by
  decide

example : (checkTransformation
    (Horner.rule (invoke (F := ZMod 7)) backend context .scalar) source () expected).isSome = true := by
  decide

/-- The semiring proof applies at every runtime binding, not only these controls. -/
example {F : Type} [Semiring F] [DecidableEq F] (env : Environment (Value F) context)
    (state : Nat) :
    (lower (Horner.rewrite source)).run (interpretation invoke) backend env state =
      (source.denote (interpretation invoke) env).run backend state := by
  rw [lower_correct, Horner.denote_rewrite]

def values (enabled : Bool) (challenge : ZMod 5) : Values (Value (ZMod 5)) context :=
  .cons enabled (.cons 1 (.cons 2 (.cons 1 (.cons challenge .nil))))

example : (lower (Horner.rewrite source)).run (interpretation invoke) backend
    (values true 2).get 10 = ⟨.stopped .abort, 12, [4, 0]⟩ := rfl

example : (lower (Horner.rewrite source)).run (interpretation invoke) backend
    (values true 0).get 10 = ⟨.returned 0, 13, [1, 2, 3]⟩ := rfl

example : (lower (Horner.rewrite source)).run (interpretation invoke) backend
    (values false 2).get 10 = ⟨.stopped .reject, 10, []⟩ := rfl

def differentInput : Program language context .scalar :=
  ((RawProgram.ret 1 : RawProgram Ty Op).elaborate (language := language) context .scalar).toOption.get
    (by decide)

example : (checkTransformation
    (Horner.rule (invoke (F := ZMod 5)) backend context .scalar)
    differentInput () expected).isSome = false := by decide

example : (checkTransformation
    (Horner.rule (invoke (F := ZMod 5)) backend context .scalar)
    source () (.ret 1)).isSome = false := by decide

/-- Merely naming an operation multiply supplies none of the semiring laws. -/
abbrev unlawful : Interpretation language (interface Nat) where
  Value := Value Nat
  condition := id
  operation
    | .multiply, .cons _ (.cons _ .nil) => .done 0
    | op, args => (interpretation invoke).operation op args

def naturalInputs : Values (Value Nat) context :=
  .cons true (.cons 1 (.cons 2 (.cons 1 (.cons 2 .nil))))

example : ((source.denote unlawful naturalInputs.get).run backend 10).events ≠
    ((Horner.rewrite source).denote unlawful naturalInputs.get |>.run backend 10).events := by
  decide

end Tests.Transformation
