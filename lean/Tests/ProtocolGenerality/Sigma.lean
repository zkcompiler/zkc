import Zkc.Source.Decoding
import Zkc.Compiler.Lowering
import Zkc.Semantics.Boundary
import Mathlib.Algebra.Module.Defs

/-! A three-message Sigma verifier in the shared structured source language.

Scalars and group points have different sorts. The source retains scalar action,
group addition and comparison as operations; its interaction has three separate
message/challenge boundaries. The algebraic completeness equation is conditional
on the module laws. No knowledge soundness, secrecy or Fiat-Shamir claim is made.
-/

set_option autoImplicit false

namespace Tests.ProtocolGenerality.Sigma

open PIR Zkc.Source Zkc.Compiler

inductive Ty where
  | scalar | point | boolean
  deriving DecidableEq

inductive Op where
  | commitment | challenge | response | scale | add | equal
  deriving DecidableEq

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .scale => [.scalar, .point]
    | .add | .equal => [.point, .point]
    | _ => []
  result
    | .commitment | .scale | .add => .point
    | .challenge | .response => .scalar
    | .equal => .boolean
  condition := .boolean

abbrev Value (F G : Type) : Ty → Type
  | .scalar => F
  | .point => G
  | .boolean => Bool

inductive Call where
  | commitment | challenge | response
  deriving DecidableEq

abbrev interface (F G : Type) : Signature := ⟨Call, fun
  | .commitment => G
  | .challenge | .response => F⟩

variable {F G : Type} [Semiring F] [AddCommMonoid G] [Module F G] [DecidableEq G]

abbrev meaning : Interpretation language (interface F G) where
  Value := Value F G
  condition := id
  operation
    | .commitment, .nil => .call .commitment .done
    | .challenge, .nil => .call .challenge .done
    | .response, .nil => .call .response .done
    | .scale, .cons scalar (.cons point .nil) => .done (scalar • point)
    | .add, .cons left (.cons right .nil) => .done (left + right)
    | .equal, .cons left (.cons right .nil) => .done (decide (left = right))

/-- Inputs are the generator and public statement. New values bind at position zero. -/
def raw : RawProgram Ty Op :=
  .letOp .commitment []
    (.letOp .challenge []
      (.letOp .response []
        (.letOp .scale [0, 3]
          (.letOp .scale [2, 5]
            (.letOp .add [4, 0]
              (.letOp .equal [2, 0] (.ret 0)))))))

def program : Program language [.point, .point] .boolean :=
  (raw.elaborate (language := language) [.point, .point] .boolean).toOption.get (by decide)

def inputs (generator statement : G) : Values (Value F G) [.point, .point] :=
  .cons generator (.cons statement .nil)

def reference (generator statement : G) : Proc (interface F G) Bool :=
  .call .commitment fun commitment =>
    .call .challenge fun challenge =>
      .call .response fun response =>
        .done (decide (response • generator = commitment + challenge • statement))

theorem denotes_verifier (generator statement : G) :
    program.denote meaning (inputs (F := F) generator statement).get =
      reference (F := F) generator statement := rfl

abbrev interaction : Interaction (interface F G) where
  Role := Bool
  Phase := Nat
  owner := fun | .challenge => false | _ => true
  enabled phase call := phase = match call with
    | .commitment => 0
    | .challenge => 1
    | .response => 2
  advance phase _ _ := phase + 1

theorem formed (generator statement : G) :
    Conforms interaction (program.denote meaning (inputs (F := F) generator statement).get) 0 := by
  rw [denotes_verifier]
  exact ⟨rfl, fun _ => ⟨rfl, fun _ => ⟨rfl, fun _ => trivial⟩⟩⟩

theorem bounded (generator statement : G) :
    Within 3 (program.denote meaning (inputs (F := F) generator statement).get) := by
  rw [denotes_verifier]
  exact fun _ _ _ => trivial

omit [DecidableEq G] in
/-- Actual group/scalar semantics, independent of any field encoding or polynomial model. -/
theorem honest_equation (generator : G) (witness nonce challenge : F) :
    (nonce + challenge * witness) • generator =
      nonce • generator + challenge • (witness • generator) := by
  rw [add_smul, mul_smul]

theorem plan_execution {S E : Type} (handler : Handler (interface F G) S E)
    (generator statement : G) (state : S) :
    (lower program).run meaning handler (inputs (F := F) generator statement).get state =
      (reference (F := F) generator statement).run handler state := by
  rw [lower_correct, denotes_verifier]

def honestHandler (generator : G) (witness nonce challenge : F) :
    Handler (interface F G) Unit Call
  | .commitment, state => ⟨.returned (nonce • generator), state, [.commitment]⟩
  | .challenge, state => ⟨.returned challenge, state, [.challenge]⟩
  | .response, state => ⟨.returned (nonce + challenge * witness), state, [.response]⟩

/-- The actual typed source and plan accept the honest statement, retaining the
three ordered interaction events. This is completeness, not a security reduction. -/
theorem honest_execution (generator : G) (witness nonce challenge : F) :
    (lower program).run meaning (honestHandler generator witness nonce challenge)
      (inputs generator (witness • generator)).get () =
      ⟨.returned true, (), [.commitment, .challenge, .response]⟩ := by
  rw [plan_execution]
  simp [reference, Proc.run, honestHandler, Execution.follow, honest_equation]

/-- The common interaction checker rejects a challenge requested before commitment. -/
example : ¬Conforms (interaction (F := F) (G := G))
    (.call .challenge (fun _ => .done ())) 0 := by
  intro conforming
  have impossible : (0 : Nat) = 1 := conforming.1
  contradiction

/-- Matching positions do not make a point a scalar. -/
example : ((RawProgram.letOp Op.scale [0, 1] (.ret 0)).elaborate
    (language := language) [.point, .point] .point).isOk = false := by decide

end Tests.ProtocolGenerality.Sigma
