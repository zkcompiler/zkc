import Zkc.Source.Interpretation
import Zkc.Semantics.InterpretationAdmission
import Mathlib.Algebra.Ring.Basic

/-! A structured source for quadratic algebraic rounds.

Each message is checked before requesting a challenge. This is the round
component: statement evaluation and final acceptance are separate consumers.
All typed messages are allowed; no honesty predicate filters received values.
-/

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds

open PIR Source

structure Message (F : Type) where
  constant : F
  linear : F
  quadratic : F
  deriving DecidableEq, Repr

variable {F : Type}

def Message.evaluate [Semiring F] (message : Message F) (challenge : F) : F :=
  message.constant + (message.linear * challenge + message.quadratic * (challenge * challenge))

def Message.boundary [Semiring F] (message : Message F) : F :=
  message.evaluate 0 + message.evaluate 1

inductive Role where | prover | verifier
  deriving DecidableEq, Repr

inductive Call where | message | challenge | reject
  deriving DecidableEq, Repr

abbrev interface (F : Type) : Signature := ⟨Call, fun
  | .message => Message F
  | .challenge => F
  | .reject => Unit⟩

variable [Semiring F] [DecidableEq F]

/-- An independently recursive logical round process, used to specify the
structured source's execution meaning. It includes the rejected prefix. -/
def rounds : Nat → F → Proc (interface F) F
  | 0, claim => .done claim
  | count + 1, claim => .call .message fun message =>
      if message.boundary = claim then
        .call .challenge fun challenge => rounds count (message.evaluate challenge)
      else .call .reject fun _ => .halt .reject

inductive Ty where | scalar | message | boolean | unit
  deriving DecidableEq, Repr

inductive Op where | receive | draw | check | evaluate | reject
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .receive | .draw | .reject => []
  | .check => [.message, .scalar]
  | .evaluate => [.message, .scalar]

def result : Op → Ty
  | .receive => .message
  | .draw | .evaluate => .scalar
  | .check => .boolean
  | .reject => .unit

abbrev language : Language := ⟨Ty, Op, arguments, result, .boolean⟩

abbrev Value (F : Type) : Ty → Type
  | .scalar => F
  | .message => Message F
  | .boolean => Bool
  | .unit => Unit

abbrev meaning : Interpretation language (interface F) where
  Value := Value F
  condition := id
  operation
    | .receive, .nil => .call .message .done
    | .draw, .nil => .call .challenge .done
    | .reject, .nil => .call .reject .done
    | .check, .cons message (.cons claim .nil) => .done (decide (message.boundary = claim))
    | .evaluate, .cons message (.cons challenge .nil) => .done (message.evaluate challenge)

/-- The outer context remains explicit through the loop body and its captures. -/
def roundBody {Γ : List Ty} : Program language (.scalar :: Γ) .scalar :=
  .letOp .receive .nil
    (.letOp .check (.cons .here (.cons (.there .here) .nil))
      (.branch .here
        (.letOp .draw .nil
          (.letOp .evaluate (.cons (.there (.there .here)) (.cons .here .nil)) (.ret .here)))
        (.letOp .reject .nil (.stop .reject))))

def program (count : Nat) : Program language [.scalar] .scalar :=
  .iterate count .here roundBody (.ret .here)

theorem roundBody_denote {Γ : List Ty} (env : Environment (Value F) (.scalar :: Γ)) :
    roundBody.denote meaning env =
      .call .message (fun message =>
        if message.boundary = env .here then
          .call .challenge (fun challenge => .done (message.evaluate challenge))
        else .call .reject (fun _ => .halt .reject)) := by
  simp [roundBody, Program.denote, Operands.eval,
    Environment.push, meaning, Proc.bind, result]

theorem repeat_rounds (count : Nat) (claim : F) :
    repeatN (I := interface F) count (fun current =>
      .call .message (fun message : Message F =>
        if message.boundary = current then
          .call .challenge (fun challenge => .done (message.evaluate challenge))
        else .call .reject (fun _ => .halt .reject))) claim = rounds count claim := by
  induction count generalizing claim with
  | zero => rfl
  | succ count ih =>
    simp only [repeatN, rounds, Proc.bind]
    congr 1
    funext message
    split
    · simp only [Proc.bind]
      congr 1
      funext challenge
      exact ih _
    · rfl

theorem program_denote (count : Nat) (env : Environment (Value F) [.scalar]) :
    (program count).denote meaning env = rounds count (env .here) := by
  simp only [program, Program.denote, roundBody_denote, Environment.push]
  change (repeatN count _ (env .here)).bind Proc.done = _
  rw [Proc.bind_done, repeat_rounds]

inductive Phase (F : Type) where
  | message (remaining : Nat) (claim : F)
  | challenge (remaining : Nat) (message : Message F)
  | reject | finished

def start : Nat → F → Phase F
  | 0, _ => .finished
  | count + 1, claim => .message count claim

def interaction : Interaction (interface F) where
  Role := Role
  Phase := Phase F
  owner := fun | .message => .prover | _ => .verifier
  enabled phase op := match phase, op with
    | .message _ _, .message | .challenge _ _, .challenge | .reject, .reject => True
    | _, _ => False
  advance phase op reply := match phase, op with
    | .message count claim, .message =>
        if reply.boundary = claim then .challenge count reply else .reject
    | .challenge count message, .challenge => start count (message.evaluate reply)
    | _, _ => .finished

theorem formed (count : Nat) (claim : F) :
    Conforms interaction (rounds count claim) (start count claim) := by
  induction count generalizing claim with
  | zero => trivial
  | succ count ih =>
    refine ⟨trivial, ?_⟩
    intro message
    by_cases accepted : message.boundary = claim
    · simp only [Conforms, interaction, start, if_pos accepted]
      exact ⟨trivial, fun _ => ih _⟩
    · simp only [Conforms, interaction, start, if_neg accepted]
      exact ⟨trivial, fun _ => trivial⟩

theorem returns (count : Nat) (claim : F) :
    Boundary.Returns interaction (fun _ phase => phase = .finished)
      (rounds count claim) (start count claim) := by
  induction count generalizing claim with
  | zero => rfl
  | succ count ih =>
    intro message
    by_cases accepted : message.boundary = claim
    · simp only [Boundary.Returns, interaction, start, if_pos accepted]
      exact fun _ => ih _
    · simp [Boundary.Returns, interaction, accepted]

theorem bounded (count : Nat) (claim : F) : Within (2 * count) (rounds count claim) := by
  induction count generalizing claim with
  | zero => trivial
  | succ count ih =>
    rw [show 2 * (count + 1) = (2 * count + 1) + 1 by omega]
    intro message
    by_cases accepted : message.boundary = claim
    · simp only [if_pos accepted, Within]
      exact fun _ => ih _
    · simp [if_neg accepted, Within]

end Zkc.Protocols.AlgebraicRounds
