import Zkc.Protocols.Sumcheck.Transcript
import Zkc.Protocols.AlgebraicRounds.Fresh

/-! A typed whole-protocol verifier source.

The original polynomial is an actual input retained through the loop. The loop
carries a scalar claim and the actual ordered challenge list. Terminal checking
evaluates the original polynomial once, with exact arity. Residual polynomial
materialization belongs to the proof, not this verifier algorithm.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Source

open PIR Zkc.Source Zkc.Polynomial
open AlgebraicRounds (Message)

structure Accumulator (F : Type) where
  claim : F
  challenges : List F

inductive Ty where | accumulator | polynomial | message | scalar | boolean | unit
  deriving DecidableEq, Repr

inductive Op where | receive | draw | check | advance | reject | terminal
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .receive | .draw | .reject => []
  | .check => [.message, .accumulator]
  | .advance => [.message, .scalar, .accumulator]
  | .terminal => [.polynomial, .accumulator]

def result : Op → Ty
  | .receive => .message
  | .draw => .scalar
  | .check | .terminal => .boolean
  | .advance => .accumulator
  | .reject => .unit

abbrev language : Language := ⟨Ty, Op, arguments, result, .boolean⟩

abbrev Value (F : Type) (n : Nat) : Ty → Type
  | .accumulator => Accumulator F
  | .polynomial => Quadratic F n
  | .message => Message F
  | .scalar => F
  | .boolean => Bool
  | .unit => Unit

variable {F : Type} {n : Nat} [CommSemiring F] [DecidableEq F]

def advance (message : Message F) (r : F) (accumulator : Accumulator F) : Accumulator F :=
  ⟨message.evaluate r, accumulator.challenges ++ [r]⟩

def terminal (p : Quadratic F n) (accumulator : Accumulator F) : Bool :=
  decide (accumulator.challenges.length = n) &&
    decide (accumulator.claim = p.eval (coordinates n accumulator.challenges))

abbrev meaning : Interpretation language (AlgebraicRounds.interface F) where
  Value := Value F n
  condition := id
  operation
    | .receive, .nil => .call .message .done
    | .draw, .nil => .call .challenge .done
    | .reject, .nil => .call .reject .done
    | .check, .cons message (.cons accumulator .nil) =>
        .done (decide (message.boundary = accumulator.claim))
    | .advance, .cons message (.cons r (.cons accumulator .nil)) => .done (advance message r accumulator)
    | .terminal, .cons p (.cons accumulator .nil) => .done (terminal p accumulator)

def roundBody {Γ : List Ty} : Program language (.accumulator :: Γ) .accumulator :=
  .letOp .receive .nil
    (.letOp .check (.cons .here (.cons (.there .here) .nil))
      (.branch .here
        (.letOp .draw .nil
          (.letOp .advance (.cons (.there (.there .here))
            (.cons .here (.cons (.there (.there (.there .here))) .nil))) (.ret .here)))
        (.letOp .reject .nil (.stop .reject))))

/-- Both the initial claim and fixed polynomial come from the actual environment. -/
def program (count : Nat) : Program language [.accumulator, .polynomial] .boolean :=
  .iterate count .here roundBody
    (.letOp .terminal (.cons (.there (.there .here)) (.cons .here .nil)) (.ret .here))

def rounds : Nat → Accumulator F → Proc (AlgebraicRounds.interface F) (Accumulator F)
  | 0, accumulator => .done accumulator
  | count + 1, accumulator => .call .message fun message =>
      if message.boundary = accumulator.claim then .call .challenge fun r =>
        rounds count (advance message r accumulator)
      else .call .reject fun _ => .halt .reject

theorem roundBody_denote {Γ : List Ty} (env : Environment (Value F n) (.accumulator :: Γ)) :
    roundBody.denote meaning env =
      .call .message (fun message => if message.boundary = (env .here).claim then
        .call .challenge (fun r => .done (advance message r (env .here)))
        else .call .reject (fun _ => .halt .reject)) := by
  simp [roundBody, Program.denote, Operands.eval, Environment.push, meaning, Proc.bind, result]

theorem repeat_rounds (count : Nat) (accumulator : Accumulator F) :
    repeatN (I := AlgebraicRounds.interface F) count (fun current =>
      .call .message (fun message : Message F => if message.boundary = current.claim then
        .call .challenge (fun r => .done (advance message r current))
        else .call .reject (fun _ => .halt .reject))) accumulator = rounds count accumulator := by
  induction count generalizing accumulator with
  | zero => rfl
  | succ count ih =>
      simp only [repeatN, rounds, Proc.bind]
      congr 1
      funext message
      split
      · simp only [Proc.bind]
        congr 1
        funext r
        exact ih _
      · rfl

theorem program_denote (count : Nat) (env : Environment (Value F n) [.accumulator, .polynomial]) :
    (program count).denote meaning env =
      (rounds count (env .here)).bind (fun accumulator =>
        .done (terminal (env (.there .here)) accumulator)) := by
  simp only [program, Program.denote, roundBody_denote (n := n), Environment.push,
    Operands.eval, meaning, Proc.bind]
  rw [repeat_rounds]
  rfl

end Zkc.Protocols.Sumcheck.Source
