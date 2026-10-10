import Examples.OpeningReduction.Rounds
import Zkc.Source.Program
import Zkc.Compiler.Lowering
import Zkc.Semantics.Interpretation

/-! Structured verifier rounds return a residual claim, never acceptance.

Only a scalar claim and the public challenge prefix are inputs. Private tables
are absent from the vocabulary and interpretation. Opening discharge is a
separate consumer of the returned result.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Source
open PIR Zkc.Source

structure Accumulator (F : Type) where
  claim : F
  challenges : List F
  deriving Repr, DecidableEq

inductive Effect where | message | challenge | reject
  deriving DecidableEq, Repr

abbrev interface (F : Type) : Signature where
  Op := Effect
  Reply
    | .message => Message F
    | .challenge => F
    | .reject => Unit

inductive Ty where | accumulator | message | scalar | boolean | unit
  deriving DecidableEq, Repr

inductive Op where | receive | draw | check | advance | reject
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .receive | .draw | .reject => []
  | .check => [.message, .accumulator]
  | .advance => [.message, .scalar, .accumulator]

def result : Op → Ty
  | .receive => .message
  | .draw => .scalar
  | .check => .boolean
  | .advance => .accumulator
  | .reject => .unit

abbrev language : Language := ⟨Ty, Op, arguments, result, .boolean⟩

abbrev Value (F : Type) : Ty → Type
  | .accumulator => Accumulator F
  | .message => Message F
  | .scalar => F
  | .boolean => Bool
  | .unit => Unit

variable {F : Type} [CommRing F] [DecidableEq F]

def advance (message : Message F) (r : F) (acc : Accumulator F) : Accumulator F :=
  ⟨message.eval r, acc.challenges ++ [r]⟩

abbrev meaning : Interpretation language (interface F) where
  Value := Value F
  condition := id
  operation
    | .receive, .nil => .call .message .done
    | .draw, .nil => .call .challenge .done
    | .reject, .nil => .call .reject .done
    | .check, .cons message (.cons acc .nil) => .done (decide (message.boundary = acc.claim))
    | .advance, .cons message (.cons r (.cons acc .nil)) => .done (advance message r acc)

def roundBody {Γ : List Ty} : Program language (.accumulator :: Γ) .accumulator :=
  .letOp .receive .nil
    (.letOp .check (.cons .here (.cons (.there .here) .nil))
      (.branch .here
        (.letOp .draw .nil
          (.letOp .advance (.cons (.there (.there .here))
            (.cons .here (.cons (.there (.there (.there .here))) .nil))) (.ret .here)))
        (.letOp .reject .nil (.stop .reject))))

def program (count : Nat) : Program language [.accumulator] .accumulator :=
  .iterate count .here roundBody (.ret .here)

def rounds : Nat → Accumulator F → Proc (interface F) (Accumulator F)
  | 0, acc => .done acc
  | count + 1, acc => .call .message fun message =>
      if message.boundary = acc.claim then .call .challenge fun r => rounds count (advance message r acc)
      else .call .reject fun _ => .halt .reject

theorem roundBody_denote {Γ : List Ty} (env : Environment (Value F) (.accumulator :: Γ)) :
    roundBody.denote meaning env =
      .call .message (fun message => if message.boundary = (env .here).claim then
        .call .challenge (fun r => .done (advance message r (env .here)))
        else .call .reject (fun _ => .halt .reject)) := by
  simp [roundBody, Program.denote, Operands.eval, Environment.push, meaning, Proc.bind, result]

theorem repeat_rounds (count : Nat) (acc : Accumulator F) :
    repeatN (I := interface F) count (fun current =>
      .call .message (fun message : Message F => if message.boundary = current.claim then
        .call .challenge (fun r => .done (advance message r current))
        else .call .reject (fun _ => .halt .reject))) acc = rounds count acc := by
  induction count generalizing acc with
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

theorem program_denote (count : Nat) (env : Environment (Value F) [.accumulator]) :
    (program count).denote meaning env = rounds count (env .here) := by
  simp only [program, Program.denote, roundBody_denote, Environment.push]
  rw [repeat_rounds]
  change (rounds count (env .here)).bind Proc.done = _
  exact Proc.bind_done _

/-- Uniform interface calls, including rejection; not a polynomial-time bound. -/
theorem rounds_within (count : Nat) (acc : Accumulator F) :
    Within (2 * count) (rounds count acc) := by
  induction count generalizing acc with
  | zero => trivial
  | succ count ih =>
      have size : 2 * (count + 1) = (2 * count + 1) + 1 := by omega
      rw [size, rounds]
      intro message
      dsimp only
      split
      · intro r; exact ih _
      · intro _; change Within (2 * count) (.halt .reject : Proc (interface F) (Accumulator F))
        cases 2 * count <;> trivial

/-- The existing generic lowering theorem applies to this non-scalar result. -/
theorem lower_correct {S E : Type} (handler : Handler (interface F) S E)
    (count : Nat) (env : Environment (Value F) [.accumulator]) (state : S) :
    (Zkc.Compiler.lower (program count)).run meaning handler env state =
      (rounds count (env .here)).run handler state := by
  rw [Zkc.Compiler.lower_correct, program_denote]

end Examples.OpeningReduction.Source
