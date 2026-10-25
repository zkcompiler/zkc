module

public import ZkcSecurity.Families.Sumcheck.TableComponent

@[expose] public section

/-! Whole-Process binding through an indexed mathematical representation.

An exact one-round equation lifts to zero, partial and complete calls. The
equation retains every typed reply, operation and stop, including challenge
delivery. Its result projection must include all actual returned components;
it is not a relation on successful outcomes alone.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent

variable {F : Type} [Field F] [DecidableEq F] {I : PIR.Signature}
  {Context A B : Type} {State : Nat → Type} {message : Message F}
  (program : Program I Context State message)

theorem remaining_succ_bind {n : Nat} (count : Nat) (context : Context)
    (state : State (n + (count + 1))) :
    program.remaining (count + 1) context state =
      (program.remaining (n := n + count) 1 context state).bind
        (fun next => program.remaining (n := n) count context next) := by
  simp only [Program.remaining, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext decoded
  cases decoded with
  | none => rfl
  | some m =>
      dsimp only
      split
      · simp only [PIR.Process.bind, PIR.Process.bind_assoc]
      · rfl

/-- This is an equality of complete open processes after the explicit full
result map. No adversarial reply is identified with an honest message. -/
theorem remaining_readback (readback : {n : Nat} → State n → A)
    (context : Context) (step : A → PIR.Process I A)
    (one : ∀ {n} (state : State (n + 1)),
      (program.remaining (n := n) 1 context state).bind
        (fun result => .done (readback result)) = step (readback state))
    {n : Nat} (count : Nat) (state : State (n + count)) :
    (program.remaining count context state).bind (fun result => .done (readback result)) =
      PIR.repeatN count step (readback state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [remaining_succ_bind, PIR.Process.bind_assoc]
      calc
        _ = (program.remaining (n := n + count) 1 context state).bind
            (fun next => PIR.repeatN count step (readback next)) := by
              exact congrArg (PIR.Process.bind _) (funext fun next => ih next)
        _ = ((program.remaining (n := n + count) 1 context state).bind
            (fun result => .done (readback result))).bind
              (PIR.repeatN count step) := by
                simp only [PIR.Process.bind_assoc, PIR.Process.bind]
        _ = PIR.repeatN (count + 1) step (readback state) := by
              rw [one]
              rfl

/-- A source-owned terminal/output map composes with the same checked loop
binding used by both security consumers. -/
theorem remaining_terminal (readback : {n : Nat} → State n → A)
    (context : Context) (step : A → PIR.Process I A)
    (one : ∀ {n} (state : State (n + 1)),
      (program.remaining (n := n) 1 context state).bind
        (fun result => .done (readback result)) = step (readback state))
    (terminal : A → PIR.Process I B)
    {n : Nat} (count : Nat) (state : State (n + count)) :
    (program.remaining count context state).bind (fun result => terminal (readback result)) =
      (PIR.repeatN count step (readback state)).bind terminal := by
  rw [← remaining_readback program readback context step one count state]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]

end ZkcSecurity.Families.Sumcheck.TableComponent
