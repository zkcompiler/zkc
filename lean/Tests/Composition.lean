import Tests.SessionControls
import Zkc
import Zkc.Semantics.ContinuationReport

set_option autoImplicit false

/-! Public loop and continuation-report controls, using the shared session fixtures. -/
namespace PIR.Tests.Composition

open _root_.Tests.SessionControls

/-- A public loop preserves the value/phase invariant for every typed reply. -/
def counterSig : Signature := ⟨Unit, fun _ => Unit⟩
def counterPhase : Interaction counterSig :=
  ⟨Unit, Nat, fun _ => (), fun _ _ => True, fun n _ _ => n+1⟩
def increment (a : Nat) : Proc counterSig Nat := .call () fun _ => .done (a+1)

theorem public_repeat_formed (n a : Nat) :
    Conforms counterPhase (repeatN n increment a) a ∧
    Boundary.Returns counterPhase (fun value phase => value = phase)
      (repeatN n increment a) a := by
  apply Boundary.repeat_formed counterPhase increment (fun value phase => value = phase)
  · intro value phase _
    exact ⟨trivial, fun _ => trivial⟩
  · intro value phase same
    exact fun _ => congrArg (fun x : Nat => x+1) same
  · rfl

theorem public_repeat_bound (n a : Nat) : Within n (repeatN n increment a) := by
  simpa only [Nat.mul_one] using
    Boundary.repeat_bound increment 1 (fun _ _ => trivial) n a

/-- Return-phase postconditions alone say nothing about successful completion. -/
theorem stopped_has_any_return_postcondition :
    Boundary.Returns once (fun _ _ => False) (Proc.halt .abort : Proc sig Nat) false :=
  trivial

def abortingArm (_ : Nat) : Proc sig Nat := .call () fun _ => .halt .abort

/-- The report retains actual acceptance, prefix state, and failed arm separately. -/
theorem accepted_report_survives_arm_abort :
    let r := Continuation.runReport accepted abortingArm resultHandler 3
    r.verifier = ⟨.returned (.accepted 3),4,[3]⟩ ∧
    r.arm = some ⟨.stopped .abort,5,[4]⟩ ∧
    r.combined = ⟨.stopped .abort,5,[3,4]⟩ := ⟨rfl,rfl,rfl⟩

theorem rejected_report_has_no_arm :
    let r := Continuation.runReport rejected abortingArm resultHandler 3
    r.verifier.outcome = .returned .rejected ∧ r.arm = none ∧
    r.combined = ⟨.stopped .reject,4,[3]⟩ := ⟨rfl,rfl,rfl⟩

/-- Refusal is not relabeled as the verifier's negative decision. -/
theorem stopped_report_has_no_arm :
    let p : Proc sig (Continuation.Terminal Nat) := .halt .refused
    let r := Continuation.runReport p abortingArm resultHandler 3
    r.verifier.outcome = .stopped .refused ∧ r.arm = none ∧
    r.combined = ⟨.stopped .refused,3,[]⟩ := ⟨rfl,rfl,rfl⟩

/-- A privileged arbitrary arm can recreate a consumed entry. This witnesses
    the missing frame premise, not a defect in the state-preserving arm law. -/
theorem unframed_arm_can_restore_consumed_right :
    ((Continuation.take (7 : Nat) (some (7, ()))).follow
      (fun _ _ => (⟨.stopped .abort, some (7, ()), []⟩ :
        Execution (Option (Nat × Unit)) Unit Unit))).state = some (7, ()) := rfl

end PIR.Tests.Composition
