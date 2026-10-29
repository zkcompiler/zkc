module

public import Zkc.Obligations.RepeatedComponent
public import ZkcSecurity.FiatShamir.CostComposition
public import ZkcSecurity.Obligations.WeakestPrecondition

@[expose] public section

/-! History-dependent loop cost obligations for the same installed component.
The existing cost WP allocates the suffix budget at the actual reached history,
without a uniform envelope over unreachable histories. Frames are independent
all-replies facts. No new execution, probability or cost interpretation is used.
-/

set_option autoImplicit false
namespace ZkcSecurity.Obligations.RepeatedComponent
open Std.WP Zkc.Transcript Zkc.Obligations ZkcSecurity.FiatShamir
open ZkcSecurity.Obligations.WeakestPrecondition
variable {I : PIR.Signature} {E P R A : Type} {Raw : E → Type}
  {absorb : Interface I E P Raw} {charge : List E → E → ENNReal}

/-- Attach an independently established all-replies frame to the cost reading.
The frame is not inferred from a No predicate or from successful honest input. -/
theorem costWP_frame (process : PIR.Process I A) (frame : A → Prop)
    (preserves : PIR.Yields frame process)
    (post : A → List E → ENNReal → Prop)
    (epost : EStack⟨PIR.Stop → List E → ENNReal → Prop⟩) :
    ∀ history budget, costWP absorb charge process post epost history budget →
      costWP absorb charge process (fun value history budget => frame value ∧ post value history budget)
        epost history budget := by
  induction process with
  | done value => exact fun _ _ holds => ⟨preserves, holds⟩
  | halt => exact fun _ _ holds => holds
  | call operation continuation ih =>
    intro history budget bounded
    rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
      ⟨event, decode⟩ | _
    all_goals simp only [costWP, PIR.Process.foldReplies, costNode, absorbed] at bounded ⊢
    · exact fun message value recovered => ih value (preserves value) _ _ (bounded message value recovered)
    · exact ih value (preserves value) _ _ bounded
    · obtain ⟨remaining, allocated, tails⟩ := bounded
      exact ⟨remaining, allocated, fun value => ih value (preserves value) _ _ (tails value)⟩

variable (component : ComponentInterface I E R R)

/-- Each successful step reserves enough remaining budget for the next step at
its reached history. This is the existing cost WP with a budget postcondition;
it permits prices that grow with transcript length and reply-dependent state.
A separate all-replies frame is required by `cost_repeatN`. -/
def CostContract (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (frame : Nat → R → Prop) (budget : Nat → List E → R → ENNReal) : Prop :=
  ∀ remaining history runtime, frame (remaining + 1) runtime →
    costWP absorb charge (component.body runtime)
      (fun returned reached available => budget remaining reached returned ≤ available)
      estack⟨fun _ _ _ => True⟩ history (budget (remaining + 1) history runtime)

theorem cost_repeatN (frame : Nat → R → Prop) (budget : Nat → List E → R → ENNReal)
    (preserves : Zkc.Obligations.RepeatedComponent.FrameContract component frame)
    (steps : CostContract component absorb charge frame budget) :
    ∀ count history runtime, frame count runtime →
      Typed.ChargedCostBound absorb charge (PIR.repeatN count component.body runtime)
        history (budget count history runtime) := by
  intro count
  induction count with
  | zero => intros; trivial
  | succ count ih =>
    intro history runtime holds
    apply (costWP_iff absorb charge _ _ _).mp
    change costWP absorb charge
      ((component.body runtime).bind (PIR.repeatN count component.body)) _ _ _ _
    have step := costWP_frame (component.body runtime) (frame count) (preserves count runtime holds)
      (fun returned reached available => budget count reached returned ≤ available)
      estack⟨fun _ _ _ => True⟩ history (budget (count + 1) history runtime)
      (steps count history runtime holds)
    unfold costWP at step ⊢
    rw [PIR.Process.foldReplies_bind]
    apply PIR.Process.foldReplies_mono (costNode_mono absorb charge) ?_ (fun _ _ _ proof => proof)
      (component.body runtime) history (budget (count + 1) history runtime) step
    intro returned reached available framed
    exact (costWP_iff absorb charge _ _ _).mpr
      (CostComposition.mono (ih reached returned framed.1) framed.2)

end ZkcSecurity.Obligations.RepeatedComponent
