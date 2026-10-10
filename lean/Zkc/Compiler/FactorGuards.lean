import Zkc.Compiler.FactorExecution

set_option autoImplicit false
namespace Zkc.Compiler.FactorGuards
open PIR Zkc.Modules.FactorExecution
variable {K E : Type}

/-- Existing Enabled evidence covers the actual world read by this Zkc.Modules.FactorExecution.guard. -/
theorem enabled_execution (spec : Nat → Zkc.Modules.FactorState.Spec K) (impl : Nat → Zkc.Modules.FactorState.Implementation K E)
    (code : Zkc.Compiler.FactorProgram.Code) (s : Zkc.Modules.FactorState.World K)
    (enabled : Zkc.Compiler.FactorProgram.Enabled spec impl code s) :
    (Zkc.Compiler.FactorExecution.embed code).run (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler impl)) s =
      (Zkc.Compiler.FactorExecution.embed code).run (Zkc.Modules.FactorExecution.handler impl) s := by
  induction code generalizing s with
  | stop => rfl
  | demand q p next ih =>
    simp [Zkc.Compiler.FactorExecution.embed,Proc.run,Zkc.Modules.FactorExecution.guard,enabled.1,Zkc.Modules.FactorExecution.handler,Execution.follow,run_bind,ih s enabled.2]
  | call id yes no ihYes ihNo =>
    cases h : (impl id s).success with
    | false =>
      have en := enabled.2
      simp only [h,Bool.false_eq_true,↓reduceIte] at en
      simp [Zkc.Compiler.FactorExecution.embed,Proc.run,Zkc.Modules.FactorExecution.guard,Zkc.Modules.FactorExecution.handler,Zkc.Modules.FactorExecution.returned,Execution.follow,h,ihNo _ en]
    | true =>
      have en := enabled.2
      simp only [h,↓reduceIte] at en
      simp [Zkc.Compiler.FactorExecution.embed,Proc.run,Zkc.Modules.FactorExecution.guard,Zkc.Modules.FactorExecution.handler,Zkc.Modules.FactorExecution.returned,Execution.follow,h,ihYes _ en]

/-- Zkc.Modules.FactorState's enabledness is independent of which pure demand plan is chosen. -/
theorem enabled_plans (spec : Nat → Zkc.Modules.FactorState.Spec K) (impl : Nat → Zkc.Modules.FactorState.Implementation K E)
    (src : Zkc.Compiler.FactorProgram.Source) (s : Zkc.Modules.FactorState.World K) (facts : List Zkc.Modules.Factor.Fact) (available : List Nat) :
    Zkc.Compiler.FactorProgram.Enabled spec impl
      (Zkc.Compiler.FactorProgram.compile (fun id => (spec id).post) facts available src) s ↔
    Zkc.Compiler.FactorProgram.Enabled spec impl (Zkc.Compiler.FactorProgram.direct src) s := by
  induction src generalizing s facts available with
  | stop => rfl
  | demand q next ih =>
    exact and_congr Iff.rfl (ih s facts available)
  | call id yes no ihYes ihNo =>
    simp only [Zkc.Compiler.FactorProgram.compile,Zkc.Compiler.FactorProgram.direct,Zkc.Compiler.FactorProgram.Enabled]
    apply and_congr Iff.rfl
    cases h : (impl id s).success with
    | false => simp only [Bool.false_eq_true,↓reduceIte]; exact ihNo _ _ _
    | true => simp only [↓reduceIte]; exact ihYes _ _ _

theorem guarded_analysis (spec : Nat → Zkc.Modules.FactorState.Spec K) (impl : Nat → Zkc.Modules.FactorState.Implementation K E)
    (laws : ∀ id, Zkc.Modules.FactorState.Satisfies (spec id) (impl id))
    (src : Zkc.Compiler.FactorProgram.Source) (s : Zkc.Modules.FactorState.World K) (facts : List Zkc.Modules.Factor.Fact) (available : List Nat)
    (valid : Zkc.Modules.Factor.Valid s.values facts) (known : Zkc.Modules.FactorState.Known s available)
    (legal : Zkc.Compiler.FactorProgram.Legal spec impl available src s) :
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (spec id).post) facts available src)).run
      (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler impl)) s =
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)).run (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler impl)) s := by
  have ec := Zkc.Compiler.FactorProgram.compile_enabled spec impl laws src s facts available known legal
  have ed := (enabled_plans spec impl src s facts available).mp ec
  rw [enabled_execution spec impl _ s ec,enabled_execution spec impl _ s ed]
  exact Zkc.Compiler.FactorExecution.compiled_execution spec impl laws src s facts available valid known legal

/-- Only module calls reached before the first readiness refusal require their
    precondition. This is a semantic applicability predicate, not a static checker.
    The Zkc.Modules.FactorExecution.guard checks actual availability; the analysis may know less. -/
def CallsBeforeRefusal (spec : Nat → Zkc.Modules.FactorState.Spec K) (impl : Nat → Zkc.Modules.FactorState.Implementation K E) :
    Zkc.Compiler.FactorProgram.Source → Zkc.Modules.FactorState.World K → Prop
  | .stop, _ => True
  | .demand q next, s => Zkc.Modules.FactorState.Ready s.known q → CallsBeforeRefusal spec impl next s
  | .call id yes no, s =>
    (spec id).pre s ∧
      let out := impl id s
      if out.success then CallsBeforeRefusal spec impl yes out.world
      else CallsBeforeRefusal spec impl no out.world

/-- Legal callers satisfy the weaker reached-call predicate. No contracts or
    abstract availability are needed to forget the stronger legality requirement. -/
theorem legal_calls_before_refusal (spec : Nat → Zkc.Modules.FactorState.Spec K)
    (impl : Nat → Zkc.Modules.FactorState.Implementation K E) (src : Zkc.Compiler.FactorProgram.Source)
    (s : Zkc.Modules.FactorState.World K) (available : List Nat)
    (legal : Zkc.Compiler.FactorProgram.Legal spec impl available src s) :
    CallsBeforeRefusal spec impl src s := by
  induction src generalizing s available with
  | stop => trivial
  | demand q next ih => exact fun _ => ih s available legal.2
  | call id yes no ihYes ihNo =>
    refine ⟨legal.1, ?_⟩
    cases h : (impl id s).success with
    | false =>
      have branch := legal.2
      simp only [h, Bool.false_eq_true, ↓reduceIte] at branch ⊢
      exact ihNo _ _ branch
    | true =>
      have branch := legal.2
      simp only [h, ↓reduceIte] at branch ⊢
      exact ihYes _ _ branch

/-- Inference preserves the complete guarded execution, including state/events
    before an actual refusal. No premise is imposed on the unexecuted suffix. -/
theorem guarded_analysis_until_refusal (spec : Nat → Zkc.Modules.FactorState.Spec K)
    (impl : Nat → Zkc.Modules.FactorState.Implementation K E)
    (laws : ∀ id, Zkc.Modules.FactorState.Satisfies (spec id) (impl id))
    (src : Zkc.Compiler.FactorProgram.Source) (s : Zkc.Modules.FactorState.World K)
    (facts : List Zkc.Modules.Factor.Fact) (available : List Nat)
    (valid : Zkc.Modules.Factor.Valid s.values facts) (known : Zkc.Modules.FactorState.Known s available)
    (calls : CallsBeforeRefusal spec impl src s) :
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (spec id).post) facts available src)).run
      (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler impl)) s =
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)).run
      (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler impl)) s := by
  induction src generalizing s facts available with
  | stop => rfl
  | demand q next ih =>
    by_cases ready : Zkc.Modules.FactorState.Ready s.known q
    · have suffix := ih s facts available valid known (calls ready)
      simp only [Zkc.Compiler.FactorProgram.compile, Zkc.Compiler.FactorProgram.direct, Zkc.Compiler.FactorExecution.embed, Proc.run,
        Zkc.Modules.FactorExecution.guard, if_pos ready, Zkc.Modules.FactorExecution.handler, Execution.follow, run_bind]
      erw [Zkc.Compiler.FactorReuse.inferred_value s.values facts available q valid, suffix]
      rfl
    · simp [Zkc.Compiler.FactorProgram.compile, Zkc.Compiler.FactorProgram.direct, Zkc.Compiler.FactorExecution.embed, Proc.run,
        Zkc.Modules.FactorExecution.guard, ready, Execution.follow]
  | call id yes no ihYes ihNo =>
    have transfer := Zkc.Modules.FactorState.call_transfer (spec id) (impl id) (laws id)
      s facts available calls.1 valid known
    cases h : (impl id s).success with
    | false =>
      have branch := calls.2
      simp only [h, Bool.false_eq_true, ↓reduceIte] at branch transfer
      have suffix := ihNo _ _ _ transfer.1 transfer.2 branch
      simp [Zkc.Compiler.FactorProgram.compile, Zkc.Compiler.FactorProgram.direct, Zkc.Compiler.FactorExecution.embed, Proc.run,
        Zkc.Modules.FactorExecution.guard, Zkc.Modules.FactorExecution.handler, Zkc.Modules.FactorExecution.returned, Execution.follow, h, suffix]
    | true =>
      have branch := calls.2
      simp only [h, ↓reduceIte] at branch transfer
      have suffix := ihYes _ _ _ transfer.1 transfer.2 branch
      simp [Zkc.Compiler.FactorProgram.compile, Zkc.Compiler.FactorProgram.direct, Zkc.Compiler.FactorExecution.embed, Proc.run,
        Zkc.Modules.FactorExecution.guard, Zkc.Modules.FactorExecution.handler, Zkc.Modules.FactorExecution.returned, Execution.follow, h, suffix]

end Zkc.Compiler.FactorGuards
