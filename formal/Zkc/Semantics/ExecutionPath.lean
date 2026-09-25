import Zkc.Semantics.Interaction

set_option autoImplicit false
namespace PIR.ExecutionPath
variable {I : Signature} {S E A : Type}

/-- Record the phase of every actual invocation. Terminal provider outcomes
    retain that phase; they do not fabricate a typed reply transition. -/
def handler (P : Interaction I) (h : Handler I S E) :
    Handler I (P.Phase × S) (Sum (P.Phase × I.Op) E) := fun o st =>
  let out := h o st.2
  ⟨out.outcome, ((match out.outcome with
    | .returned a => P.advance st.1 o a
    | .stopped _ => st.1), out.state),
    .inl (st.1,o) :: out.events.map Sum.inr⟩

/-- The audit is semantic instrumentation: its original-event/state projection
    is exactly the uninstrumented interpreter, including terminal failure. -/
theorem erasure (P : Interaction I) (h : Handler I S E) (p : Proc I A)
    (phase : P.Phase) (s : S) :
    let out := p.run (handler P h) (phase,s)
    (⟨out.outcome,out.state.2,out.events.filterMap (fun
      | .inl _ => none | .inr e => some e)⟩ : Execution S E A) = p.run h s := by
  induction p generalizing phase s with
  | done a => rfl
  | halt why => rfl
  | call o k ih =>
    simp only [Proc.run,handler]
    cases hx : h o s with
    | mk outcome t es =>
      cases outcome with
      | stopped why => simp [Execution.follow,Function.comp_def]
      | returned a =>
        simp only [Execution.follow]
        have tail := ih a (P.advance phase o a) t
        cases ht : (k a).run (handler P h) (P.advance phase o a,t) with
        | mk result last events =>
          simp only [ht] at tail ⊢
          rw [← tail]
          simp [List.filterMap_append,Function.comp_def]

/-- Conformance applies to actual returned replies of any handler. No success,
    total-progress, honest-payload or provider-distribution premise is added. -/
theorem calls_permitted (P : Interaction I) (h : Handler I S E) (p : Proc I A)
    (phase : P.Phase) (s : S) (formed : Conforms P p phase) :
    ∀ before o, Sum.inl (before,o) ∈ (p.run (handler P h) (phase,s)).events →
      P.enabled before o := by
  induction p generalizing phase s with
  | done a => simp [Proc.run]
  | halt why => simp [Proc.run]
  | call op k ih =>
    simp only [Proc.run,handler]
    cases hx : h op s with
    | mk outcome t es =>
      cases outcome with
      | stopped why =>
        simpa [Execution.follow] using formed.1
      | returned a =>
        intro before o member
        simp only [Execution.follow,List.mem_append,List.mem_cons] at member
        rcases member with (first | emitted) | later
        · cases first
          exact formed.1
        · simp at emitted
        · exact ih a (P.advance phase op a) t (formed.2 a) before o later

end PIR.ExecutionPath

namespace PIR.ExecutionPath
variable {I : Signature} {S E A : Type}

/-- A public all-reply bound limits actual invocations, including the call that
    stops. The count is independent of the number of events emitted by a call
    and does not measure the handler's internal work. See
    docs/spec/core/execution.md, "the bound counts reached handler
    invocations, including the stopping invocation". -/
theorem calls_bounded (P : Interaction I) (h : Handler I S E) (p : Proc I A)
    (n : Nat) (phase : P.Phase) (s : S) (bounded : Within n p) :
    ((p.run (handler P h) (phase,s)).events.filterMap (fun
      | .inl call => some call | .inr _ => none)).length ≤ n := by
  induction p generalizing n phase s with
  | done a => simp [Proc.run]
  | halt why => simp [Proc.run]
  | call op k ih =>
    cases n with
    | zero => exact False.elim bounded
    | succ n =>
      simp only [Proc.run,handler]
      cases hx : h op s with
      | mk outcome t events =>
        have erased : events.filterMap (fun _ => (none : Option (P.Phase × I.Op))) = [] := by
          simp
        cases outcome with
        | stopped why => simp [Execution.follow,Function.comp_def,erased]
        | returned a =>
          have tail := ih a n (P.advance phase op a) t (bounded a)
          simpa [Execution.follow,List.filterMap_append,Function.comp_def,erased] using
            Nat.succ_le_succ tail

/-- An explicit observer history in state accumulates all actual events even
    when a handler stops. This law does not reconstruct a lost state afterward. -/
theorem run_recorded (log : S → List E) (h : Handler I S E)
    (records : ∀ o s, log (h o s).state = log s ++ (h o s).events)
    (p : Proc I A) (s : S) : log (p.run h s).state = log s ++ (p.run h s).events := by
  induction p generalizing s with
  | done a => simp [Proc.run]
  | halt why => simp [Proc.run]
  | call o k ih =>
    have step := records o s
    simp only [Proc.run]
    cases hx : h o s with
    | mk outcome t events =>
      simp only [hx] at step
      cases outcome with
      | stopped why => exact step
      | returned a =>
        change log ((k a).run h t).state = log s ++ (events ++ ((k a).run h t).events)
        rw [ih,step,List.append_assoc]

end PIR.ExecutionPath
