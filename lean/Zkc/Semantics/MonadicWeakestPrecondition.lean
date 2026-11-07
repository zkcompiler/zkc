module

public import Zkc.Semantics.WeakestPrecondition
public import Zkc.Semantics.MonadicPostcondition
public import Zkc.Semantics.HandlerReturn

@[expose] public section

/-! Verification conditions over the existing monadic runner. The assertion
sees the actual state and ordered event prefix on both returns and stops.
Outer aborts and missing probability mass remain properties of the selected
monad; this interface does not prove that an execution returns a record. -/
set_option autoImplicit false
namespace PIR.WeakestPrecondition
open Std.WP Lean.Order Std.Do.Internal
variable {I : Signature} {M : Type → Type} [Monad M] [LawfulMonad M] {S E A B : Type}

def runMWP (handler : MonadHandler M I S E) (process : Process I A)
    (post : A → S → List E → Prop) (epost : EStack⟨Stop → S → List E → Prop⟩)
    (state : S) (preceding : List E) : Prop :=
  Ensures (fun execution ↦ satisfies execution post epost.1 preceding) (process.runM handler state)

theorem runMWP_mono (handler : MonadHandler M I S E) (process : Process I A) :
    (⟨runMWP handler process⟩ :
      PredTrans (S → List E → Prop) EStack⟨Stop → S → List E → Prop⟩ A).monotone := by
  intro post post' epost epost' stopImplies returnImplies state preceding holds
  apply holds.weaken
  intro execution valid
  cases execution with
  | mk outcome final events =>
    cases outcome with
    | returned value => exact returnImplies value final (preceding ++ events) valid
    | stopped reason => exact stopImplies.1 reason final (preceding ++ events) valid

theorem runMWP_bind (handler : MonadHandler M I S E) (process : Process I A)
    (next : A → Process I B) (post : B → S → List E → Prop)
    (epost : EStack⟨Stop → S → List E → Prop⟩) :
    runMWP handler process (fun value ↦ runMWP handler (next value) post epost) epost ⊑
      runMWP handler (process.bind next) post epost := by
  intro state preceding holds
  change Ensures _ ((process.bind next).runM handler state)
  rw [runM_bind]
  apply holds.bind
  rintro ⟨outcome, current, events⟩ valid
  cases outcome with
  | stopped reason => exact Zkc.MonadicPostcondition.pure _ _ valid
  | returned value =>
    apply Zkc.MonadicPostcondition.map valid
    intro execution final
    cases execution with
    | mk outcome current tail =>
      cases outcome <;> simpa only [satisfies, List.append_assoc] using final

/-- Install locally: the program type alone does not choose an experiment. -/
@[reducible] def wpMonadM (handler : MonadHandler M I S E) :
    WPMonad (Process I) (S → List E → Prop) EStack⟨Stop → S → List E → Prop⟩ where
  toWP _ := { wpTrans := fun process ↦ ⟨runMWP handler process⟩,
              wp_trans_monotone := runMWP_mono handler }
  pure_le_wp_pure value post epost := by
    intro state preceding valid
    apply Zkc.MonadicPostcondition.pure
    simpa only [satisfies, List.append_nil] using valid
  bind_le_wp_bind process next post epost := runMWP_bind handler process next post epost

theorem tripleM_iff_run (handler : MonadHandler M I S E) (process : Process I A)
    (pre : S → List E → Prop) (post : A → S → List E → Prop)
    (stopped : Stop → S → List E → Prop) :
    (letI := wpMonadM handler
     Triple process pre post estack⟨stopped⟩) ↔
      ∀ state preceding, pre state preceding →
        Ensures (fun execution ↦ satisfies execution post stopped preceding) (process.runM handler state) := by
  letI := wpMonadM handler
  constructor
  · rintro ⟨holds⟩
    exact holds
  · intro holds
    exact ⟨holds⟩

/-- A deterministic instantiation checks the actual complete record. In
particular, a stop cannot satisfy a return-only specification. -/
theorem runMWP_id_iff (handler : MonadHandler Id I S E) (process : Process I A)
    (post : A → S → List E → Prop) (stopped : Stop → S → List E → Prop)
    (state : S) (preceding : List E) :
    runMWP (M := Id) handler process post estack⟨stopped⟩ state preceding ↔
      satisfies (process.runM (m := Id) handler state) post stopped preceding := by
  constructor
  · intro valid
    exact (MayReturn.of_canReturn (m := Id) (x := process.runM (m := Id) handler state) rfl).imp
      (P := fun record ↦ satisfies record post stopped preceding) valid
  · intro valid
    exact Zkc.MonadicPostcondition.pure _ _ valid

/-- An existing handler law becomes a local specification. The postcondition
on a stop remains explicit and need not imply the successful postcondition. -/
theorem callM_spec (handler : MonadHandler M I S E) (operation : I.Op)
    (post : I.Reply operation → S → List E → Prop) (stopped : Stop → S → List E → Prop) :
    (letI := wpMonadM handler
     Triple (Process.call operation .done)
       (fun state preceding ↦ Ensures (fun execution ↦ satisfies execution post stopped preceding)
         (handler operation state)) post estack⟨stopped⟩) := by
  apply (tripleM_iff_run _ _ _ _ _).mpr
  intro state preceding valid
  change Ensures _ (handler operation state >>= _)
  apply valid.bind
  rintro ⟨outcome, current, events⟩ holds
  cases outcome <;> simp only [Execution.followM, Process.runM, pure_bind, List.append_nil] <;>
    exact Zkc.MonadicPostcondition.pure _ _ holds

theorem haltM_spec (handler : MonadHandler M I S E) (reason : Stop)
    (post : A → S → List E → Prop) (stopped : Stop → S → List E → Prop) :
    (letI := wpMonadM handler
     Triple (Process.halt reason : Process I A) (stopped reason) post estack⟨stopped⟩) := by
  apply (tripleM_iff_run _ _ _ _ _).mpr
  intro state preceding holds
  exact Zkc.MonadicPostcondition.pure _ _ (by simpa only [satisfies, List.append_nil] using holds)

/-- Native process constructors expose the same monadic rules without
requiring the proof producer to rewrite the source's bind notation. -/
theorem bindM_spec (handler : MonadHandler M I S E) (process : Process I A)
    (next : A → Process I B) (post : B → S → List E → Prop)
    (stopped : Stop → S → List E → Prop) :
    (letI := wpMonadM handler
     Triple (process.bind next)
       (wp process (fun value ↦ wp (next value) post estack⟨stopped⟩)
         estack⟨stopped⟩) post estack⟨stopped⟩) := by
  letI := wpMonadM handler
  exact ⟨runMWP_bind handler process next post estack⟨stopped⟩⟩

theorem doneM_spec (handler : MonadHandler M I S E) (value : A)
    (post : A → S → List E → Prop) (stopped : Stop → S → List E → Prop) :
    (letI := wpMonadM handler
     Triple (Process.done value : Process I A) (post value) post estack⟨stopped⟩) := by
  apply (tripleM_iff_run _ _ _ _ _).mpr
  intro state preceding holds
  exact Zkc.MonadicPostcondition.pure _ _ (by simpa only [satisfies, List.append_nil] using holds)

end PIR.WeakestPrecondition

namespace PIR.Process
open Std.WP
variable {I : Signature} {M : Type → Type} [Monad M] [LawfulMonad M] {S E A : Type}

/-- A fixed-reply law is one usable specification, not the only form of
operation contract. It preserves its invariant on stopped executions too. -/
theorem ReturnsUnder.tripleM {handler : MonadHandler M I S E} {invariant : S → Prop}
    {process : Process I A} {expected : A}
    (law : ReturnsUnder handler invariant process expected) :
    (letI := WeakestPrecondition.wpMonadM handler
     Triple process (fun state _ ↦ invariant state)
       (fun value state _ ↦ invariant state ∧ value = expected)
       estack⟨fun _ state _ ↦ invariant state⟩) := by
  apply (WeakestPrecondition.tripleM_iff_run _ _ _ _ _).mpr
  intro state preceding valid
  apply (law state valid).weaken
  rintro ⟨outcome, current, events⟩ ⟨kept, agrees⟩
  cases outcome with
  | stopped reason => exact kept
  | returned value => exact ⟨kept, agrees value rfl⟩

end PIR.Process
