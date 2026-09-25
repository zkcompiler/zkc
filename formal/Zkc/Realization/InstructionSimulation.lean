import Zkc.Realization.InstructionSequence

/-! State simulation for instruction sequences, retaining exact terminal exits and events. -/

set_option autoImplicit false

namespace Zkc.Realization.InstructionSequence

variable {S T E Op : Type}

inductive Lift (R : S → T → Prop) : Step S E → Step T E → Prop where
  | next {s t es} : R s t → Lift R (.next s es) (.next t es)
  | halt {s t es x} : R s t → Lift R (.halt x s es) (.halt x t es)
def TerminalRel (R : S → T → Prop) (x : Terminal S E) (y : Terminal T E) : Prop :=
  x.outcome = y.outcome ∧ R x.state y.state ∧ x.events = y.events
/-- Both exhaustion and every halt preserve the terminal state relation. -/
theorem simulation (l : Op → S → Step S E) (r : Op → T → Step T E)
    (R : S → T → Prop) (hloc : ∀ op s t, R s t → Lift R (l op s) (r op t))
    (ops : List Op) (s : S) (t : T) (h : R s t) :
    TerminalRel R (run l ops s) (run r ops t) := by
  have handlers : PIR.HandlerRelated R (fun e => [e]) (fun e => [e])
      (sourceHandler l) (sourceHandler r) := by
    intro op s t related
    have stepLaw := hloc op s t related
    cases hl : l op s <;> cases hr : r op t <;> rw [hl, hr] at stepLaw
    · simp only [sourceHandler, hl, hr]
      cases stepLaw with
      | next states => exact ⟨rfl, states, rfl⟩
    · cases stepLaw
    · cases stepLaw
    · simp only [sourceHandler, hl, hr]
      cases stepLaw with
      | halt states => exact ⟨rfl, states, rfl⟩
  have result := PIR.run_related R (fun e => [e]) (fun e => [e])
    (sourceHandler l) (sourceHandler r) handlers (source ops) s t h
  rw [execution_exact, execution_exact] at result
  exact ⟨PIR.Outcome.returned.inj result.outcome, result.state,
    by simpa [PIR.observeEvents, Terminal.toExecution] using result.events⟩

theorem lift_map {S T E : Type} (f : S → T) (a : Step S E) :
    Lift (fun s t => f s = t) a (mapStep f a) := by
  cases a <;> constructor <;> rfl


end Zkc.Realization.InstructionSequence
