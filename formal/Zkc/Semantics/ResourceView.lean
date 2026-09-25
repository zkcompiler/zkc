import Zkc.Semantics.Execution

/-! A restricted heterogeneous store and its execution frame.
The admitted slots are an explicit semantic parameter. Static operands do not
establish admission, resource authenticity, freshness or absence of aliases.
Installation retains every selected post-state, including after a stop. -/
set_option autoImplicit false
namespace Zkc.Semantics.ResourceView

variable {Slot : Type} {Cell : Slot → Type} {I : PIR.Signature} {E A : Type}

abbrev Store (Cell : Slot → Type) := (slot : Slot) → Cell slot
abbrev Selected (Cell : Slot → Type) (admitted : Slot → Prop) :=
  (slot : Subtype admitted) → Cell slot.val

def restrict (admitted : Slot → Prop) (store : Store Cell) : Selected Cell admitted :=
  fun slot => store slot.val

def install (admitted : Slot → Prop) [DecidablePred admitted]
    (store : Store Cell) (selected : Selected Cell admitted) : Store Cell :=
  fun slot => if member : admitted slot then selected ⟨slot, member⟩ else store slot

@[simp] theorem install_selected (admitted : Slot → Prop) [DecidablePred admitted]
    (store : Store Cell) (selected : Selected Cell admitted)
    (slot : Slot) (member : admitted slot) :
    install admitted store selected slot = selected ⟨slot, member⟩ := by
  simp only [install, dif_pos member]

@[simp] theorem install_outside (admitted : Slot → Prop) [DecidablePred admitted]
    (store : Store Cell) (selected : Selected Cell admitted)
    (slot : Slot) (outside : ¬ admitted slot) :
    install admitted store selected slot = store slot := by
  simp only [install, dif_neg outside]

@[simp] theorem restrict_install (admitted : Slot → Prop) [DecidablePred admitted]
    (store : Store Cell) (selected : Selected Cell admitted) :
    restrict admitted (install admitted store selected) = selected := by
  funext slot
  exact install_selected admitted store selected slot.val slot.property

@[simp] theorem install_restrict (admitted : Slot → Prop) [DecidablePred admitted]
    (store : Store Cell) : install admitted store (restrict admitted store) = store := by
  funext slot
  by_cases member : admitted slot <;> simp [install, restrict, member]

/-- Equality at each selected slot and preservation of the initial outside frame.
The cell family may contain unrelated types, with no default inhabitants. -/
def Frame (admitted : Slot → Prop) (initial : Store Cell)
    (selected : Selected Cell admitted) (store : Store Cell) : Prop :=
  restrict admitted store = selected ∧
    ∀ slot, ¬ admitted slot → store slot = initial slot

/-- Reinstall the actual residual view regardless of its terminal outcome. -/
def lift (admitted : Slot → Prop) [DecidablePred admitted] (store : Store Cell)
    (result : PIR.Execution (Selected Cell admitted) E A) : PIR.Execution (Store Cell) E A :=
  ⟨result.outcome, install admitted store result.state, result.events⟩

def scopeHandler (admitted : Slot → Prop) [DecidablePred admitted]
    (handler : PIR.Handler I (Selected Cell admitted) E) : PIR.Handler I (Store Cell) E :=
  fun op store => lift admitted store (handler op (restrict admitted store))

theorem handler_related (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell) (handler : PIR.Handler I (Selected Cell admitted) E) :
    PIR.HandlerRelated (Frame admitted initial) (fun e => [e]) (fun e => [e])
      handler (scopeHandler admitted handler) := by
  intro op selected store related
  rcases related with ⟨same, frame⟩
  simp only [scopeHandler, same]
  refine ⟨rfl, ⟨restrict_install admitted store _, ?_⟩, rfl⟩
  intro slot outside
  exact (install_outside admitted store _ slot outside).trans (frame slot outside)

/-- An actual use of PIR.run_related with distinct state spaces, through every
reply-dependent branch. It includes stopped executions and all emitted events. -/
theorem run_related (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell) (handler : PIR.Handler I (Selected Cell admitted) E)
    (program : PIR.Proc I A) :
    PIR.Related (Frame admitted initial) (fun e => [e]) (fun e => [e])
      (program.run handler (restrict admitted initial))
      (program.run (scopeHandler admitted handler) initial) :=
  PIR.run_related _ _ _ _ _ (handler_related admitted initial handler) _ _ _
    ⟨rfl, fun _ _ => rfl⟩

/-- The lifted whole run is exactly the child run with its residual view
installed once. In particular, failure is never implemented as rollback. -/
theorem run_scoped (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell) (handler : PIR.Handler I (Selected Cell admitted) E)
    (program : PIR.Proc I A) :
    program.run (scopeHandler admitted handler) initial =
      lift admitted initial (program.run handler (restrict admitted initial)) := by
  have related := run_related admitted initial handler program
  have states : (program.run (scopeHandler admitted handler) initial).state =
      install admitted initial (program.run handler (restrict admitted initial)).state := by
    funext slot
    by_cases member : admitted slot
    · rw [install_selected admitted initial _ slot member]
      exact congrFun related.state.1 ⟨slot, member⟩
    · rw [install_outside admitted initial _ slot member]
      exact related.state.2 slot member
  have events := related.events
  simp only [PIR.observeEvents] at events
  have outcomes := related.outcome
  generalize program.run handler (restrict admitted initial) = child at *
  generalize program.run (scopeHandler admitted handler) initial = whole at *
  cases child
  cases whole
  simp only [lift, PIR.Execution.mk.injEq] at *
  exact ⟨outcomes.symm, states, by simpa using events.symm⟩

theorem run_selected (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell) (handler : PIR.Handler I (Selected Cell admitted) E)
    (program : PIR.Proc I A) (slot : Slot) (member : admitted slot) :
    (program.run (scopeHandler admitted handler) initial).state slot =
      (program.run handler (restrict admitted initial)).state ⟨slot, member⟩ :=
  congrFun (run_related admitted initial handler program).state.1 ⟨slot, member⟩

theorem run_frame (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell) (handler : PIR.Handler I (Selected Cell admitted) E)
    (program : PIR.Proc I A) (slot : Slot) (outside : ¬ admitted slot) :
    (program.run (scopeHandler admitted handler) initial).state slot = initial slot :=
  (run_related admitted initial handler program).state.2 slot outside

theorem run_returned (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell) (handler : PIR.Handler I (Selected Cell admitted) E)
    (program : PIR.Proc I A) (value : A) (final : Selected Cell admitted) (events : List E)
    (returned : program.run handler (restrict admitted initial) = ⟨.returned value, final, events⟩) :
    program.run (scopeHandler admitted handler) initial =
      ⟨.returned value, install admitted initial final, events⟩ := by
  rw [run_scoped, returned]
  rfl

theorem run_stopped (admitted : Slot → Prop) [DecidablePred admitted]
    (initial : Store Cell) (handler : PIR.Handler I (Selected Cell admitted) E)
    (program : PIR.Proc I A) (reason : PIR.Stop) (final : Selected Cell admitted) (events : List E)
    (stopped : program.run handler (restrict admitted initial) = ⟨.stopped reason, final, events⟩) :
    program.run (scopeHandler admitted handler) initial =
      ⟨.stopped reason, install admitted initial final, events⟩ := by
  rw [run_scoped, stopped]
  rfl

end Zkc.Semantics.ResourceView
