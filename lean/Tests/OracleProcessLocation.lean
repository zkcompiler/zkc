module

public import Zkc.Source.Structured.OracleProcessLocation
public import Tests.OracleProcessData

@[expose] public section
set_option autoImplicit false
namespace Tests.OracleProcessLocation
open Zkc.Source Zkc.Source.Structured OracleProcessData

def leafRequest (position : Nat) : OracleRead :=
  ⟨kind, anchor 0, position, location 9, [(anchor 2, location 7)]⟩

theorem baseLocated : OracleStore.Located runtime.entries baseTable [] :=
  ⟨[⟨.index, virtualTable 2 1⟩, ⟨.index, virtualTable 1 0⟩], rfl, by decide +kernel⟩

/-- Two newer virtual constructions do not replace this request, its source
path or the published base. No provider reply is fixed by the proof. -/
theorem actual_leaf {E : Type} (position : Fin 2) (state : Provider × Nat) :
    OracleProcess.answer (E := E) model 0 runtime.entries (leafRequest position) state =
      OracleProcess.mapResult (fun reply ↦
        ⟨reply.outcome, (reply.state, state.2 + 1),
          .query (leafRequest position) :: reply.events.map OracleEvent.provider⟩)
        (OracleProcess.baseCall (leafRequest position) state.1) :=
  OracleProcess.answer_base (leafRequest position) 2 0 [1] (some ([10, 20] : List Nat))
    baseLocated 0 rfl (by change OracleStore.validRows kind 2 = true; decide +kernel)
    position.isLt state

/-- The same source installation works for every lawful outer monad,
including adversarial branching, stopped replies and missing mass. -/
theorem actual_monadic_leaf {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}
    (external : PIR.MonadHandler m (OracleProcess.External model) Provider E)
    (position : Fin 2) (state : Provider × Nat) :
    OracleProcess.executeM external
      (OracleProcess.answer model 0 runtime.entries (leafRequest position) state) state =
      (do
        let reply ← external (.inr (leafRequest position)) state.1
        pure ⟨reply.outcome, (reply.state, state.2 + 1),
          .query (leafRequest position) :: reply.events.map OracleEvent.provider⟩) := by
  rw [actual_leaf, OracleProcess.executeM_base]

/-- An invalid position is refused before the external call, while recording
the attempted logical query and preserving the provider's current state. -/
theorem outside_refused {E : Type} (state : Provider × Nat) :
    OracleProcess.answer (E := E) model 0 runtime.entries (leafRequest 2) state =
      .done ⟨.stopped .refused, (state.1, state.2 + 1), [.query (leafRequest 2)]⟩ :=
  OracleProcess.answer_refused (leafRequest 2) baseTable baseLocated rfl 0 state
    (by decide +kernel)

/-- A later same-anchor installation is not a permitted store extension.
Even the same answer type cannot justify forgetting a changed admission row. -/
def shadow : OracleStoredTable model snapshot [] math .index :=
  {baseTable with rows := 0}

theorem shadowing_refuses {E : Type} (state : Provider × Nat) :
    OracleProcess.answer (E := E) model 0 (⟨.index, shadow⟩ :: runtime.entries)
      (leafRequest 0) state =
      .done ⟨.stopped .refused, (state.1, state.2 + 1), [.query (leafRequest 0)]⟩ :=
  OracleProcess.answer_refused (leafRequest 0) shadow (.head _ _) rfl 0 state
    (by decide +kernel)

theorem shadowing_changes (state : Provider × Nat) :
    OracleProcess.answer (E := Unit) model 0 (⟨.index, shadow⟩ :: runtime.entries)
      (leafRequest 0) state ≠
      OracleProcess.answer model 0 runtime.entries (leafRequest 0) state := by
  intro equal
  rw [shadowing_refuses, actual_leaf ⟨0, by decide⟩] at equal
  cases equal

#print axioms actual_monadic_leaf
#print axioms outside_refused
#print axioms shadowing_changes
#print axioms OracleProcess.answer_virtual
end Tests.OracleProcessLocation
