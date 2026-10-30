module

public import Zkc.Construction.PairAcceptance
public import ZkcSecurity.Transformations.FiatShamir.TranscriptOracle

@[expose] public section

/-! Transport successful deterministic runs into a larger honest interpreter.

Only operations reached on a returning run need agree. In particular, a local
service refused by the deterministic handler cannot occur on such a run. This
lets existing readback proofs retain their exact proof buffers and observations
under arbitrary private-service interpreters, without a second evaluator.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.ReadbackTransport
open Zkc.Source Zkc.Construction OracleComp OracleSpec

variable {I : PIR.Signature} {S T E A : Type} {m : Type → Type}
  [Monad m] [LawfulMonad m]

def mapState (embed : S → T) (execution : PIR.Execution S E A) : PIR.Execution T E A :=
  ⟨execution.outcome, embed execution.state, execution.events⟩

/-- Agreement on returning operations suffices for a returning whole run.
No conclusion is made about a stopped run under a larger interpreter. -/
theorem runM_of_returned (embed : S → T) (reference : PIR.Handler I S E)
    (handler : PIR.MonadHandler m I T E)
    (agreement : ∀ operation state reply final events,
      reference operation state = ⟨.returned reply, final, events⟩ →
      handler operation (embed state) = pure ⟨.returned reply, embed final, events⟩)
    (process : PIR.Process I A) (state : S) (value : A)
    (returned : (process.run reference state).outcome = .returned value) :
    process.runM handler (embed state) = pure (mapState embed (process.run reference state)) := by
  induction process generalizing state with
  | done result => rfl
  | halt reason => cases returned
  | call operation next ih =>
      cases observed : reference operation state with
      | mk outcome final events =>
          cases outcome with
          | stopped reason =>
              simp [PIR.Process.run, observed, PIR.Execution.follow] at returned
          | returned reply =>
              have continued : ((next reply).run reference final).outcome = .returned value := by
                simpa only [PIR.Process.run, observed, PIR.Execution.follow] using returned
              simp only [PIR.Process.runM, agreement operation state reply final events observed,
                pure_bind, PIR.Execution.followM, ih reply final continued, PIR.Process.run,
                observed, PIR.Execution.follow, mapState]

variable {carriers : Structured.Carriers}

/-- Fix public answers without changing the private service state or its law. -/
def tableOracle (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    Domain.Oracle m carriers S := fun history event state =>
  pure (.returned (Typed.readTable (R := Typed.ByLast Domain.Raw) answers history event), state)

def restore (privateState : S) (state : Domain.RuntimeState carriers Unit) :
    Domain.RuntimeState carriers S := ⟨state.environment, state.proof, privateState⟩

/-- The old refusing interpreter and any installed services agree on every
returning deterministic operation, including exact public-query replies. -/
theorem handler_agreement
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (services : Domain.LocalServices m carriers S) (mode : Domain.Mode) (privateState : S)
    (operation : Domain.Effect carriers) (state : Domain.RuntimeState carriers Unit)
    (reply : (Domain.effects carriers).Reply operation)
    (final : Domain.RuntimeState carriers Unit) (events : List (Domain.Event carriers))
    (returned : Domain.handler mode (tableOracle (m := Id) answers) Domain.refuseLocal operation state =
      ⟨.returned reply, final, events⟩) :
    Domain.handler mode (tableOracle answers) services operation (restore privateState state) =
      pure ⟨.returned reply, restore privateState final, events⟩ := by
  cases operation with
  | checkpoint environment | observe event =>
      cases returned
      rfl
  | localService port origin =>
      simp [Domain.handler, Domain.refuseLocal] at returned
      cases returned
  | send site schema peer payload =>
      cases mode <;> cases returned <;> rfl
  | receive ty site schema peer =>
      cases mode with
      | producer => cases returned
      | validator =>
          cases proof : state.proof with
          | nil => simp [Domain.handler, proof] at returned; cases returned
          | cons payload unread =>
              cases decoded : payload.value ty with
              | none => simp [Domain.handler, proof, decoded] at returned; cases returned
              | some value =>
                  simp only [Domain.handler, proof, decoded] at returned
                  cases returned
                  simp [Domain.handler, restore, proof, decoded]
  | query history origin =>
      simp only [Domain.handler] at returned ⊢
      split at returned
      · rename_i supported
        simp only [supported, ite_true, tableOracle] at returned ⊢
        cases returned
        simp [restore]
      · cases returned

/-- Retain the exact returned record of a table run, adding the actual private
state and arbitrary service interpreter. A successful refusing run uses neither. -/
theorem run_table_of_returned
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (services : Domain.LocalServices m carriers S) (mode : Domain.Mode) (privateState : S)
    (process : PIR.Process (Domain.effects carriers) A)
    (state : Domain.RuntimeState carriers Unit)
    (value : A) (final : Domain.RuntimeState carriers Unit) (events : List (Domain.Event carriers))
    (execution : process.run (Domain.handler mode (tableOracle (m := Id) answers)) state =
      ⟨.returned value, final, events⟩) :
    Domain.run mode (tableOracle answers) process (restore privateState state) services =
      pure ⟨.returned value, restore privateState final, events⟩ := by
  have transported := runM_of_returned (restore privateState)
    (Domain.handler mode (tableOracle (m := Id) answers))
    (Domain.handler mode (tableOracle answers) services)
    (handler_agreement answers services mode privateState) process state value
    (congrArg PIR.Execution.outcome execution)
  simpa only [Domain.run, execution, mapState] using transported

end ZkcSecurity.FiatShamir.ReadbackTransport
