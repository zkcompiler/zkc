import Zkc.Protocols.CommitmentSessions.Modular

set_option autoImplicit false

namespace Zkc.Protocols.CommitmentSessions.Preparation
open Zkc.Modules.Preparation Zkc.Source.TablePreparation

abbrev SessionState := CommitmentSessions.State (List Nat)
/-- Commit/open machine, with preparation executed by the common
    register interpreter. Session messages and coins are never cached. -/
def interpretedProvider : CommitmentSessions.Provider (List Nat) where
  prepare := fun h => (provider (CommitmentSessions.Modular.key h)).1
  commit := fun _ t m r => CommitmentSessions.Modular.consume t m r
  verify := CommitmentSessions.Modular.provider.verify

/-- The source state carries the direct-build counter only as ghost reference
    bookkeeping; actual work/hits live exclusively in the generic handler. -/
def lower (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) : List CommitmentSessions.Action → SessionState →
    Program Key (List Nat) CommitmentSessions.Event SessionState
  | [],s => .done s
  | a :: rest,s =>
    let i := inputs a.sid
    if CommitmentSessions.needs (s.sessions a.sid) a.cmd then
      .request (CommitmentSessions.Modular.key i.key) fun table =>
        let next := CommitmentSessions.localTransition (interpretedProvider.verify i.key)
          (interpretedProvider.commit i.key table) i (s.sessions a.sid) a.cmd
        Modules.Preparation.emitAll (next.2.map (fun m => (a.sid,m)))
          (lower inputs rest (CommitmentSessions.finish s a next s.cache 1))
    else
      let next := CommitmentSessions.localTransition (interpretedProvider.verify i.key)
        (fun _ _ => 0) i (s.sessions a.sid) a.cmd
      Modules.Preparation.emitAll (next.2.map (fun m => (a.sid,m)))
        (lower inputs rest (CommitmentSessions.finish s a next s.cache 0))

/-- All finite action words, including cancellation, invalid and hostile opens,
    join the actual direct transition function at this interpreted provider. -/
theorem source_join (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (actions : List CommitmentSessions.Action) (s : SessionState) :
    (denote provider (lower inputs actions s)).1 = CommitmentSessions.run interpretedProvider inputs false actions s := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [lower,CommitmentSessions.run]
    split
    · rename_i h
      simp only [denote,Modules.Preparation.denote_emitAll_value]
      rw [ih]
      simp [CommitmentSessions.step,h,CommitmentSessions.acquire,interpretedProvider]
    · rename_i h
      rw [Modules.Preparation.denote_emitAll_value,ih]
      simp [CommitmentSessions.step,h]

theorem memo_source_trace (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (actions : List CommitmentSessions.Action) :
    (Modules.Preparation.run provider prices .memo (lower inputs actions CommitmentSessions.initial) Modules.Preparation.empty).value.trace =
    (CommitmentSessions.run interpretedProvider inputs false actions CommitmentSessions.initial).trace := by
  rw [(Modules.Preparation.simulation provider prices .memo _ Modules.Preparation.empty
    (Modules.ImmutableCache.empty_valid provider)).1,source_join]

theorem full_protocol_observer (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (actions : List CommitmentSessions.Action)
    {O : Type} (obs : List CommitmentSessions.Event → O) :
    obs (Modules.Preparation.run provider prices .direct (lower inputs actions CommitmentSessions.initial) Modules.Preparation.empty).value.trace =
    obs (Modules.Preparation.run provider prices .memo (lower inputs actions CommitmentSessions.initial) Modules.Preparation.empty).value.trace :=
  Modules.Preparation.observer provider prices _ (fun (s : SessionState) _ => obs s.trace)

/-- A scheduler sees only the source protocol trace, including hostile prior
    messages, and is unfolded to the SAME shared preparation program. -/
def adaptiveLower (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (scheduler : CommitmentSessions.Scheduler) :
    Nat → SessionState → Program Key (List Nat) CommitmentSessions.Event SessionState
  | 0,s => .done s
  | n+1,s => match scheduler s.trace with
    | none => .done s
    | some a => (lower inputs [a] s).bind (adaptiveLower inputs scheduler n)

theorem adaptive_source_join (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (scheduler : CommitmentSessions.Scheduler)
    (n : Nat) (s : SessionState) :
    (denote provider (adaptiveLower inputs scheduler n s)).1 =
    CommitmentSessions.adaptive interpretedProvider inputs false scheduler n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [adaptiveLower,CommitmentSessions.adaptive]
    cases scheduler s.trace with
    | none => rfl
    | some a =>
      rw [denote_bind_value,source_join,ih]
      rfl

theorem adaptive_protocol_observer (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (scheduler : CommitmentSessions.Scheduler)
    (n : Nat) {O : Type} (obs : List CommitmentSessions.Event → O) :
    obs (Modules.Preparation.run provider prices .memo (adaptiveLower inputs scheduler n CommitmentSessions.initial) Modules.Preparation.empty).value.trace =
    obs (CommitmentSessions.adaptive interpretedProvider inputs false scheduler n CommitmentSessions.initial).trace := by
  rw [(Modules.Preparation.simulation provider prices .memo _ Modules.Preparation.empty
    (Modules.ImmutableCache.empty_valid provider)).1,adaptive_source_join]

/-- Stored source history and actual emitted messages are separate projections.
    The new emits append exactly the reference messages, with arbitrary prior history. -/
theorem source_emissions (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (actions : List CommitmentSessions.Action) (s : SessionState) :
    s.trace ++ (denote provider (lower inputs actions s)).2.1 =
      (CommitmentSessions.run interpretedProvider inputs false actions s).trace := by
  induction actions generalizing s with
  | nil => simp [lower,denote,CommitmentSessions.run]
  | cons a rest ih =>
    simp only [lower]
    split
    · rename_i h
      simp only [denote,Modules.Preparation.denote_emitAll_trace]
      let i := inputs a.sid
      let step := CommitmentSessions.localTransition (interpretedProvider.verify i.key)
        (interpretedProvider.commit i.key (provider (CommitmentSessions.Modular.key i.key)).1) i (s.sessions a.sid) a.cmd
      have next := ih (CommitmentSessions.finish s a step s.cache 1)
      simpa [CommitmentSessions.run,CommitmentSessions.step,h,CommitmentSessions.acquire,interpretedProvider,CommitmentSessions.finish,step,i,List.append_assoc] using next
    · rename_i h
      rw [Modules.Preparation.denote_emitAll_trace]
      let i := inputs a.sid
      let step := CommitmentSessions.localTransition (interpretedProvider.verify i.key) (fun _ _ => 0) i (s.sessions a.sid) a.cmd
      have next := ih (CommitmentSessions.finish s a step s.cache 0)
      simpa [CommitmentSessions.run,CommitmentSessions.step,h,CommitmentSessions.finish,step,i,List.append_assoc] using next

theorem memo_emissions (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (actions : List CommitmentSessions.Action) :
    (Modules.Preparation.run provider prices .memo (lower inputs actions CommitmentSessions.initial) Modules.Preparation.empty).trace =
      (CommitmentSessions.run interpretedProvider inputs false actions CommitmentSessions.initial).trace := by
  rw [(Modules.Preparation.simulation provider prices .memo _ Modules.Preparation.empty
    (Modules.ImmutableCache.empty_valid provider)).2.1]
  simpa [CommitmentSessions.initial] using source_emissions inputs actions CommitmentSessions.initial

theorem adaptive_emissions (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (scheduler : CommitmentSessions.Scheduler)
    (fuel : Nat) (s : SessionState) :
    s.trace ++ (denote provider (adaptiveLower inputs scheduler fuel s)).2.1 =
      (CommitmentSessions.adaptive interpretedProvider inputs false scheduler fuel s).trace := by
  induction fuel generalizing s with
  | zero => simp [adaptiveLower,denote,CommitmentSessions.adaptive]
  | succ fuel ih =>
    simp only [adaptiveLower,CommitmentSessions.adaptive]
    cases hs : scheduler s.trace with
    | none => simp [denote]
    | some a =>
      rw [Modules.Preparation.denote_bind_trace,← List.append_assoc,source_emissions,source_join]
      exact ih _

theorem adaptive_memo_emissions (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input) (scheduler : CommitmentSessions.Scheduler)
    (fuel : Nat) :
    (Modules.Preparation.run provider prices .memo (adaptiveLower inputs scheduler fuel CommitmentSessions.initial) Modules.Preparation.empty).trace =
      (CommitmentSessions.adaptive interpretedProvider inputs false scheduler fuel CommitmentSessions.initial).trace := by
  rw [(Modules.Preparation.simulation provider prices .memo _ Modules.Preparation.empty
    (Modules.ImmutableCache.empty_valid provider)).2.1]
  simpa [CommitmentSessions.initial] using adaptive_emissions inputs scheduler fuel CommitmentSessions.initial

end Zkc.Protocols.CommitmentSessions.Preparation
