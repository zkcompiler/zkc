import Zkc.Semantics.Preparation.Emission
import Zkc.Protocols.CommitmentSessions.Preparation

set_option autoImplicit false

namespace Zkc.Protocols.CommitmentSessions.Source
open PIR Zkc.Modules.Preparation Zkc.Source.TablePreparation Zkc.Protocols.CommitmentSessions.Preparation

/-- Adaptive scheduler lowering, now executed by the common PIR interpreter.
    Session cancellation/rejection/invalid attempts are returned source data. -/
def source (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input)
    (scheduler : CommitmentSessions.Scheduler) (horizon : Nat) (s : SessionState) :=
  PIR.Preparation.Emission.embed (adaptiveLower inputs scheduler horizon s)

def execute (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input)
    (scheduler : CommitmentSessions.Scheduler) (horizon : Nat) (s : SessionState) (mode : Mode) :=
  (source inputs scheduler horizon s).run
    (PIR.Preparation.handler provider prices mode PIR.Preparation.Emission.handler)
    (Modules.Preparation.empty, ())

/-- The source result and actual emissions both reach the existing machine.
    The direct-build field inside SessionState is reference bookkeeping; actual work
    is read from Preparation events, not from that field. -/
theorem execution_exact (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input)
    (scheduler : CommitmentSessions.Scheduler) (horizon : Nat) (s : SessionState) (mode : Mode) :
    (execute inputs scheduler horizon s mode).outcome =
      .returned (CommitmentSessions.adaptive interpretedProvider inputs false scheduler horizon s) ∧
    s.trace ++ observeEvents PIR.Preparation.view (execute inputs scheduler horizon s mode).events =
      (CommitmentSessions.adaptive interpretedProvider inputs false scheduler horizon s).trace := by
  have emb := PIR.Preparation.Emission.embedding_exact provider prices mode
    (adaptiveLower inputs scheduler horizon s) Modules.Preparation.empty
  have sim := Modules.Preparation.simulation provider prices mode
    (adaptiveLower inputs scheduler horizon s) Modules.Preparation.empty
      (Modules.ImmutableCache.empty_valid provider)
  dsimp only [execute,source]
  constructor
  · rw [emb.1,sim.1,adaptive_source_join]
  · rw [emb.2.2.1,sim.2.1]
    exact CommitmentSessions.Preparation.adaptive_emissions inputs scheduler horizon s

/-- Handler-cost accounting is attached to this actual communication source. -/
theorem priced_improvement (inputs : CommitmentSessions.SessionId → CommitmentSessions.Input)
    (scheduler : CommitmentSessions.Scheduler) (horizon : Nat) (s : SessionState) :
    PIR.Preparation.work (execute inputs scheduler horizon s .memo).events +
      PIR.Preparation.overhead (execute inputs scheduler horizon s .memo).events ≤
      PIR.Preparation.work (execute inputs scheduler horizon s .direct).events ↔
    PIR.Preparation.overhead (execute inputs scheduler horizon s .memo).events ≤
      PIR.Preparation.saved (execute inputs scheduler horizon s .memo).events :=
  PIR.Preparation.Emission.priced_improvement provider prices (adaptiveLower inputs scheduler horizon s)

end Zkc.Protocols.CommitmentSessions.Source
