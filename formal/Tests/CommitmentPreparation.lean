import Zkc.Protocols.CommitmentSessions.Preparation
import Tests.CommitmentSessions

set_option autoImplicit false

namespace Tests.CommitmentPreparation
open Zkc.Modules.Preparation Zkc.Source.TablePreparation Zkc.Protocols.CommitmentSessions.Preparation

def summary (actions : List Zkc.Protocols.CommitmentSessions.Action) (mode : Mode) : List Nat :=
  let r := Zkc.Modules.Preparation.run Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode (lower Tests.CommitmentSessions.inputs actions Zkc.Protocols.CommitmentSessions.initial) Zkc.Modules.Preparation.empty
  [r.trace.length,r.work,r.saved,r.overhead]
-- [trace length, work, saved, overhead]. Memoizing the complete session
-- halves the work and accounts for what it saved; a session that cancels
-- before committing prepares nothing and so saves nothing.
#guard summary Tests.CommitmentSessions.complete .direct = [6, 24, 0, 0]
#guard summary Tests.CommitmentSessions.complete .memo = [6, 12, 12, 3]
#guard summary [⟨false,.cancel⟩,⟨false,.commit⟩] .memo = [2, 0, 0, 0]

theorem actual_honest_opens :
    (Zkc.Modules.Preparation.run Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices .memo (lower Tests.CommitmentSessions.inputs Tests.CommitmentSessions.complete Zkc.Protocols.CommitmentSessions.initial) Zkc.Modules.Preparation.empty).value.sessions false = .done ∧
    (Zkc.Modules.Preparation.run Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices .memo (lower Tests.CommitmentSessions.inputs Tests.CommitmentSessions.complete Zkc.Protocols.CommitmentSessions.initial) Zkc.Modules.Preparation.empty).value.sessions true = .done := by decide

theorem actual_wrong_open :
    (Zkc.Modules.Preparation.run Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices .memo (lower Tests.CommitmentSessions.inputs (Tests.CommitmentSessions.both ++ [⟨true,.open 1 2⟩]) Zkc.Protocols.CommitmentSessions.initial) Zkc.Modules.Preparation.empty).value.sessions true = .failed := by decide

theorem actual_cancel_is_lazy :
    (Zkc.Modules.Preparation.run Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices .memo (lower Tests.CommitmentSessions.inputs [⟨false,.cancel⟩,⟨false,.commit⟩] Zkc.Protocols.CommitmentSessions.initial) Zkc.Modules.Preparation.empty).work = 0 := by decide

/-- Even total pure preparation does not preserve this cost-adaptive observer. -/
def scheduled (mode : Mode) : List Zkc.Protocols.CommitmentSessions.Event :=
  let first := Zkc.Modules.Preparation.run Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode (lower Tests.CommitmentSessions.inputs Tests.CommitmentSessions.both Zkc.Protocols.CommitmentSessions.initial) Zkc.Modules.Preparation.empty
  let a : Zkc.Protocols.CommitmentSessions.Action := if first.work = 24 then ⟨false,.cancel⟩ else ⟨false,.reveal⟩
  (Zkc.Modules.Preparation.run Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode (lower Tests.CommitmentSessions.inputs [a] first.value) first.cache).value.trace

theorem cost_adaptive_separator : scheduled .direct ≠ scheduled .memo := by decide

end Tests.CommitmentPreparation
