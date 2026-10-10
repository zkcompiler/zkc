import Zkc.Protocols.CommitmentSessions.Source
import Tests.CommitmentSessions

set_option autoImplicit false

namespace Tests.CommitmentSource
open PIR Zkc.Protocols.CommitmentSessions.Source

def afterCancel : Zkc.Protocols.CommitmentSessions.Scheduler := fun trace =>
  match trace.length with
  | 0 => some ⟨false,.cancel⟩
  | 1 => some ⟨false,.commit⟩
  | 2 => some ⟨true,.commit⟩
  | _ => none

theorem session_cancel_does_not_stop_scheduler :
    observeEvents PIR.Preparation.view (execute Tests.CommitmentSessions.inputs afterCancel 3 Zkc.Protocols.CommitmentSessions.initial .memo).events =
      [(false,.cancel),(false,.invalid),(true,.commitment 4)] := by
  decide +kernel

end Tests.CommitmentSource
