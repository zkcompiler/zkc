import Zkc.Protocols.CorrelatedSetup.Communication

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Tests.CorrelatedCommunication
open PIR Zkc.Protocols.CorrelatedSetup Zkc.Protocols.CorrelatedSetup.Communication Zkc.Protocols.CorrelatedSetup.Service


def setup : Setup Int := ⟨3,5,1,6,2⟩
def witness : Witness Int := ⟨1,1,by decide⟩
def publication : Triple Int := (6,4,5)
def out (edit : Edit) := generated edit setup witness publication 4 empty [9,10,11,12]

theorem edited_capture_changes_execution : (out .baseline).events ≠ (out .capture).events := by
  decide +kernel
theorem edited_bound_changes_consumption :
    (out .baseline).state.2 = [11,12] ∧ (out .extraRequest).state.2 = [12] := by
  decide +kernel
theorem edited_delivery_changes_view : (out .baseline).events ≠ (out .fullDelivery).events := by
  decide +kernel
theorem edited_future_input_refused :
    ¬({code .baseline with challenge := .var 8} : Zkc.Protocols.CorrelatedSetup.Source.Program).Good := by
  decide +kernel
theorem edited_private_guard_refused :
    ¬({code .baseline with stop := .var 6} : Zkc.Protocols.CorrelatedSetup.Source.Program).Good := by
  decide +kernel

def changedSetup : Setup Int := {setup with delta := 4}
def staleRun := (Zkc.Protocols.CorrelatedSetup.Execution.source ((code .baseline).denote changedSetup witness)
    publication 4 empty).run
  (cachedHandler changedSetup witness publication (buildCache setup witness publication).value)
  (empty,[9,10,11,12])

theorem stale_capture_cache_wrong : staleRun.events ≠
    (generated .baseline changedSetup witness publication 4 empty [9,10,11,12]).events := by
  decide +kernel



end Tests.CorrelatedCommunication
