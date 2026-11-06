module

public import Zkc.Source.Structured.ServiceOperations
public import Zkc.Source.Structured.DomainModels

@[expose] public section

/-! Checked service replies in the existing participant effect interface.
Untrusted source services can stop or return any carrier value; only values
within the requested finite range and exact block length continue. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

def ServiceOp.validInputs {carriers : Carriers} :
    (operation : ServiceOp) → Values carriers.Value operation.arguments → Bool
  | .draw _, _ => true
  | .sampleIndex _, .cons _ (.cons bound .nil) => 0 < bound && bound < indexLimit
  | .sampleIndices _, .cons _ (.cons bound (.cons count .nil)) =>
      0 < bound && bound < indexLimit && 0 < count && count < indexLimit

def ServiceOp.validReply {carriers : Carriers} :
    (operation : ServiceOp) → Values carriers.Value operation.arguments →
      carriers.Value operation.result → Bool
  | .draw _, _, _ => true
  | .sampleIndex _, .cons _ (.cons bound .nil), value => (value : Nat) < bound
  | .sampleIndices _, .cons _ (.cons bound (.cons count .nil)), values =>
      values.length == count && values.all (· < bound)

/-- The adversarial source interface is total on carrier values. A reply must
pass this check before the surrounding source continuation is entered. -/
abbrev ServiceOp.checkedReply {carriers : Carriers} (operation : ServiceOp)
    (args : Values carriers.Value operation.arguments) (reply : carriers.Value operation.result) :
    PIR.Process (Participant.interface Nat Ty services carriers.Value) (carriers.Value operation.result) :=
  if operation.validReply args reply then .done reply else .halt .refused

def serviceAction {carriers : Carriers} : PIR.OperationInterpretation
    (Participant.interface Nat Ty services carriers.Value)
    (Participant.interface Nat Ty services carriers.Value)
  | .query site operation args =>
      if operation.validInputs args then
        .call (.query site operation args) fun reply =>
          if operation.validReply args reply then .done reply else .halt .refused
      else .halt .refused
  | operation => .call operation .done

theorem ServiceOp.checkedReply_refused {carriers : Carriers} (operation : ServiceOp)
    (args : Values carriers.Value operation.arguments) (reply : carriers.Value operation.result)
    (invalid : operation.validReply args reply = false) :
    operation.checkedReply args reply = .halt .refused := by
  simp [checkedReply, invalid]

theorem ServiceOp.checkedReply_returned {carriers : Carriers} (operation : ServiceOp)
    (args : Values carriers.Value operation.arguments) (reply : carriers.Value operation.result)
    (valid : operation.validReply args reply = true) :
    operation.checkedReply args reply = .done reply := by
  simp [checkedReply, valid]

theorem serviceAction_invalid {carriers : Carriers} (site : String) (operation : ServiceOp)
    (args : Values carriers.Value operation.arguments) (invalid : operation.validInputs args = false) :
    serviceAction (.query site operation args) = .halt .refused := by
  simp [serviceAction, invalid]

/-- The field operation is exactly the original unchecked field reply action.
Its typed signature has no bound/count formation or range check. -/
theorem serviceAction_draw {carriers : Carriers} (site field : String) (handle : Nat) :
    serviceAction (carriers := carriers) (.query site (.draw field) (.cons handle .nil)) =
      .call (.query site (.draw field) (.cons handle .nil)) .done := rfl

end Zkc.Source.Structured
