import ZkcExamples.Structured.Generated.Scalar.SumcheckSourceLibrary
import Tests.StructuredNormalFormComponents

/-! Typed source association and complete-frame controls for scalar presentations.
The guarded failures must reach the kernel; admission, resource or parser errors
cannot stand in for rejection of a changed meaning. -/
set_option autoImplicit false
namespace Tests.ScalarSourcePresentations
open Zkc.Source Zkc.Source.Structured NormalForm ZkcExamples.Structured
open Tests.StructuredNormalFormComponents

example : Generated.Scalar.SumcheckSourceLibrary.pendingBody =
    SumcheckPendingBodies.pendingBody :=
  Generated.Scalar.SumcheckSourceLibrary.pending_pattern

example : Generated.Scalar.SumcheckSource.Reduce.roundBody =
    SumcheckVerifierBodies.roundBody :=
  Generated.Scalar.SumcheckSourceLibrary.round_body

-- Keeping the helper's type does not permit changing its nominal identity.
/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : Generated.Scalar.SumcheckSourceLibrary.pendingDefinition.helper =
    {SumcheckPendingBodies.pendingHelper with name := "different"} := by kernel_rfl

-- Keeping its complete helper key does not permit changing the stored body.
/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : Generated.Scalar.SumcheckSourceLibrary.pendingDefinition.body =
    (.stop .abort) := by kernel_rfl

-- A callback with the same input and result sorts must still match the body.
/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : Generated.Scalar.SumcheckSource.Reduce.roundBody =
    (.stop .reject) := by kernel_rfl

def duplicatedOperand : Region protocolDialect [.boolean, .boolean] [.boolean] :=
  .letOp (.calculate (.invoke conjunction.helper) rfl)
    (.cons .here (.cons .here .nil)) .nil (.ret (.cons .here .nil))

-- Same-sort operands retain their positions, including duplicate reads.
/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : normalize {} duplicatedOperand 0 1 optionalPair = .ok mathForm := by kernel_rfl

def pairPattern : InputPattern [.index, .index] := .cons .present (.cons .present .nil)
def pairBody : Region protocolDialect [.index, .index] [.index, .index] :=
  .ret (.cons .here (.cons (.there .here) .nil))
def pairForm : Form [] [] pairPattern.scope [.index, .index] :=
  .done (.cons (.present (.var .here)) (.cons (.present (.var (.there .here))) .nil))
def swappedReturns : Form [] [] pairPattern.scope [.index, .index] :=
  .done (.cons (.present (.var (.there .here))) (.cons (.present (.var .here)) .nil))

example : normalize {} pairBody 0 1 pairPattern = .ok pairForm := by kernel_rfl

/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : normalize {} pairBody 0 1 pairPattern = .ok swappedReturns := by kernel_rfl

-- A body that requires an unprovided local-helper law is refused explicitly.
example : normalize {} SumcheckVerifierBodies.roundBody 0 2
    SumcheckRoundNormalForms.proverPattern = .error "no-law" := by kernel_rfl

-- Generic component controls also check arbitrary guards, missing operands,
-- effectful helper replies and the stop before any continuation can execute.
end Tests.ScalarSourcePresentations
