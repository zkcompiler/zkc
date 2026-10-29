import Zkc.Source.KernelRfl
import Zkc.Source.Structured.Import
import Zkc.Source.Structured.ComponentRoutes
import Zkc.Source.Structured.NormalForm.Presentation

/-! Disjoint assembly selects the role's existing value. These are independent
formal controls, not a claim that the native projector is proved in Lean. -/
set_option autoImplicit false
set_option smartUnfolding false
open Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredAssembly

private def original (roles : List String) (operands : List Nat)
    (outputRoles : List String := ["P", "V"]) : Snapshot :=
  let function : Function := ⟨"main", .protocol, .publicDef,
    [.boolean, .boolean], [.boolean], some ⟨["P", "V"], [["P"], ["V"]], [outputRoles]⟩,
    [], some (.protocol ⟨"main", []⟩),
    .block [.instruction (.assemble roles) operands [.boolean] [] ""] (.ret [0])⟩
  ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000", "main",
    [], [], [], [.function function], [⟨"main", []⟩], blsRows, {}⟩

-- Initial ports retain declaration order. Results are subsequently prepended
-- to this context. Crossing ports with the role list is not a renaming.
example : (check (original ["P", "V"] [0, 1])).isOk = true := by decide +kernel
example : (check (original ["P", "V"] [1, 0])).isOk = false := by decide +kernel
example : (check (original ["P", "P"] [1, 1])).isOk = false := by decide +kernel
example : (check (original ["P", "unknown"] [1, 0])).isOk = false := by decide +kernel
example : (check (original [] [])).isOk = false := by decide +kernel
example : (check (original ["P", "V"] [1])).isOk = false := by decide +kernel
example : (check (original ["P"] [0])).isOk = false := by decide +kernel
example : (check (original ["P"] [0] ["P"])).isOk = true := by decide +kernel

private def assembledRoutes : Except String (List (List (String × SeamRoute × Option String))) := do
  let snapshot := original ["P", "V"] [0, 1]
  let some owner := snapshot.protocolFunctions.head? | throw "missing-owner"
  let left : ComponentRoutes.Flow :=
    { route := .input 0 "P", effect := some "left-effect" }
  let right : ComponentRoutes.Flow := { route := .input 1 "V" }
  let environment : ComponentRoutes.Environment := [[("P", left)], [("V", right)]]
  let (returned, _) ← (ComponentRoutes.block snapshot owner 64 owner.body owner.inputs
    environment [] [] []).run {}
  return returned.map fun family => family.map fun (role, flow) => (role, flow.route, flow.effect)

example : assembledRoutes = .ok [[("P", .input 0 "P", some "left-effect"),
    ("V", .input 1 "V", none)]] := by decide +kernel

private noncomputable def body : Region protocolDialect [.boolean, .boolean] [.boolean] :=
  .letOp (.assemble .boolean [0, 1]) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

private def pattern : NormalForm.InputPattern [.boolean, .boolean] :=
  .cons .present (.cons .absent .nil)
private noncomputable def selected : NormalForm.Form [] [] pattern.scope [.boolean] :=
  .done (.cons (.present (.var .here)) .nil)
private noncomputable def missing : NormalForm.Form [] [] pattern.scope [.boolean] :=
  .done (.cons .absent .nil)
example : NormalForm.normalize {} body 0 2 pattern = .ok selected := by kernel_rfl
example : NormalForm.normalize {} body 1 2 pattern = .ok missing := by kernel_rfl
example : NormalForm.normalize {} body 2 3 pattern = .ok missing := by kernel_rfl
example : NormalForm.normalize {} body 0 1 pattern = .error "role-outside-roster" := by kernel_rfl

private def components : Values (fun _ : Ty => Option Bool) [.boolean, .boolean] :=
  .cons (some true) (.cons (some false) .nil)
example : assembleComponent (fun role => role == 0) none [0, 1] components = some true := rfl
example : assembleComponent (fun role => role == 1) none [0, 1] components = some false := rfl
example : assembleComponent (fun role => role == 2) none [0, 1] components = none := rfl

-- Optional components are selected pointwise without forcing their presence.
private def optionalPattern : NormalForm.InputPattern [.boolean, .boolean] :=
  .cons .optional (.cons .optional .nil)
example : NormalForm.normalize {} body 0 2 optionalPattern =
    .ok (.done (.cons (.input .here) .nil)) := by kernel_rfl
example : NormalForm.normalize {} body 1 2 optionalPattern =
    .ok (.done (.cons (.input (.there .here)) .nil)) := by kernel_rfl

-- The Domain operation is silent and preserves the selected component exactly,
-- including absence. No equality of the two role values is a premise.
example (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (protocols : ProtocolTable model.Value I) (context : ProtocolContext)
    (iterations : IterationObservations I) (self : Nat)
    (left right : Component model.Value .boolean) :
    protocolOperationWithOn model observations actions tables self (.assemble .boolean [0, 1])
      (.cons left (.cons right .nil)) .nil protocols context iterations =
      .done (.cons (if context.roles 0 == self then left else
        if context.roles 1 == self then right else none) .nil) := rfl

end Tests.StructuredAssembly
