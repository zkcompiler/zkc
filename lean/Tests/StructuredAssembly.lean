import Zkc.Source.KernelRfl
import Zkc.Source.Structured.Import
import Zkc.Source.Structured.NormalForm.Presentation
import Zkc.Construction.Projection

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

-- Assembly adds no participant instruction or physical reference. The reader
-- retains the exact selected component, including the source's absence mask.
example (program : Program) (context : Zkc.Construction.Context) :
    Zkc.Construction.walkOperation program context {} 20
      (.assemble .boolean [context.validator]) [.held 17] [] =
        .ok ([], [.held 17], 20) := by
  simp [Zkc.Construction.walkOperation]
example (program : Program) (context : Zkc.Construction.Context) :
    Zkc.Construction.walkOperation program context {} 20
      (.assemble .boolean [context.validator]) [.absent] [] =
        .ok ([], [.absent], 20) := by
  simp [Zkc.Construction.walkOperation]
example (program : Program) (context : Zkc.Construction.Context) :
    Zkc.Construction.walkOperation program context {} 20
      (.assemble .boolean [context.validator]) [.held 17, .held 18] [] =
        .error "projection-assembly" := rfl

end Tests.StructuredAssembly
