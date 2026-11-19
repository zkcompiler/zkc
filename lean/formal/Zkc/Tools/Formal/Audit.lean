import Zkc.Tools.Formal.Policy
-- the controls are imported so that Lake builds them; the audit reads them from their files
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.Extern
import Zkc.Tools.Audit.Controls.ImplementedBy
import Zkc.Tools.Audit.Controls.ConstructorIndex
import Zkc.Tools.Audit.Controls.Generated
import Zkc.Tools.Audit.Controls.Recognition
import Zkc.Tools.Audit.Controls.Unchecked
import Zkc.Tools.Audit.Controls.UsesUnchecked
import Zkc.Tools.Audit.Controls.Import
import Zkc.Tools.Audit.Controls.ImportOutside
import Zkc.Tools.Audit.Controls.Unreached
import Zkc.Tools.Audit.Controls.Unreached.Apart
import Zkc.Tools.Audit.Controls.Layers

open Zkc.Tools.Audit

/-- The libraries of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  { name := "formal", root := `Zkc.Formal, imports := some #[`Init, `Std, `Lean, `Zkc.Core,
      `Zkc.Frontend.Emit.Bindings, `Zkc.Frontend.Written.LeanTerms, `Zkc.Frontend.Written.ChargeData, `Mathlib, `VCVio], directory },
  { name := "tests of the formal library", root := `Zkc.Tests.Formal, kind := .tests, directory }] ++
  Zkc.Tools.Formal.publicIssuers directory

/-- Verify the configuration actually handed to the package audit. Source clients
are required even when the local build cache contains all of their dependencies. -/
def checkIssuers (configured : Array Library) : IO Unit := do
  for root in [`Zkc.Tools.Formal.DrawCharge] do
    unless configured.any (fun lib => lib.root == root && lib.withoutReplay.isNone) do
      throw (IO.userError s!"missing public kernel replay root {root}")

/-- The package's controls are in its sibling compiler package. -/
def main : IO UInt32 := do
  let configured := libraries (← packageDirectory)
  checkIssuers configured
  run (fun _ => configured) (fun directory => directory / ".." / "compiler") Zkc.Tools.Formal.policy
