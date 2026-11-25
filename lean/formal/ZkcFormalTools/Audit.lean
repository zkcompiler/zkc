import ZkcFormalTools.Policy
import ZkcFormalTools.Controls.FrontendImport
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

/-- The dependencies available to the formal semantics, for ordinary and meta imports. -/
def formalLibrary (directory : System.FilePath) : Library :=
  { name := "formal", root := `ZkcFormal, imports := some #[`Init, `Std, `Lean, `Zkc.Core,
      `Zkc.Vocabulary, `Zkc.Subject, `Mathlib, `VCVio], directory }

/-- The libraries of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  formalLibrary directory,
  { name := "tests of the formal library", root := `ZkcFormalTests, kind := .tests, directory }] ++
  ZkcFormalTools.publicIssuers directory

/-- Verify the configuration actually handed to the package audit. Source clients
are required even when the local build cache contains all of their dependencies. -/
def checkIssuers (configured : Array Library) : IO Unit := do
  for root in [`ZkcFormalTools.DrawCharge] do
    unless configured.any (fun lib => lib.root == root && lib.withoutReplay.isNone) do
      throw (IO.userError s!"missing public kernel replay root {root}")

/-- Exercise the formal library's import policy on a module with a frontend meta import. -/
def frontendImportControl (directory : System.FilePath) : Control :=
  let root := `ZkcFormalTools.Controls.FrontendImport
  { description := "a frontend meta import in the formal library"
    library := { formalLibrary directory with root, directory := none, withoutReplay := anotherRule }
    rule := .importOutside
    isRefusal := fun finding => finding.subject == root }

/-- Run the formal audit with the shared compiler controls and the formal import control. -/
def main : IO UInt32 := do
  let directory ← packageDirectory
  let configured := libraries directory
  checkIssuers configured
  run (fun _ => configured) (fun directory => directory / ".." / "compiler") ZkcFormalTools.policy
    #[frontendImportControl directory]
