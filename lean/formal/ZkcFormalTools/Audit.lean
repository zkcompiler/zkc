import ZkcFormalTools.Policy
import ZkcFormalTools.Controls.FrontendImport
import ZkcFormalTools.Controls.ValueReadsFees
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

/-- The modules of the judgment by fees. -/
def feeModules : Array Lean.Name := #[`ZkcFormal.ChargedJudgment, `ZkcFormal.ChargedProbability,
  `ZkcFormal.ChargedReturn, `ZkcFormal.Written.Contract, `ZkcFormal.Written.Fees,
  `ZkcFormal.Written.FeeRules]

/-- What the formal library keeps apart. The value of a process and its reading are what a
statement of soundness means and what every method of proof reads: they import nothing of the
judgment by fees. What a contract of a call says is a statement that a library's protocol
publishes: it imports neither the rules for the generator of proofs nor a theorem from the
judgment to a probability. -/
def formalApart : Array Apart := #[
  { above := #[`ZkcFormal.Value, `ZkcFormal.Written.Value, `ZkcFormal.Reading], below := feeModules
    because := "the value of a process and its reading do not read the judgment by fees" },
  { above := #[`ZkcFormal.Written.Contract]
    below := #[`ZkcFormal.Written.FeeRules, `ZkcFormal.ChargedReturn, `ZkcFormal.Value]
    because := "what a contract of a call says reads no rule of a generator and no theorem to a probability" }]

/-- The dependencies available to the formal semantics, for ordinary and meta imports. -/
def formalLibrary (directory : System.FilePath) : Library :=
  { name := "formal", root := `ZkcFormal, imports := some #[`Init, `Std, `Lean, `Zkc.Core,
      `Zkc.Vocabulary, `Zkc.Subject, `Mathlib, `VCVio, `PolyFun], directory, apart := formalApart }

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

/-- Exercise the rule that keeps the value apart from the judgment by fees, on a module that is
listed with the value and imports the judgment. -/
def valueReadsFeesControl : Control :=
  let root := `ZkcFormalTools.Controls.ValueReadsFees
  { description := "a module of the value that imports the judgment by fees"
    library := { name := "kept apart", root, withoutReplay := anotherRule
                 apart := #[{ above := #[root], below := feeModules
                              because := "the value of a process does not read the judgment by fees" }] }
    rule := .layers
    isRefusal := fun finding => finding.subject == root &&
      (finding.line.splitOn "ZkcFormal.ChargedJudgment").length > 1 }

/-- Run the formal audit with the shared compiler controls and the formal import control. -/
def main : IO UInt32 := do
  let directory ← packageDirectory
  let configured := libraries directory
  checkIssuers configured
  run (fun _ => configured) (fun directory => directory / ".." / "compiler") ZkcFormalTools.policy
    #[frontendImportControl directory, valueReadsFeesControl]
