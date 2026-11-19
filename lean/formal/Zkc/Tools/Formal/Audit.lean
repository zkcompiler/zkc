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
  { name := "tests of the formal library", root := `Zkc.Tests.Formal, kind := .tests, directory },
  Zkc.Tools.Formal.chargeIssuer directory]

/-- The compiler's package, which holds the files of the controls: the package that this one
requires, at `../compiler`. -/
def main : IO UInt32 := run libraries (fun directory => directory / ".." / "compiler") Zkc.Tools.Formal.policy
