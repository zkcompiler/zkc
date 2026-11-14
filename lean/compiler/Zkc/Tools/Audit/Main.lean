import Zkc.Tools.Audit
-- the controls are imported so that Lake builds them; the audit reads them from their files
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.Extern
import Zkc.Tools.Audit.Controls.ImplementedBy
import Zkc.Tools.Audit.Controls.Unchecked
import Zkc.Tools.Audit.Controls.UsesUnchecked
import Zkc.Tools.Audit.Controls.Import
import Zkc.Tools.Audit.Controls.ImportOutside
import Zkc.Tools.Audit.Controls.Unreached
import Zkc.Tools.Audit.Controls.Unreached.Apart

/-! `zkc-audit`: the audit of the core, the frontend and the tests of the core
(`Zkc.Tools.Audit`). -/

open Zkc.Tools.Audit

/-- The libraries of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  { name := "core", root := `Zkc.Core, imports := some coreImports, directory },
  { name := "frontend", root := `Zkc.Frontend, directory
    withoutReplay := some "it is the unproved part of the compiler, and no theorem of the project rests on it" },
  { name := "tests of the core", root := `Zkc.Tests.Core, kind := .tests, directory }]

def main : IO UInt32 := run libraries
