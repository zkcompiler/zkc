import Zkc.Tools.Audit
-- the controls are imported so that Lake builds them; the audit reads them from their files
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.Extern
import Zkc.Tools.Audit.Controls.ImplementedBy
import Zkc.Tools.Audit.Controls.Unchecked
import Zkc.Tools.Audit.Controls.Import
import Zkc.Tools.Audit.Controls.ImportOutside
import Zkc.Tools.Audit.Controls.Unreached
import Zkc.Tools.Audit.Controls.Unreached.Apart

/-! `zkc-formal-audit`: the audit of the formal library and of its tests, with the audit of the
compiler's package (`Zkc.Tools.Audit`). A module of `Zkc.Formal` imports only modules of the core
and of the formal library, besides Lean's prelude (`Init`). -/

open Zkc.Tools.Audit

/-- The libraries of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  { name := "formal", root := `Zkc.Formal, imports := some #[`Zkc.Core, `Init], directory },
  { name := "tests of the formal library", root := `Zkc.Tests.Formal, kind := .tests, directory }]

/-- The compiler's package, which holds the files of the controls: the package that this one
requires, at `../compiler`. -/
def main : IO UInt32 := run libraries fun directory => directory / ".." / "compiler"
