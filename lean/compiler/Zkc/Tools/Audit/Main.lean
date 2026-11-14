import Zkc.Tools.Audit
-- the controls are imported so that Lake builds them; the audit reads them from their files
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.Import

/-! `zkc-audit`: the audit of the core and the frontend (`Zkc.Tools.Audit`). -/

open Zkc.Tools.Audit

/-- The libraries of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  { name := "core", root := `Zkc.Core, imports := some #[`Init, `Std, `Lean], directory },
  { name := "frontend", root := `Zkc.Frontend, imports := none, directory }]

def main : IO UInt32 := run libraries
