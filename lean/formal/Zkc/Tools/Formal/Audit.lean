import Zkc.Tools.Audit
-- the controls are imported so that Lake builds them; the audit reads them from their files
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.Import

/-! `zkc-formal-audit`: the audit of the formal library, with the audit of the compiler's package
(`Zkc.Tools.Audit`). A module of `Zkc.Formal` imports only modules of the core and of the formal
library, besides Lean's prelude (`Init`). -/

open Zkc.Tools.Audit

/-- The library of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  { name := "formal", root := `Zkc.Formal, imports := some #[`Zkc.Core, `Init], directory }]

def main : IO UInt32 := run libraries
