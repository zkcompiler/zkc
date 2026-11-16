import Zkc.Tools.Audit
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

/-! `zkc-audit`: the audit of the core, the vocabulary and their tests (`Zkc.Tools.Audit`). -/

open Zkc.Tools.Audit

/-- The libraries of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  { name := "core", root := `Zkc.Core, imports := some coreImports, directory },
  { name := "vocabulary", root := `Zkc.Vocabulary, imports := some vocabularyImports, directory },
  { name := "tests of the core", root := `Zkc.Tests.Core, kind := .tests, directory },
  { name := "tests of the vocabulary", root := `Zkc.Tests.Vocabulary, kind := .tests,
    directory }]

def main : IO UInt32 := run libraries
