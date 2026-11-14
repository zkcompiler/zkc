import Zkc.Tests.Frontend.Harness
import Zkc.Tools.Frontend.Generate

/-!
# The generated program of the measurements

It parses, and the printer keeps its tree.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend.Syntax

def generatedSuite : TestM Unit := do
  let text := Zkc.Tools.Frontend.Generate.program 50000
  match parseString "generated" text with
  | .error error => failure s!"the generated program is refused: {error.render}"
  | .ok parsed =>
    pass
    note s!"generated program: {(text.splitOn "\n").length - 1} lines, {parsed.tree.items.size} items"
    checkPrinter "generated" parsed

end Zkc.Tests.Frontend
