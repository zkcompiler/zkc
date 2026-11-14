import Zkc.Tests.Core.Check
import Zkc.Core.Serialize

/-! Commands for the kernel checks of the construction steps.

`raw_declaration name from file "<path>"` reads a declaration with the tool's reader and
adds it as the constant `name`.

`construction_check name from "<stem>"` states, for the fixture with the given stem,
that the kernel's evaluation of the Fiat–Shamir step and of the serialize step after it
gives the protocols that the compiled tool printed, and that both results elaborate. -/

set_option autoImplicit false

open Lean Elab Command Term Meta

namespace Zkc.Core

deriving instance ToExpr for Raw.SiteRow
deriving instance ToExpr for Raw.Suite
deriving instance ToExpr for Raw.Layout
deriving instance ToExpr for Raw.Declaration

syntax (name := rawDeclaration) "raw_declaration " ident " from " &"file " str : command

elab_rules : command
  | `(raw_declaration $name:ident from file $path:str) => do
      let source ← IO.FS.readFile (← liftCoreM (packagePath path.getString))
      let declaration ← match Raw.parseDeclaration source with
        | .ok declaration => pure declaration
        | .error message => throwError "refused declaration: {message}"
      liftCoreM <| addDecl (.defnDecl {
        name := (← getCurrNamespace) ++ name.getId, levelParams := [],
        type := mkConst ``Raw.Declaration, value := toExpr declaration,
        hints := .abbrev, safety := .safe })

/-- The protocols of a step's result, as raw syntax. -/
def steppedProtocols (typed : Typed)
    (stepped : Except StepRefusal
      (Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)) :
    Except StepRefusal (List Raw.Protocol) :=
  match stepped with
  | .ok stepped =>
      .ok (unelaborateProtocols typed.functions.length stepped.headers.length stepped.protocols [])
  | .error refusal => .error refusal

end Zkc.Core
