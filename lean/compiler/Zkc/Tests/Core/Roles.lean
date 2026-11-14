import Zkc.Tests.Core.Check
import Zkc.Core.Pipeline

/-! Reading the role programs that the tool printed, for the per-package checks.

`raw_roles name from file "<path>"` reads role programs with the tool's reader and adds
their raw syntax as the constant `name`. -/

set_option autoImplicit false

open Lean Elab Command Term Meta

namespace Zkc.Core

deriving instance ToExpr for Raw.RoleCount
deriving instance ToExpr for Raw.RoleStep, Raw.RoleRegion, Raw.RoleArms
deriving instance ToExpr for Raw.RoleProgram

syntax (name := rawRoles) "raw_roles " ident " from " &"file " str : command

elab_rules : command
  | `(raw_roles $name:ident from file $path:str) => do
      let source ← IO.FS.readFile (← liftCoreM (packagePath path.getString))
      let programs ← match Raw.parseRolePrograms source with
        | .ok programs => pure programs
        | .error message => throwError "refused role programs: {message}"
      liftCoreM <| withOptions (fun options => maxRecDepth.set (Elab.async.set options false) 100000) <|
        addDecl (.defnDecl {
          name := (← getCurrNamespace) ++ name.getId, levelParams := [],
          type := mkApp (mkConst ``List [Level.zero]) (mkConst ``Raw.RoleProgram),
          value := toExpr programs, hints := .abbrev, safety := .safe })

/-- The expanded entry of a package as the protocols of a package with one protocol. -/
def Typed.expandedProtocols (typed : Typed) : Except PipelineRefusal (List Raw.Protocol) :=
  match typed.expandedProtocol with
  | .ok protocol => .ok [protocol]
  | .error refusal => .error refusal

end Zkc.Core
