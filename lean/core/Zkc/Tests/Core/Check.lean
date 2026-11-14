import Lean
import Zkc.Tests.Core.Files
import Zkc.Core.Package
import Zkc.Core.Unelaborate

/-! Commands for the per-package kernel checks. This module imports Lean's elaborator;
the executable does not link it.

`raw_package name from file "<path>"` reads a package with the tool's reader and adds
its raw syntax as the constant `name`.

`reprinted_package name from file "<path>"` reads a package, prints it with the tool's
printer and reads the printed text again; the second reading is the constant `name`. A
`kernel_refl` that it equals the first reading checks the printed spellings.

`kernel_refl name : left equals right` adds the theorem `name : left = right` with the
proof `Eq.refl right`, checked by the kernel alone: the elaborator elaborates the two
sides and does not compare them. It reports the kernel's time.
-/

set_option autoImplicit false

open Lean Elab Command Term Meta

namespace Zkc.Core

deriving instance ToExpr for Use
deriving instance ToExpr for Ty
deriving instance ToExpr for RecordDeclaration
deriving instance ToExpr for VariantDeclaration
deriving instance ToExpr for Located
deriving instance ToExpr for Static
deriving instance ToExpr for CatalogueRow
deriving instance ToExpr for OperationKind
deriving instance ToExpr for OperationSignature
deriving instance ToExpr for Operation
deriving instance ToExpr for Reason
deriving instance ToExpr for PIR.Stop
deriving instance ToExpr for Raw.Literal
deriving instance ToExpr for Raw.Builtin
deriving instance ToExpr for Raw.LoopCount
deriving instance ToExpr for Raw.LocalStep, Raw.LocalRegion, Raw.LocalArms
deriving instance ToExpr for ChoiceTag
deriving instance ToExpr for Raw.RepeatCount
deriving instance ToExpr for Raw.ProtocolStep, Raw.ProtocolRegion, Raw.ProtocolArms
deriving instance ToExpr for Raw.Agreement
deriving instance ToExpr for Raw.Function
deriving instance ToExpr for Raw.Protocol
deriving instance ToExpr for Raw.Names
deriving instance ToExpr for Raw.Package

syntax (name := rawPackage) "raw_package " ident " from " &"file " str : command

elab_rules : command
  | `(raw_package $name:ident from file $path:str) => do
      let source ← IO.FS.readFile (← liftCoreM (packagePath path.getString))
      let package ← match Raw.parsePackage source with
        | .ok package => pure package
        | .error message => throwError "refused package: {message}"
      liftCoreM <| withOptions (fun options => maxRecDepth.set (Elab.async.set options false) 100000) <|
        addDecl (.defnDecl {
          name := (← getCurrNamespace) ++ name.getId, levelParams := [],
          type := mkConst ``Raw.Package, value := toExpr package,
          hints := .abbrev, safety := .safe })

syntax (name := reprintedPackage) "reprinted_package " ident " from " &"file " str : command

elab_rules : command
  | `(reprinted_package $name:ident from file $path:str) => do
      let source ← IO.FS.readFile (← liftCoreM (packagePath path.getString))
      let package ← match Raw.parsePackage source with
        | .ok package => pure package
        | .error message => throwError "refused package: {message}"
      let reprinted ← match Raw.parsePackage (Raw.printPackage package).render with
        | .ok package => pure package
        | .error message => throwError "refused printed package: {message}"
      liftCoreM <| withOptions (fun options => maxRecDepth.set (Elab.async.set options false) 100000) <|
        addDecl (.defnDecl {
          name := (← getCurrNamespace) ++ name.getId, levelParams := [],
          type := mkConst ``Raw.Package, value := toExpr reprinted,
          hints := .abbrev, safety := .safe })

syntax (name := kernelRefl) "kernel_refl " ident " : " term " equals " term : command

elab_rules : command
  | `(kernel_refl $name:ident : $left:term equals $right:term) => do
      let (type, left, right) ← liftTermElabM do
        let right ← elabTerm right none
        let type ← inferType right
        let left ← elabTermEnsuringType left type
        synthesizeSyntheticMVarsNoPostponing
        pure (← instantiateMVars type, ← instantiateMVars left, ← instantiateMVars right)
      let level ← liftTermElabM (getLevel type)
      let statement := mkApp3 (mkConst ``Eq [level]) type left right
      let proof := mkApp2 (mkConst ``Eq.refl [level]) type right
      let started ← IO.monoNanosNow
      liftCoreM <| withOptions (fun options => maxRecDepth.set (Elab.async.set options false) 100000) <|
        addDecl (.thmDecl {
          name := (← getCurrNamespace) ++ name.getId, levelParams := [], type := statement,
          value := proof })
      let finished ← IO.monoNanosNow
      logInfo m!"kernel_refl {name.getId}: {(finished - started) / 1000000} ms"

end Zkc.Core

namespace Zkc.Core

open Lean Elab Command Term Meta

/-- `normal_form name := term` adds `name` as the normal form of `term`, computed by the
elaborator's evaluator. The result is a proposal: the kernel checks only that it has the
type of `term`. A `kernel_refl` afterwards checks that it equals `term`. -/
syntax (name := normalForm) "normal_form " ident " := " term : command

elab_rules : command
  | `(normal_form $name:ident := $value:term) => do
      let started ← IO.monoNanosNow
      let (type, reduced) ← liftTermElabM do
        let value ← elabTerm value none
        synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        let type ← inferType value
        let reduced ← withOptions (fun options => maxRecDepth.set options 100000) <|
          withTransparency .all <| reduce value (skipProofs := true) (skipTypes := true)
        pure (type, reduced)
      let evaluated ← IO.monoNanosNow
      liftCoreM <| withOptions (fun options => maxRecDepth.set (Elab.async.set options false) 100000) <|
        addDecl (.defnDecl {
          name := (← getCurrNamespace) ++ name.getId, levelParams := [], type := type,
          value := reduced, hints := .abbrev, safety := .safe })
      let finished ← IO.monoNanosNow
      modifyEnv (addNoncomputable · ((← getCurrNamespace) ++ name.getId))
      logInfo m!"normal_form {name.getId}: evaluation {(evaluated - started) / 1000000} ms, kernel {(finished - evaluated) / 1000000} ms"

end Zkc.Core

/-! ## A proposer of typed literals

`typed_literal name := term` adds `name` as the literal form of a closed term of data:
constructor applications down to numerals, with every argument that is a type or a
function left as an application whose own arguments are literal, and with every proof
of an equation replaced by `Eq.refl` of its right side. The kernel's own evaluator
computes each weak head normal form; the command only walks the result. The literal is
a proposal: the kernel checks its type when the constant is added, and a `kernel_refl`
afterwards checks that it equals the term.

The walk shares equal subterms, so the literal of a region is a graph of linear size
although every node states its context. -/

namespace Zkc.Core.Literal

open Lean Meta

/-- Heads that stay as applications: structures of types and functions, whose weak
head normal form would expose their fields. -/
def neutralHeads : List Lean.Name :=
  [``Zkc.Core.LocalDialect, ``Zkc.Core.ProtocolDialect]

/-- Types whose closed terms are kept as they are written. -/
def leafTypes : List Lean.Name := [``String, ``Char]

abbrev LiteralM := StateRefT (Std.HashMap Expr Expr) MetaM

def kernelWhnf (e : Expr) : MetaM Expr := do
  match Lean.Kernel.whnf (← getEnv) {} e with
  | .ok value => pure value
  | .error _ => throwError "the kernel could not evaluate {e}"

mutual
  /-- An application with every argument in literal form, each by its declared type. -/
  partial def literalApp (head : Expr) (arguments : Array Expr) : LiteralM Expr := do
    let mut type ← inferType head
    let mut done : Array Expr := #[]
    for argument in arguments do
      type ← whnf type
      match type with
      | .forallE _ domain body _ =>
          let value ← literalArgument argument domain
          done := done.push value
          type := body.instantiate1 value
      | _ => throwError "unexpected application {head}"
    return mkAppN head done

  /-- An argument of a declared type: a proof, a type or function, or data. -/
  partial def literalArgument (argument type : Expr) : LiteralM Expr := do
    if ← isProp type then
      let type ← whnfR type
      match type.eq? with
      | some (carrier, _, right) =>
          let level ← getLevel carrier
          return mkApp2 (mkConst ``Eq.refl [level]) carrier right
      | none => return argument
    let shape ← whnf type
    if shape.isSort || shape.isForall then literalNeutral argument
    else literalData argument shape

  /-- A type or a function: its own arguments in literal form. -/
  partial def literalNeutral (e : Expr) : LiteralM Expr := do
    match e.getAppFn with
    | .const .. => if e.getAppNumArgs == 0 then pure e else literalApp e.getAppFn e.getAppArgs
    | _ => pure e

  /-- Data: the kernel's weak head normal form, then its fields. -/
  partial def literalData (e type : Expr) : LiteralM Expr := do
    if let some known := (← get)[e]? then return known
    let result ← do
      if let .const name _ := type.getAppFn then
        if leafTypes.contains name then pure e
        else if let .const head _ := e.getAppFn then
          if neutralHeads.contains head then literalApp e.getAppFn e.getAppArgs
          else literalValue e
        else literalValue e
      else literalValue e
    modify (·.insert e result)
    return result

  partial def literalValue (e : Expr) : LiteralM Expr := do
    let value ← kernelWhnf e
    match value.getAppFn with
    | .const name _ =>
        match (← getEnv).find? name with
        | some (.ctorInfo _) => literalApp value.getAppFn value.getAppArgs
        | _ => pure value
    | _ => pure value
end

end Zkc.Core.Literal

namespace Zkc.Core

open Lean Elab Command Term Meta

syntax (name := typedLiteral) "typed_literal " ident " := " term : command

elab_rules : command
  | `(typed_literal $name:ident := $value:term) => do
      let started ← IO.monoNanosNow
      let (type, literal) ← liftTermElabM do
        let value ← elabTerm value none
        synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        let type ← inferType value
        let literal ← (Literal.literalData value (← whnf type)).run' {}
        pure (type, literal)
      let evaluated ← IO.monoNanosNow
      liftCoreM <| withOptions (fun options => maxRecDepth.set (Elab.async.set options false) 100000) <|
        addDecl (.defnDecl {
          name := (← getCurrNamespace) ++ name.getId, levelParams := [], type := type,
          value := literal, hints := .abbrev, safety := .safe })
      let finished ← IO.monoNanosNow
      modifyEnv (addNoncomputable · ((← getCurrNamespace) ++ name.getId))
      logInfo m!"typed_literal {name.getId}: evaluation {(evaluated - started) / 1000000} ms, kernel {(finished - evaluated) / 1000000} ms"

end Zkc.Core
