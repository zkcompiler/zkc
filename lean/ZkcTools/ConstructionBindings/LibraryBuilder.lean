module

public import Zkc.Construction.ConnectionLibrary
public import ZkcTools.ConstructionBindings.LibraryPlan
public meta import ZkcTools.ConstructionBindings.LibraryPlan
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Closure
public meta import Lean.Compiler.NoncomputableAttr

public meta section

/-! Propose a finite source library from the admitted declaration graph.
Normalized source forms are frozen behind checked constants, shared when their
complete type and value agree. Each declaration-specific template retains its
exact admitted source, role and signature. This shares source normalization,
not target alignment. The selected library still requires the independent finite root
connection before it supplies execution correspondence. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.LibraryBuilder
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionLibrary

initialize normalizedBodies : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.foldl (· ++ ·) #[]
  }

private def sharedSourceBody (form : Expr) : TermElabM Expr := do
  let type ← inferType form
  let (type, form) := _root_.ShareCommon.shareCommon' (type, form)
  for name in normalizedBodies.getState (← getEnv) do
    unless (← getEnv).contains name do continue
    let candidate := mkConst name
    if (← withTransparency .all <| isDefEq (← inferType candidate) type) &&
        (← withTransparency .all <| isDefEq candidate form) then return candidate
  -- Respect the enclosing public/private context. A forced private name cannot
  -- appear in a later exported template or its type.
  let name ← mkAuxDeclName `normalizedConnectionBody
  withOptions (Elab.async.set · false) <|
    addDecl (.defnDecl {name, levelParams := [], type, value := form, hints := .abbrev, safety := .safe})
  modifyEnv fun environment => addNoncomputable (normalizedBodies.addEntry environment name) name
  return mkConst name

/-- Freeze an explicit source-template record so selecting its finite key does
not re-run its source normalizer. The auxiliary definition is kernel checked. -/
private def freezeSourceTemplate (expression : Expr) : TermElabM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let type ← inferType expression
  let value ← withTransparency .all <| whnf expression
  unless value.isAppOf ``SourceTemplate.mk do
    throwError "source-library-template-refused"
  let parts := value.getAppArgs
  let form ← withTransparency .all <| reduce parts[parts.size - 3]! true true true
  let body ← sharedSourceBody form
  let value := mkAppN value.getAppFn (parts.set! (parts.size - 3) body)
  let (type, value) := _root_.ShareCommon.shareCommon' (type, value)
  let name ← mkAuxDeclName `sourceConnectionBody
  withOptions (Elab.async.set · false) <|
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
  modifyEnv (addNoncomputable · name)
  return mkConst name

private def template (payload keys : Expr) (selection : LibraryPlan.Selection) : TacticM Expr := do
  let source ← Term.exprToSyntax payload
  let earlier ← Term.exprToSyntax keys
  let index := Syntax.mkNumLit (toString selection.declaration)
  let role := Syntax.mkNumLit (toString selection.role)
  let proposed ← Term.elabTerm (← `(term|
    (SourceTemplate.build $source $earlier ⟨$index, by decide +kernel⟩ $role
      (rolePattern $role ($source).protocols[$index].inputs
        ($source).protocols[$index].inputScopes)).toOption.get (by decide +kernel))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposed ← instantiateMVars proposed
  if proposed.hasMVar then throwError "connection-library-template-unresolved"
  freezeSourceTemplate proposed

private def listNodes (value : Expr) : MetaM (Array Expr) := do
  let mut cursor := value
  let mut result := #[]
  while true do
    cursor ← withTransparency .all <| whnf cursor
    if cursor.isAppOf ``List.nil then return result
    unless cursor.isAppOf ``List.cons do throwError "connection-library-discovery-not-finite"
    let arguments := cursor.getAppArgs
    result := result.push arguments[1]!
    cursor := arguments[2]!
  return result

/-- Return the exact keys and checked library. Discovery is untrusted and may
refuse. The kernel checks every installed template without a caller-supplied
process equation, slot map, or protocol-specific method. -/
def propose (payload roles : Expr) : TacticM (Expr × Expr) := do
  let plan ← mkAppM ``LibraryPlan.forPayload #[payload, roles]
  let result ← withTransparency .all <| whnf plan
  unless result.isAppOf ``Except.ok do throwError "connection-library-discovery-refused: {result}"
  let selections ← listNodes result.getAppArgs.back!
  let mut keys ← mkListLit (mkConst ``CalleeKey) []
  let mut library ← mkAppOptM ``Library.empty #[some payload]
  for selection in selections do
    let some declaration ← getNatValue? (← withTransparency .all <| whnf (← mkAppM ``LibraryPlan.Selection.declaration #[selection]))
      | throwError "connection-library-declaration-not-static"
    let some role ← getNatValue? (← withTransparency .all <| whnf (← mkAppM ``LibraryPlan.Selection.role #[selection]))
      | throwError "connection-library-role-not-static"
    let selected ← template payload keys ⟨declaration, role⟩
    library ← mkAppM ``Library.extend #[library, selected]
    keys ← mkAppM ``List.cons #[← mkAppM ``SourceTemplate.key #[selected], keys]
  return (keys, library)

/-- Assemble one checked dependency closure for the requested source roles.
With no explicit role selection the entry roster supplies all roles, so the
producer and validator refer to the same source library. -/
private def deriveLibrary (rolesSyntax : Option Syntax) : TacticM Unit := withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    let goal ← getMainGoal
    let expected ← whnf (← goal.getType)
    unless expected.isAppOf ``Bundle do throwError "expected a source library bundle"
    let payload := expected.getAppArgs[0]!
    let roles ← match rolesSyntax with
      | some selectedRoles => Term.elabTerm selectedRoles (some (← mkAppM ``List #[mkConst ``Nat]))
      | none => do
        let entry ← mkAppM ``UnitPayload.entry #[payload]
        let signature ← mkAppM ``CheckedProtocol.signature #[entry]
        let roster ← mkAppM ``ProtocolSignature.roles #[signature]
        mkAppM ``List.range #[← mkAppM ``List.length #[roster]]
    let (keys, library) ← propose payload roles
    goal.assign (← mkAppM ``Bundle.mk #[keys, library])
    replaceMainGoal []

elab "derive_connection_library" : tactic => deriveLibrary none

elab "derive_connection_library" &"roles" roles:term : tactic =>
  deriveLibrary (some roles)

end ZkcTools.ConstructionBindings.LibraryBuilder
