module

public import Zkc.IR.Construction.ConnectionLibrary
public import Zkc.Program.Source.KernelRfl
public import Zkc.Tools.IR.ConstructionBindings.LibraryPlan
public meta import Zkc.Tools.IR.ConstructionBindings.LibraryPlan
public meta import Lean.Elab.Tactic
public meta import Zkc.Tools.IR.ConstructionBindings.Normalization
public meta import Zkc.Tools.IR.ConstructionBindings.Syntax
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

private def phase (message : String) : TacticM Unit := do
  if !(← getOptions).getBool `zkc.connection.trace false then return
  let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
  unless destination.isEmpty do
    IO.FS.withFile destination .append fun handle => handle.putStrLn s!"library {message}"

initialize normalizedBodies : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    -- Library discovery can run inside a theorem task. Only checked names
    -- already available in that task may accelerate its proof search.
    asyncMode := .local
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

/-- Freeze the explicit record after its literal and every finite obligation
have been checked. Reading a key must never rerun the source normalizer. -/
private def freezeSourceTemplate (expression : Expr) : TermElabM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar then throwError "connection-library-template-unresolved"
  let type ← inferType expression
  let (type, value) := _root_.ShareCommon.shareCommon' (type, expression)
  let name ← mkAuxDeclName `sourceConnectionBody
  withOptions (Elab.async.set · false) <|
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
  modifyEnv (addNoncomputable · name)
  return mkConst name

private def template (cache : Syntax.Cache) (payload keys : Expr) (selection : LibraryPlan.Selection) : TacticM Expr := do
  let source ← Term.exprToSyntax payload
  let earlier ← Term.exprToSyntax keys
  let index := Syntax.mkNumLit (toString selection.declaration)
  let role := Syntax.mkNumLit (toString selection.role)
  let pattern ← Term.elabTerm (← `(term|
    InputVisibility.rolePattern $role ($source).protocols[$index].inputs
      ($source).protocols[$index].inputScopes)) none
  let pattern ← withTransparency .all <| Syntax.normalize cache pattern
  let patternSyntax ← Term.exprToSyntax pattern
  let computation ← Term.elabTerm (← `(term|
    NormalForm.normalize
      { strict := true, names := true, kept := ($source).definitions.map CheckedDefinition.helper, callees := $earlier }
      ($source).protocols[$index].body $role ($source).protocols[$index].roles.length $patternSyntax)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let literal ← unsafe Normalization.propose cache computation
  let form ← withTransparency .all <| Syntax.normalize cache literal
  let body ← sharedSourceBody form
  let bodySyntax ← Term.exprToSyntax body
  let proposed ← Term.elabTerm (← `(term|
    (show SourceTemplate $source $earlier from {
      declaration := ⟨$index, by decide +kernel⟩
      role := $role
      roleValid := by decide +kernel
      pattern := $patternSyntax
      pins := []
      visible := by decide +kernel
      inputScopes := by decide +kernel
      outputScopes := by decide +kernel
      form := $bodySyntax
      normalized := by kernel_rfl
      matched := by kernel_rfl }))) none
  freezeSourceTemplate proposed

private def listNodes (value : Expr) : MetaM (Array Expr) := do
  let mut cursor := value
  let mut result := #[]
  while true do
    cursor ← Syntax.head cursor
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
  phase "plan start"
  let plan ← mkAppM ``LibraryPlan.forPayload #[payload, roles]
  let result ← Syntax.head plan
  phase "plan reduced"
  unless result.isAppOf ``Except.ok do throwError "connection-library-discovery-refused: {result}"
  let selections ← listNodes result.getAppArgs.back!
  let cache ← Syntax.newCache
  let mut keys ← mkListLit (mkConst ``CalleeKey) []
  let mut library ← mkAppOptM ``Library.empty #[some payload]
  for selection in selections do
    let some declaration ← getNatValue? (← withTransparency .all <| whnf (← mkAppM ``LibraryPlan.Selection.declaration #[selection]))
      | throwError "connection-library-declaration-not-static"
    let some role ← getNatValue? (← withTransparency .all <| whnf (← mkAppM ``LibraryPlan.Selection.role #[selection]))
      | throwError "connection-library-role-not-static"
    let selected ← template cache payload keys ⟨declaration, role⟩
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
    phase "roles start"
    let roles ← match rolesSyntax with
      | some selectedRoles => Term.elabTerm selectedRoles (some (← mkAppM ``List #[mkConst ``Nat]))
      | none => do
        let entry ← mkAppM ``UnitPayload.entry #[payload]
        let signature ← mkAppM ``CheckedProtocol.signature #[entry]
        let roster ← mkAppM ``ProtocolSignature.roles #[signature]
        mkAppM ``List.range #[← mkAppM ``List.length #[roster]]
    let (keys, library) ← propose payload roles
    phase "bundle start"
    goal.assign (← mkAppM ``Bundle.mk #[keys, library])
    phase "bundle complete"
    replaceMainGoal []

elab "derive_connection_library" : tactic => deriveLibrary none

elab "derive_connection_library" &"roles" roles:term : tactic =>
  deriveLibrary (some roles)

end ZkcTools.ConstructionBindings.LibraryBuilder
