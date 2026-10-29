module

public import Zkc.Construction.ConnectionLibrary
public import Zkc.Source.KernelRfl
public import ZkcTools.ConstructionBindings.LibraryPlan
public meta import ZkcTools.ConstructionBindings.LibraryPlan
public meta import Lean.Elab.Tactic
public meta import ZkcTools.StructuredSource.Presentation.Syntax
public meta import ZkcTools.ConstructionBindings.Syntax
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

/-- Compiled proposal using the existing normalizer and literal printer. This
produces source text, never an equation or a proof. Public visibility lets the
meta evaluator invoke it from an importing module. -/
def normalizationLiteral (signature : Signature) {inputs outputs : List Ty}
    (body : Region protocolDialect inputs outputs) (role roster : Nat)
    (pattern : InputPattern inputs) : Except String String := do
  let form ← NormalForm.normalize signature body role roster pattern
  return ZkcTools.StructuredSource.Presentation.formLiteral form

/-- Reduce the finite inputs, then run the normalizer in compiled meta code.
Reducing its whole call with `whnf` repeatedly expands intermediate symbolic
states. The proposed literal is checked against that unchanged call below.
Implicit data indices must also be reduced: a generated syntax constant can
be noncomputable even when its closed data has an executable literal. -/
private unsafe def proposeNormalization (computation : Expr) : TermElabM Expr := do
  let computation ← instantiateMVars computation
  unless computation.isAppOf ``NormalForm.normalize &&
      !computation.hasFVar && !computation.hasMVar do
    throwError "connection-normalization-not-closed"
  let mut arguments := computation.getAppArgs
  for index in [:arguments.size] do
    arguments := arguments.set! index (← withTransparency .all <|
      reduce arguments[index]! (explicitOnly := false) (skipTypes := false))
  let proposal := mkAppN (mkConst ``normalizationLiteral) arguments
  let text ← evalExpr (Except String String)
    (← mkAppM ``Except #[mkConst ``String, mkConst ``String]) proposal
  let .ok text := text | throwError "connection-native-normalization-refused"
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "connection-native-normalization-syntax"
  let resultType ← inferType computation
  Term.elabTerm parsed (some resultType.getAppArgs.back!)

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
  let literal ← unsafe proposeNormalization computation
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
