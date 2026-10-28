module

public import Zkc.Construction.ConnectionLibrary
public import ZkcTools.ConstructionBindings.LibraryPlan
public meta import ZkcTools.ConstructionBindings.LibraryPlan
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Closure
public meta import Lean.Compiler.NoncomputableAttr

public meta section

/-! Propose a finite source library from the admitted declaration graph.
Each template is checked once in an auxiliary definition; applications retain
that definition by reference. This shares source normalization, not target
alignment. The selected library still requires the independent finite root
connection before it supplies execution correspondence. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.LibraryBuilder
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionLibrary

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
  let name ← mkAuxDeclName `connectionCallee
  let reference ← mkAuxDefinitionFor name proposed (compile := false)
  -- A template is checked proof data. Mark the auxiliary declaration as well
  -- as its public consumer, so downstream code generation cannot try to
  -- compile an intentionally uncompiled dependent record.
  modifyEnv (addNoncomputable · name)
  return reference

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

end ZkcTools.ConstructionBindings.LibraryBuilder
