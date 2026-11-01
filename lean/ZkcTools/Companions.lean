module

public meta import Lean.Elab.Tactic
public meta import Lean.Util.CollectAxioms
public meta import Batteries.Util.ProofWanted

public meta section

/-! Proof aids are ordinary Lean declarations indexed by source identities.
The index is discovery metadata only: the instantiated declaration must have
exactly the independently generated type. This layer neither registers a
security meaning nor authorizes a receipt. The owning consumer still audits
its statement, premises, axioms and required links.

An instance selection precedes its template selection. A present but invalid
instance refuses; it cannot silently fall back to a generic proof. Missing and
incomplete companions remain ordinary open obligations, never new axioms. -/
set_option autoImplicit false
namespace ZkcTools.Companions
open Lean Meta Elab Term

structure Registration where
  identity : String
  declaration : Name
  deriving Inhabited

initialize registrations : SimplePersistentEnvExtension Registration (Array Registration) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun modules => modules.foldl (· ++ ·) #[]
  }

syntax (name := zkc) "zkc " str : attr

initialize registerBuiltinAttribute {
  name := `zkc
  descr := "Associate an ordinary Lean proof or contract value with a generated source obligation"
  add := fun declaration stx kind => do
    unless kind == .global do throwError "zkc companions require a global registration"
    let `(attr| zkc $identity:str) := stx | throwError "expected a companion identity"
    let identity := identity.getString
    if identity.isEmpty then throwError "a companion identity cannot be empty"
    modifyEnv fun environment => registrations.addEntry environment ⟨identity, declaration⟩
}

/-- The caller supplies static arguments independently for each selected
identity. Instance-specific declarations need not repeat a template's binders. -/
structure Selection where
  identity : String
  arguments : Array (TSyntax `term) := #[]

inductive Resolution where
  | matched (identity : String) (declaration : Name) (value : Expr)
  | missing
  | incomplete (identity : String) (declaration : Name) (reason : String)
  | refused (identity : String) (reason : String)

/-- Only declarations visible in the current module may supply a companion.
Repeated registration of one declaration is harmless; competing declarations
remain ambiguous, including when introduced by independent imported modules. -/
def candidates (environment : Environment) (identity : String) : Array Name :=
  ((registrations.getState environment).filterMap fun entry =>
    if entry.identity == identity && environment.contains entry.declaration then
      some entry.declaration else none).toList.eraseDups.toArray

/-- Orphans are feedback about source changes, not security failures. -/
def orphaned (environment : Environment) (identities : Array String) : Array Registration :=
  (registrations.getState environment).filter fun entry =>
    environment.contains entry.declaration && !identities.contains entry.identity

/-- Inspect the result sort before reducing a declaration's result. Stub wrappers
live in Type; a recursive security proposition is never a stub. -/
def placeholderWrapper? (type : Expr) : MetaM (Option Name) :=
  forallTelescope type fun _ result => do
    if ← isProp result then return none
    let result ← whnf result
    return if result.isAppOf ``ProofWanted then some ``ProofWanted
      else if result.isAppOf ``DefWanted then some ``DefWanted else none

/-- Resolve against an already fixed type. Failed elaboration is rolled back;
no companion can fill holes in the expected meaning or leave proof holes behind.
The enclosing Lean declaration performs the ordinary kernel check. -/
def resolve (selections : Array Selection) (expected : Expr) : TermElabM Resolution := do
  let expected ← instantiateMVars expected
  if expected.hasMVar then
    return .refused "" "the generated companion type must be fixed before lookup"
  for selection in selections do
    let found := candidates (← getEnv) selection.identity
    if found.isEmpty then continue
    if found.size != 1 then
      return .refused selection.identity "more than one visible companion has this identity"
    let declaration := found[0]!
    let axioms ← collectAxioms declaration
    if axioms.contains ``sorryAx then
      return .incomplete selection.identity declaration "the companion depends on sorry"
    let saved ← saveState
    try
      let function := mkIdent declaration
      let arguments := selection.arguments
      let application ← `(term| $function:ident $arguments*)
      let placeholder ← placeholderWrapper? (← getConstInfo declaration).type
      let applicationType ← match placeholder with
        | none => pure expected
        | some wrapper => mkAppM wrapper #[expected]
      let value ← Term.withoutErrToSorry <|
        elabTermEnsuringType application applicationType
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasMVar then
        saved.restore
        return .incomplete selection.identity declaration "the companion leaves unsolved arguments"
      for used in value.getUsedConstants do
        if (← collectAxioms used).contains ``sorryAx then
          saved.restore
          return .incomplete selection.identity declaration "an instantiated argument depends on sorry"
      if placeholder.isSome then
        saved.restore
        return .incomplete selection.identity declaration "unproved companion stub"
      return .matched selection.identity declaration value
    catch error =>
      if error.isRuntime then throw error
      if let .internal _ _ := error then throw error
      let message ← error.toMessageData.toString
      saved.restore
      return .refused selection.identity message
  return .missing

declare_syntax_cat companionSelection
syntax str "[" term,* "]" : companionSelection
syntax (name := companionTerm) "zkc_companion " "[" companionSelection,* "]" : term

/-- Generated assemblers use this term form; authors normally only add the
attribute to their ordinary theorem or contract definition. -/
elab_rules : term <= expected
  | `(zkc_companion [$choices:companionSelection,*]) => do
      let selections ← choices.getElems.mapM fun choice => do
        let `(companionSelection| $identity:str [$arguments:term,*]) := choice
          | throwError "invalid companion selection"
        return (⟨identity.getString, arguments.getElems⟩ : Selection)
      match ← resolve selections expected with
      | .matched _ _ value => return value
      | .missing => throwError "open companion obligation: no declaration is registered"
      | .incomplete identity _ reason => throwError "open companion obligation {identity}: {reason}"
      | .refused identity reason => throwError "refused companion {identity}: {reason}"

end ZkcTools.Companions
