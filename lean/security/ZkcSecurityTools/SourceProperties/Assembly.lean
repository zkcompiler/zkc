module

public meta import ZkcTools.Companions.Report
public import Zkc.Source.Structured.Import

public meta section

/-! Security property attempts use the common companion resolver and report.
Identity and navigation are supplied by the source owner. An open result is
returned as authoring data; the term form can only return a discharged proof.
It does not create declarations, assumptions, registrations or receipts. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceProperties
open Lean Meta Elab Term ZkcTools.Companions

structure Request where
  identity : String
  source : Option SourceSpan := none
  selections : Array Selection := #[]
  responsibility : String := "source property mathematics"
  goal : Option Name := none
  subject : Option SourceIdentity := none
  proofNavigation : Option StubLocation := none

def attempt (request : Request) (expected : Expr) (methods : Array DefaultMethod) :
    TermElabM (Assembly × Json) := do
  if let some goal := request.goal then validateGoal expected goal
  let stubText ← request.goal.mapM fun goal => do
    let stub : Stub := {
      identity := request.identity, goal, declaration := goal ++ `companion
      kind := if ← isProp expected then .proof else .value }
    match stub.render with
    | .ok text => pure text
    | .error reason => throwError reason
  let result ← assemble request.selections expected methods
  let row ← report {
    identity := request.identity
    source := request.source
    responsibility := request.responsibility
    expected := expected
    stubText
    goal := request.goal
    subject := request.subject
    proofNavigation := request.proofNavigation } result
  return (result, row)

syntax (name := sourceProperty) "source_property " str
  " companions " "[" companionSelection,* "]" " via " term : term

elab_rules : term <= expected
  | `(source_property $identity:str companions [$choices:companionSelection,*] via $method:term) => do
      let selections ← choices.getElems.mapM fun choice => do
        let `(companionSelection| $key:str [$arguments:term,*]) := choice
          | throwError "invalid source property companion selection"
        return (⟨key.getString, arguments.getElems⟩ : Selection)
      let (result, row) ← attempt { identity := identity.getString, selections := selections } expected
        #[⟨"source-normal-form", method⟩]
      match result with
      | .discharged value _ _ => return value
      | .openObligation _ _ => throwError "open source property obligation: {row.compress}"
      | .refused _ _ => throwError "refused source property obligation: {row.compress}"

/-- Read the actual retained Entry and its structured origin. Only projections
of the fixed source term are reduced; no source symbol is decoded as an origin. -/
def sourceIdentity (program : Expr) : MetaM SourceIdentity := do
  let snapshot ← mkAppM ``Zkc.Source.Structured.Program.snapshot #[program]
  let stringValue (expression : Expr) : MetaM String := do
    let .lit (.strVal value) ← whnf expression
      | throwError "source property identity is not fixed retained data"
    return value
  let capture ← stringValue (← mkAppM ``Zkc.Source.Structured.Snapshot.source #[snapshot])
  let symbol ← stringValue (← mkAppM ``Zkc.Source.Structured.Snapshot.entry #[snapshot])
  let mut functions ← mkAppM ``Zkc.Source.Structured.Snapshot.protocolFunctions #[snapshot]
  repeat
    let values ← whnf functions
    if values.isAppOf ``List.nil then break
    unless values.isAppOf ``List.cons do throwError "source property inventory is not fixed"
    let function := values.getAppArgs[1]!
    functions := values.getAppArgs[2]!
    let name ← stringValue (← mkAppM ``Zkc.Source.Structured.Function.name #[function])
    if name != symbol then continue
    let origin ← whnf (← mkAppM ``Zkc.Source.Structured.Function.origin #[function])
    unless origin.isAppOf ``Option.some do throwError "source property Entry has no retained origin"
    let origin ← whnf origin.getAppArgs.back!
    unless origin.isAppOf ``Zkc.Source.Structured.FunctionOrigin.protocol do
      throwError "source property Entry is not a protocol origin"
    let owner ← stringValue (← mkAppM ``Zkc.Source.Structured.ProtocolOrigin.path #[origin.getAppArgs.back!])
    return ⟨owner, symbol, capture⟩
  throwError "source property Entry has no original protocol declaration"

syntax (name := sourcePropertyAt) "source_property " "for " term:max " : " ident
  " with " str " companions " "[" companionSelection,* "]" (" via " term)? : term

@[term_elab sourcePropertyAt]
def elabSourcePropertyAt : TermElab := fun stx expected? => do
  let some expected := expected? | throwError "source_property requires a fixed expected type"
  let program : TSyntax `term := ⟨stx[2]⟩
  let goal : TSyntax `ident := ⟨stx[4]⟩
  let label : TSyntax `str := ⟨stx[6]⟩
  let choices := stx[9].getSepArgs
  let methods ← if stx[11].isNone then pure #[] else do
    let method : TSyntax `term := ⟨stx[11][1]⟩
    pure #[⟨"source-normal-form", method⟩]
  let program ← Term.withoutErrToSorry <| elabTermEnsuringType program
    (mkConst ``Zkc.Source.Structured.Program)
  synthesizeSyntheticMVarsNoPostponing
  let subject ← sourceIdentity (← instantiateMVars program)
  let goal ← realizeGlobalConstNoOverloadWithInfo goal
  let mut selections ← choices.mapM fun choice => do
    let `(companionSelection| $key:str [$arguments:term,*]) := choice
      | throwError "invalid source property companion selection"
    return (⟨key.getString, arguments.getElems⟩ : Selection)
  let identity := subject.implementationKey label.getString
  -- The generated goal has this complete telescope. Argument substitution
  -- is fixed from the consumer's context, independently of any candidate.
  let mut arguments := #[]
  for declaration in ← getLCtx do
    if !declaration.isLet && !declaration.isAuxDecl && declaration.binderInfo == .default then
      arguments := arguments.push (← Term.exprToSyntax declaration.toExpr)
  selections := selections.push ⟨identity, arguments⟩
  let position := (← getFileMap).toPosition ((← getRef).getPos?.getD 0)
  let (result, row) ← attempt {
    identity, selections, goal := some goal, subject := some subject
    proofNavigation := some ⟨← getFileName, position.line⟩ } expected
    methods
  trace[zkc.sourceProperty] "{row.compress}"
  match result with
  | .discharged value _ _ => return value
  | .openObligation _ _ => throwError "open source property obligation: {row.compress}"
  | .refused _ _ => throwError "refused source property obligation: {row.compress}"

initialize registerTraceClass `zkc.sourceProperty

end ZkcSecurity.Tools.SourceProperties
