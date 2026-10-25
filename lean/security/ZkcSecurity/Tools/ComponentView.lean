module

public import ZkcSecurity.FiatShamir.DomainComposition
public meta import Lean.Elab.Tactic
public meta import Lean.Elab.DeclarationRange
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Meta.Eqns

@[expose] public meta section

/-! Build readable component presentations from the admitted source and installed
checked rules. Every synthesis step produces an ordinary Bridge proof. The
source continuation, result map and exact stopped outcomes remain obligations;
unknown effects and helpers are never replaced by an unrestricted summary. -/

open Lean Meta Elab Tactic Command
namespace ZkcSecurity.Tools.ComponentView
partial def firstCondition (expression : Expr) : Option Expr :=
  if expression.isAppOf ``ite then some expression.getAppArgs[1]!
  else match expression with
    | .app fn arg => firstCondition fn <|> firstCondition arg
    | .mdata _ body => firstCondition body
    | _ => none

partial def synthesize (goal : MVarId) (rules : Array (TSyntax `term))
    (normalizer side finish : TSyntax `tactic) : TacticM Unit := goal.withContext <|
      Term.withoutErrToSorry <| withoutRecover do
  setGoals [goal]
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| try simp_all only [ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]))
  evalTactic normalizer
  if (← getGoals).isEmpty then return
  let goals ← getGoals
  let mut bridges := []
  for candidate in goals do
    let kind ← candidate.withContext do
      forallTelescope (← candidate.getType) fun _ body => do
        let body ← whnf body
        pure (body.isAppOf ``ZkcSecurity.FiatShamir.DomainReduction.Bridge,
          body.isAppOf ``PIR.Process)
    if kind.1 then bridges := bridges ++ [candidate]
    else unless kind.2 do throwError "normalizer left a non-presentation obligation: {MessageData.ofGoal candidate}"
  let [goal] := bridges | throwError "normalizer must leave one Bridge"
  setGoals [goal]
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOf ``ZkcSecurity.FiatShamir.DomainReduction.Bridge do
      throwError "expected a Bridge: {target}"
    let args := target.getAppArgs
    let actual := args[args.size - 2]!
    if actual.isAppOf ``PIR.Process.done then
      evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.DomainReduction.Bridge.done))
      evalTactic finish
      unless (← getGoals).isEmpty do throwError "terminal postcondition remains"
      return
    if actual.isAppOf ``PIR.Process.halt then
      evalTactic (← `(tactic| exact ZkcSecurity.FiatShamir.DomainReduction.Bridge.halt _ _))
      return
    if let some condition := firstCondition actual then
      let conditionSyntax ← Term.exprToSyntax condition
      evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.DomainReduction.Bridge.byCasesPresentation $conditionSyntax))
      let branches ← (← getGoals).filterM fun g => g.withContext do
        forallTelescope (← g.getType) fun _ body =>
          pure (body.isAppOf ``ZkcSecurity.FiatShamir.DomainReduction.Bridge)
      for branch in branches do synthesize branch rules normalizer side finish
      return
    let original ← saveState
    let mut errors : Array MessageData := #[]
    for rule in rules do
      original.restore
      try
        let proof ← Term.elabTerm rule none
        let obligations ← withReducible <| goal.apply proof
        let mut continuations := []
        for premise in obligations do
          let isBridge ← premise.withContext do
            forallTelescope (← premise.getType) fun _ body =>
              pure (body.isAppOf ``ZkcSecurity.FiatShamir.DomainReduction.Bridge)
          if isBridge then continuations := continuations ++ [premise]
          else
            let isPresentation ← premise.withContext do
              forallTelescope (← premise.getType) fun _ body => do
                pure ((← whnf body).isAppOf ``PIR.Process)
            unless isPresentation do
              setGoals [premise]
              evalTactic side
              unless (← getGoals).isEmpty do throwError "side premise remains"
        for continuation in continuations do
          synthesize continuation rules normalizer side finish
        return
      catch error => errors := errors.push error.toMessageData
    original.restore
    throwError "no checked synthesis rule: {errors}"

/-- Construct the presentation and its bridge together, with a fresh data
metavariable whose scope precedes all proof-only component hypotheses. -/
elab "construct_component_view " "[" rules:term,* "]" " normalizing " normalizer:tactic
    " solving " side:tactic " finishing " finish:tactic : tactic => withMainContext <| withoutRecover do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  let target ← whnf (← goal.getType)
  unless target.isAppOfArity ``Subtype 2 do
    throwError "construct_component_view expects a presentation with its Bridge proof"
  let arguments := target.getAppArgs
  let proposed ← mkFreshExprMVar arguments[0]! .natural
  let meaning ← whnf (mkApp arguments[1]! proposed)
  unless meaning.isAppOf ``ZkcSecurity.FiatShamir.DomainReduction.Bridge do
    throwError "the checked presentation predicate must be a Bridge"
  let bridgeArguments := meaning.getAppArgs
  unless ← isDefEq bridgeArguments.back! proposed do
    throwError "the presentation must be the Bridge's presented process"
  for argument in bridgeArguments[:bridgeArguments.size - 1] do
    if (argument.find? (· == proposed)).isSome then
      throwError "the source, history, interface and postcondition must be fixed before presentation construction"
  let proof ← mkFreshExprMVar meaning .natural
  synthesize proof.mvarId! rules.getElems normalizer side finish
  let proposed ← instantiateMVars proposed
  let proof ← instantiateMVars proof
  if proposed.hasMVar || proof.hasMVar then
    throwError "component view construction left unresolved obligations"
  goal.assign (← mkAppM ``Subtype.mk #[proposed, proof])
  setGoals pending

/-- Extract the data field of a checked dependent pair into a regular exposed
constant, and retain its proof as a named theorem over that exact constant. -/
elab "project_checked_view " assembled:ident " as " viewName:ident " with " proofName:ident : command => do
  let sourceName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo assembled
  let viewDecl := (← getCurrNamespace) ++ viewName.getId
  let proofDecl := (← getCurrNamespace) ++ proofName.getId
  liftTermElabM do
    let info ← getConstInfo sourceName
    let levels := info.levelParams.map Level.param
    forallTelescope info.type fun arguments resultType => do
      let resultType ← whnf resultType
      unless resultType.isAppOfArity ``Subtype 2 do
        throwError "checked presentation must return a subtype"
      let parameters := resultType.getAppArgs
      let assembledValue := mkAppN (mkConst sourceName levels) arguments
      let some presented ← withTransparency .all <| project? assembledValue 0
        | throwError "checked presentation must reduce to a constructed dependent pair"
      -- Presentation data must not acquire a prerequisite for an unused
      -- proof-only binder. Retain ordinary inputs, and retain proof binders
      -- when the data, its type or another retained binder actually uses them.
      let uses (expression parameter : Expr) := (expression.find? (· == parameter)).isSome
      let mut viewArguments := arguments
      for parameter in arguments.reverse do
        if (← isProp (← inferType parameter)) || (← parameter.fvarId!.getDecl).binderInfo.isInstImplicit then
          let mut required := uses presented parameter || uses parameters[0]! parameter
          for retained in viewArguments do
            if retained != parameter && uses (← inferType retained) parameter then
              required := true
          unless required do viewArguments := viewArguments.filter (· != parameter)
      let viewType ← mkForallFVars viewArguments parameters[0]!
      let viewValue ← mkLambdaFVars viewArguments presented
      if viewType.hasMVar || viewValue.hasMVar then
        throwError "checked presentation contains unresolved metavariables"
      addDecl (.defnDecl {
        name := viewDecl
        levelParams := info.levelParams
        type := viewType
        value := viewValue
        hints := .regular (getMaxHeight (← getEnv) viewValue + 1)
        safety := .safe
      }) true
      modifyEnv (addNoncomputable · viewDecl)
      saveEqnAffectingOptions viewDecl
      enableRealizationsForConst viewDecl
      discard <| getEqnsFor? viewDecl
      let named := mkAppN (mkConst viewDecl levels) viewArguments
      let proofType ← mkForallFVars arguments (mkApp parameters[1]! named)
      let proofValue ← mkLambdaFVars arguments (mkProj ``Subtype 1 assembledValue)
      addDecl (.thmDecl {
        name := proofDecl
        levelParams := info.levelParams
        type := proofType
        value := proofValue
      })
  addDeclarationRangesFromSyntax viewDecl (← getRef) viewName
  addDeclarationRangesFromSyntax proofDecl (← getRef) proofName
end ZkcSecurity.Tools.ComponentView
