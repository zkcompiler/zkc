module

public import ZkcSecurity.Families.Sigma.Realization
public import ZkcSecurity.FiatShamir.HonestSampledReadback
public import ZkcSecurity.FiatShamir.SampledCompiled
public import ZkcSecurity.Claims.SubjectABI
public meta import ZkcSecurity.Tools.InputLaws
public meta import Zkc.Construction.ProcessViewTactic
public meta import Lean.Elab.Tactic
public meta import Zkc.Construction.TransportReduction
public meta import Mathlib.Tactic.Linter.UnusedTactic
public meta import Batteries.Linter.UnreachableTactic

@[expose] public meta section

/-! Installed Sigma proof search over actual constructed Process terms.
Private requests require the request-fixed capability predicate. Communication
and queries retain that capability through the entire derivation, with exact
histories and nominal origins; subsequent private draws remain permitted.
There is no alternate evaluator and no protocol-name or source-hash dispatch. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SigmaReadback
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.FiatShamir

macro "normalize_sigma_process " "[" definitions:term,* "]" : tactic => do
  let definitions ← definitions.getElems.mapM fun declaration =>
    `(Parser.Tactic.simpLemma| $declaration:term)
  let rules ← #[
    `(Parser.Tactic.simpLemma| Domain.View.participant),
    `(Parser.Tactic.simpLemma| Domain.View.sequence),
    `(Parser.Tactic.simpLemma| Domain.View.localService),
    `(Parser.Tactic.simpLemma| Domain.View.receive),
    `(Parser.Tactic.simpLemma| Domain.View.send),
    `(Parser.Tactic.simpLemma| Domain.View.indicesEmpty),
    `(Parser.Tactic.simpLemma| Domain.View.indicesAppend),
    `(Parser.Tactic.simpLemma| Domain.View.observe),
    `(Parser.Tactic.simpLemma| Domain.View.challenge),
    `(Parser.Tactic.simpLemma| Domain.View.calculation),
    `(Parser.Tactic.simpLemma| Domain.View.append),
    `(Parser.Tactic.simpLemma| Domain.View.empty),
    `(Parser.Tactic.simpLemma| Domain.View.guard),
    `(Parser.Tactic.simpLemma| Domain.read),
    `(Parser.Tactic.simpLemma| Domain.localCoordinates),
    `(Parser.Tactic.simpLemma| Domain.sortsMatch),
    `(Parser.Tactic.simpLemma| Domain.Value.sort),
    `(Parser.Tactic.simpLemma| Domain.Payload.ty),
    `(Parser.Tactic.simpLemma| Domain.Value.encode),
    `(Parser.Tactic.simpLemma| Domain.Payload.value),
    `(Parser.Tactic.simpLemma| ↓reduceTransport),
    `(Parser.Tactic.simpLemma| Domain.Payload.ofValue),
    `(Parser.Tactic.simpLemma| Domain.dataType),
    `(Parser.Tactic.simpLemma| Domain.localOrigin),
    `(Parser.Tactic.simpLemma| Domain.templateOrigin),
    `(Parser.Tactic.simpLemma| Domain.queryOrigin),
    `(Parser.Tactic.simpLemma| Domain.Calculations.fieldAdd),
    `(Parser.Tactic.simpLemma| Domain.Calculations.fieldMultiply),
    `(Parser.Tactic.simpLemma| Domain.Calculations.fieldEqual),
    `(Parser.Tactic.simpLemma| Domain.Calculations.fieldConstant),
    `(Parser.Tactic.simpLemma| Domain.Calculations.booleanConstant),
    `(Parser.Tactic.simpLemma| Domain.Calculations.booleanEqual),
    `(Parser.Tactic.simpLemma| ZkcSecurity.Families.Sigma.Realization.groupScale),
    `(Parser.Tactic.simpLemma| ZkcSecurity.Families.Sigma.Realization.groupAdd),
    `(Parser.Tactic.simpLemma| ZkcSecurity.Families.Sigma.Realization.groupEqual),
    `(Parser.Tactic.simpLemma| ZkcSecurity.Families.Sigma.Realization.booleanAnd),
    `(Parser.Tactic.simpLemma| List.mapM_cons),
    `(Parser.Tactic.simpLemma| List.mapM_nil),
    `(Parser.Tactic.simpLemma| Bind.bind),
    `(Parser.Tactic.simpLemma| Option.bind),
    `(Parser.Tactic.simpLemma| Option.pure_def),
    `(Parser.Tactic.simpLemma| List.getElem?_cons_zero),
    `(Parser.Tactic.simpLemma| List.getElem?_cons_succ),
    `(Parser.Tactic.simpLemma| List.cons_append),
    `(Parser.Tactic.simpLemma| List.nil_append),
    `(Parser.Tactic.simpLemma| List.map_cons),
    `(Parser.Tactic.simpLemma| List.map_nil),
    `(Parser.Tactic.simpLemma| PIR.Process.bind),
    `(Parser.Tactic.simpLemma| beq_self_eq_true),
    `(Parser.Tactic.simpLemma| ite_true),
    `(Parser.Tactic.simpLemma| decide_true),
    `(Parser.Tactic.simpLemma| decide_false),
    `(Parser.Tactic.simpLemma| Bool.false_beq),
    `(Parser.Tactic.simpLemma| and_true),
    `(Parser.Tactic.simpLemma| true_and),
    `(Parser.Tactic.simpLemma| and_self),
    `(Parser.Tactic.simpLemma| ZkcSecurity.Families.Sigma.response_equation)].mapM id
  let lemmas := definitions ++ rules
  `(tactic| try simp only [$lemmas,*])

/-- Normalize the actual retained pure formula only to its returned Boolean.
The checker has already fixed the formula, arguments and nominal model. No
protocol-name match or alternate formula evaluator supplies this fact. -/
elab "prepare_sigma_relation " "for " subject:term " reading " read:term : tactic =>
    withMainContext <| Term.withoutErrToSorry <| withoutRecover do
  let law ← `(ZkcSecurity.Claims.HonestPair.Subject.relation_iff_of_read $subject _ _ $read)
  let fact ← InputLaws.forwardIff law
  withMainContext do
    let declaration ← fact.getDecl
    let some (_, left, right) := declaration.type.eq?
      | throwError "retained Sigma relation must be a formula equation"
    let left ← withTransparency .all <| whnf left
    let right ← withTransparency .all <| whnf right
    unless left.isAppOf ``PIR.Process.done && right.isAppOf ``PIR.Process.done do
      throwError "retained formula does not return a Boolean"
    let normalized ← mkEq left right
    let name := mkIdent declaration.userName
    let normalized ← Term.exprToSyntax normalized
    evalTactic (← `(tactic| change $normalized at $name:ident))
    let valuesType ← Term.exprToSyntax (← inferType left.getAppArgs.back!)
    let truth := mkIdent (← mkFreshUserName `formulaTruth)
    evalTactic (← `(tactic| have $truth:ident := congrArg
      (fun (values : $valuesType) => values.get .here) (PIR.Process.done.inj $name:ident)))
    let readProof ← Term.elabTerm read none
    let some (_, _, bound) := (← inferType readProof).eq?
      | throwError "expected the actual ABI selector-read equation"
    let bound ← whnf bound
    unless bound.isAppOf ``Option.some do throwError "expected complete relation arguments"
    let some argumentsName := bound.getAppArgs.back!.getAppFn.constName?
      | throwError "expected an ABI argument declaration"
    let arguments := mkIdent argumentsName
    let arguments ← `(Parser.Tactic.simpLemma| $arguments:ident)
    evalTactic (← `(tactic| simp only [$arguments, Operands.eval,
      Environment.prepend, Environment.push, Values.get,
      Bool.and_eq_true, decide_eq_true_eq] at $truth:ident))
    withMainContext do
      let declaration ← (← getFVarId truth).getDecl
      let normalized ← transform declaration.type (pre := fun expression => do
        if expression.isAppOf ``Values.get then
          let reduced ← withTransparency .all <| whnf expression
          if reduced != expression then return .visit reduced
        return .continue)
      let normalized ← Term.exprToSyntax normalized
      evalTactic (← `(tactic| change $normalized at $truth:ident))
  InputLaws.splitFacts
  evalTactic (← `(tactic| subst_vars))

/-- Fail-closed recursion: only checked constructor rules may advance a goal.
The deterministic constructor closes returned leaves. All communication rules
retain the sampled relation so a later private request can be certified. -/
partial def prove (goal : MVarId) (normalize : TSyntax `tactic)
    (allowed finish : TSyntax `tactic) : TacticM Unit :=
  goal.withContext <| Term.withoutErrToSorry <| withoutRecover do
    setGoals [goal]
    evalTactic normalize
    if (← getGoals).isEmpty then return
    let [goal] ← getGoals | throwError "Sigma normalization left multiple obligations"
    goal.withContext do
      let target ← whnf (← instantiateMVars (← goal.getType))
      let sampled := target.isAppOf ``SampledReadback
      unless sampled || target.isAppOf ``Readback do
        throwError "expected actual sampled/deterministic Readback: {← ppGoal goal}"
      let arguments := target.getAppArgs
      let left ← whnf arguments[arguments.size-2]!
      let right ← whnf arguments.back!
      let effect? (process : Expr) : Option Name := do
        guard (process.isAppOf ``PIR.Process.call)
        process.getAppArgs[process.getAppArgs.size-2]!.getAppFn.constName?
      let leftEffect := effect? left
      let rightEffect := effect? right
      let rules : Array (TSyntax `term) ← if sampled then
        if leftEffect == some ``Domain.Effect.checkpoint then
          pure #[← `(SampledReadback.checkpointLeft)]
        else if leftEffect == some ``Domain.Effect.localService then
          pure #[← `(SampledReadback.localServiceLeft)]
        else if rightEffect == some ``Domain.Effect.checkpoint then
          pure #[← `(SampledReadback.checkpointRight)]
        else if leftEffect == some ``Domain.Effect.observe then
          pure #[← `(SampledReadback.observeLeft)]
        else if rightEffect == some ``Domain.Effect.observe then
          pure #[← `(SampledReadback.observeRight)]
        else if leftEffect == some ``Domain.Effect.send && rightEffect == some ``Domain.Effect.receive then
          pure #[← `(SampledReadback.sendReceive)]
        else if rightEffect == some ``Domain.Effect.send then
          pure #[← `(SampledReadback.sendRight)]
        else if leftEffect == some ``Domain.Effect.query && rightEffect == some ``Domain.Effect.query then
          pure #[← `(SampledReadback.query)]
        else if left.isAppOf ``PIR.Process.done && right.isAppOf ``PIR.Process.done then
          pure #[← `(SampledReadback.deterministic)]
        else throwError "unmatched effect or stopped sampled execution: {← ppGoal goal}"
      else if left.isAppOf ``PIR.Process.done && right.isAppOf ``PIR.Process.done then
        pure #[← `(Readback.done)]
      else if leftEffect == some ``Domain.Effect.checkpoint then pure #[← `(Readback.checkpointLeft)]
      else if rightEffect == some ``Domain.Effect.checkpoint then pure #[← `(Readback.checkpointRight)]
      else if leftEffect == some ``Domain.Effect.observe then pure #[← `(Readback.observeLeft)]
      else if rightEffect == some ``Domain.Effect.observe then pure #[← `(Readback.observeRight)]
      else if leftEffect == some ``Domain.Effect.send && rightEffect == some ``Domain.Effect.receive then
        pure #[← `(Readback.sendReceive)]
      else if rightEffect == some ``Domain.Effect.send then pure #[← `(Readback.sendRight)]
      else if leftEffect == some ``Domain.Effect.query && rightEffect == some ``Domain.Effect.query then
        pure #[← `(Readback.query)]
      else throwError "unmatched effect or stopped Sigma execution: {← ppGoal goal}"
      for rule in rules do
        let proof ← Term.elabTerm rule none
        let premises ← withTransparency .default <| goal.apply proof
        for premise in premises do
          unless ← premise.isAssigned do
            let (_, body) ← premise.intros
            let recursive ← body.withContext do
              let target ← whnf (← body.getType)
              pure (target.isAppOf ``SampledReadback || target.isAppOf ``Readback)
            if recursive then prove body normalize allowed finish
            else body.withContext do
              setGoals [body]
              if left.isAppOf ``PIR.Process.done && right.isAppOf ``PIR.Process.done then
                evalTactic finish
              else evalTactic allowed
              unless (← getGoals).isEmpty do throwError "Sigma side condition remains: {← ppGoal body}"

elab (name := proveSigmaReadback) "prove_sigma_readback " " normalizing " normalize:tactic
    " authorizing " allowed:tactic " finishing " finish:tactic : tactic => withMainContext do
  let pending := (← getGoals).tail
  prove (← getMainGoal) normalize allowed finish
  setGoals pending

-- These callbacks are conditional proof-search inputs, like simp dischargers.
-- Keep linting the enclosing tactic and all surrounding proof steps.
initialize Mathlib.Linter.UnusedTactic.addIgnoreTacticKind ``proveSigmaReadback
initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``proveSigmaReadback

end ZkcSecurity.Tools.SigmaReadback
