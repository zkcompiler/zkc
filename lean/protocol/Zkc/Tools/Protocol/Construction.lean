module

public import Zkc.Protocol.Construction.Control
public import Zkc.Protocol.Construction.Component
public import Std.Tactic.Do
public meta import Lean.Elab.Tactic.VCGen.RuleConstruction
public meta import Lean.Elab.Tactic.VCGen.SpecDB
public meta import Lean.Meta.Tactic.SplitIf
public meta import Lean.Meta.Tactic.Rewrite
public meta import Zkc.Tools.Program.Companions.Report

/-! Checked construction uses upstream VC generation and its specification database.

Dependent Region arguments sometimes require the ordinary Lean elaborator's unification,
rather than the symbolic matcher's restricted unification. This adapter applies the same
upstream-generated backward rule with `Meta.apply`; it introduces no semantic rule or visitor.
-/

public meta section
open Lean Meta Elab Tactic
open Lean.Elab.Tactic.VCGen

namespace ProtocolProof.Tools.Construction

initialize registerTraceClass `Zkc.construction

/-- Extensible structural normalization; semantic rules still use the upstream spec database. -/
initialize constructionSimp : SimpExtension ←
  registerSimpAttr `construction_simp "structural normalization for source proof construction"

/-- Normalization of the obligations of proposition-valued readings that remain after
construction. The registration is global wherever its module is imported, but `construct`
applies the set only to the remaining goals whose statement mentions the carrier
`ProtocolProof.Truth`, its constructor or its projection (`mentionsTruth`) when the final
normalization starts; other goals are never rewritten by it. On each such goal it is applied
twice: before and after the structural `simp_all`. Stepping never uses these lemmas, so they
cannot remove the shape `pre ⊑ wp …` while rules are still being applied. -/
initialize constructionResidual : SimpExtension ←
  registerSimpAttr `construction_residual
    "normalization of residual obligations stated over `ProtocolProof.Truth`"

/-- Definitions that structural normalization evaluates. An application of a registered
definition is replaced by the result of unfolding it and reducing the matches of its body, whose
scrutinees are decided by evaluation. An application whose match is not decided stays as written,
so a symbolic argument never exposes a match. This serves definitions indexed by a decided value,
such as a transport along the membership of a literal set: no equation can rewrite them, because
the two sides of such an equation have types that agree only after evaluation. -/
initialize constructionEvaluated : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    addEntry := fun names name => names.insert name
    initial := {} }

initialize registerBuiltinAttribute {
  name := `construction_eval
  descr := "a definition that source proof construction evaluates when its matches are decided"
  applicationTime := .afterTypeChecking
  add := fun declaration _ kind => constructionEvaluated.add declaration kind }

/-- Whether a statement mentions the assertion carrier of proposition-valued readings: the type
`ProtocolProof.Truth`, its constructor or its projection. Named without an import, since this
module does not depend on the carrier's module. -/
def mentionsTruth (statement : Expr) : Bool :=
  (statement.find? fun part => match part with
    | .const name _ =>
        name == `ProtocolProof.Truth || name == `ProtocolProof.Truth.mk ||
          name == `ProtocolProof.Truth.holds
    | .proj typeName _ _ => typeName == `ProtocolProof.Truth
    | _ => false).isSome

/-- The final structural normalization of the remaining goals, in order. Every goal receives the
structural `simp_all`; a goal that mentions the carrier also receives the residual normalization
immediately before and after it, so the second application also reaches what the structural
simplification exposes in that goal. -/
def normalizeRemaining : TacticM Unit := do
  let residual := !(← constructionResidual.getTheorems).lemmaNames.isEmpty
  let mut result := []
  for goal in ← getGoals do
    if ← goal.isAssigned then continue
    let statement ← goal.withContext <| instantiateMVars (← goal.getType)
    let reading := residual && mentionsTruth statement
    setGoals [goal]
    if reading then
      evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only
        [construction_residual]))
    evalTactic (← `(tactic| all_goals try simp_all only [construction_simp]))
    if reading then
      evalTactic (← `(tactic| all_goals simp (config := { failIfUnchanged := false }) only
        [construction_residual]))
    result := result ++ (← getGoals)
  setGoals result

/-- Filter only impossible body heads before dependent unification. Structural constructor
rules inspect the actual constructor; a different named law cannot replace its source. -/
def compatibleRegionRule (pattern actual : Expr) : MetaM Bool := do
  let region (value : Expr) := value.isAppOf ``Zkc.Source.Region.denote ||
    value.isAppOf ``Zkc.Source.Region.component
  unless region pattern && region actual do return true
  let supplied := pattern.getAppArgs[pattern.getAppNumArgs - 2]!.getAppFn
  let body := actual.getAppArgs[actual.getAppNumArgs - 2]!
  unless supplied.isConst do return true
  let environment ← getEnv
  let constructor (name : Name) := (environment.find? name).any
    (fun info => match info with | .ctorInfo _ => true | _ => false)
  if constructor supplied.constName! then
    let head ← match Kernel.whnf environment (← getLCtx) body with
      | .ok value => pure value.getAppFn
      | .error error => throwError "body reduction failed: {error.toMessageData (← getOptions)}"
    return !head.isConst || !constructor head.constName! || supplied == head
  return !body.getAppFn.isConst || supplied == body.getAppFn

/-- An equation for one constructor of an operation cannot describe a call of another. Full
unification may still accept it after unfolding both sides, leaving the parameters of the unused
case unassigned, so a candidate whose left side differs from the actual program in a
constructor-headed argument is rejected before unification, as region bodies are. Proof
arguments are not compared: proofs of the same proposition unify whatever their constructors. -/
def compatibleEquation (pattern actual : Expr) : MetaM Bool := do
  let some name := pattern.getAppFn.constName? | return true
  unless actual.getAppFn.constName? == some name &&
      pattern.getAppNumArgs == actual.getAppNumArgs do return true
  let environment ← getEnv
  let constructor (value : Expr) : Option Name := do
    let head ← value.getAppFn.constName?
    match environment.find? head with
    | some (.ctorInfo _) => some head
    | _ => none
  for (supplied, argument) in pattern.getAppArgs.zip actual.getAppArgs do
    let some expected := constructor supplied | continue
    if ← (try isProof argument catch _ => pure false) then continue
    if let some found := constructor (← withDefault (whnf argument)) then
      if found != expected then return false
  return true

/-- Prefer a law for this named body over a rule that unfolds its constructor.
Priority still orders laws within each group; every candidate is checked on application. -/
def namesActualRegion (pattern actual : Expr) : MetaM Bool := do
  unless (actual.isAppOf ``Zkc.Source.Region.denote ||
      actual.isAppOf ``Zkc.Source.Region.component) &&
      pattern.getAppFn == actual.getAppFn do return false
  let body := actual.getAppArgs[actual.getAppNumArgs - 2]!.getAppFn
  unless body.isConst && pattern.getAppArgs[pattern.getAppNumArgs - 2]!.getAppFn == body do
    return false
  return match (← getEnv).find? body.constName! with
    | some (.ctorInfo _) => false
    | _ => true

/-- The answer of a premise that evaluation decides: an equation between Boolean terms that both
reduce to literals. Such a premise states a decided fact about the actual program, such as the
membership of a literal role in a literal set. A premise of another form, or one that mentions a
value evaluation cannot decide, has no answer and remains an obligation. -/
def decidedPremise? (premise : Expr) : MetaM (Option Bool) := do
  let_expr Eq sort left right := premise | return none
  unless sort.isConstOf ``Bool do return none
  let literal (value : Expr) : MetaM (Option Bool) := do
    let value ← withDefault (whnf value)
    if value.isConstOf ``Bool.true then return some true
    if value.isConstOf ``Bool.false then return some false
    return none
  let some left ← literal left | return none
  let some right ← literal right | return none
  return some (left == right)

/-- Settle the obligations of an applied law that evaluation decides. One that holds is closed
by reflexivity. When one fails, the law does not describe the actual program: the result is `none`
and the caller tries the next candidate, so laws for one operation that differ in a decided premise
select one another. Every other obligation is returned unchanged. -/
def settleDecided (goals : List MVarId) : MetaM (Option (List MVarId)) := do
  let mut remaining := []
  for goal in goals do
    if ← goal.isAssigned then continue
    let statement ← instantiateMVars (← goal.getType)
    match ← goal.withContext (decidedPremise? statement) with
    | some true =>
      let_expr Eq _ left _ := statement | return none
      goal.assign (← goal.withContext (mkExpectedTypeHint (← mkEqRefl left) statement))
    | some false =>
      trace[Zkc.construction] "refuted premise {statement}"
      return none
    | none => remaining := remaining ++ [goal]
  return some remaining

/-- Assign a parameter of a law that the program, its interpretation and its postconditions do
not determine: an instance of a class is found by instance synthesis. No other value is chosen. -/
def synthesizeParameter (parameter type : Expr) : MetaM Bool := do
  unless (← isClass? type).isSome do return false
  let some found ← synthInstance? type | return false
  isDefEq parameter found

/-- Reuse a named law with the actual postcondition before general consequence rules.
This preserves inferable mathematical parameters instead of turning them into choice holes. -/
def applyExactPostSpec (goal : MVarId) (candidate : SpecAttr.SpecTheorem)
    (info : WPApp) : MetaM (Option (List MVarId)) := do
  let (parameters, _, proof, type) ← candidate.instantiate
  if type.isAppOfArity ``Eq 3 then
    let lhs := type.getAppArgs[1]!
    let rhs := type.getAppArgs[2]!
    -- Instantiate a dependent equation against the concrete operation before abstracting
    -- it into a backward rule. This avoids splitting unrelated operation constructors.
    unless ← isDefEq lhs info.prog do return none
    let mut premises := []
    for parameter in parameters do
      let parameter ← instantiateMVars parameter
      if parameter.isMVar then
        let type ← instantiateMVars (← inferType parameter)
        if type.hasMVar then return none
        if ← isProp type then premises := premises ++ [parameter.mvarId!]
        else unless ← synthesizeParameter parameter type do return none
    let target ← instantiateMVars (← goal.getType)
    let_expr Lean.Order.PartialOrder.rel _ _ expected _ := target | return none
    let context ← withLocalDeclD `program info.Prog fun program => do
      let next := mkAppN info.head ((info.args.set! 7 program) ++ info.excessArgs)
      mkLambdaFVars #[program] (← mkAppM ``Lean.Order.PartialOrder.rel #[expected, next])
    let equality ← mkAppM ``congrArg #[context, (← instantiateMVars proof)]
    let child ← goal.replaceTargetEq ((context.app (← instantiateMVars rhs)).headBeta) equality
    return some (child :: premises)
  let_expr Lean.Order.PartialOrder.rel _ _ pre rhs := type | return none
  let some supplied := isWPApp? rhs | return none
  unless ← compatibleRegionRule supplied.prog info.prog do return none
  -- Fix the dialect, interpretation and typed contexts before matching a dependent body.
  -- Otherwise unification can try to recover the meaning by inverting Value projections.
  if supplied.prog.getAppFn == info.prog.getAppFn &&
      (info.prog.isAppOf ``Zkc.Source.Region.denote ||
        info.prog.isAppOf ``Zkc.Source.Region.component) then
    let provided := supplied.prog.getAppArgs
    let actual := info.prog.getAppArgs
    for index in [:actual.size - 2] do
      unless ← isDefEq provided[index]! actual[index]! do return none
  unless ← isDefEq supplied.prog info.prog do return none
  unless ← isDefEq supplied.instWP info.instWP do return none
  unless ← isDefEq supplied.post info.post do
    trace[Zkc.construction] "no exact postcondition"
    return none
  unless ← isDefEq supplied.args[9]! info.args[9]! do
    trace[Zkc.construction] "no exact stop"
    return none
  let mut obligations := []
  for parameter in parameters do
    let parameter ← instantiateMVars parameter
    if parameter.isMVar then
      let type ← instantiateMVars (← inferType parameter)
      if type.hasMVar then
        trace[Zkc.construction] "unfixed parameter {parameter}: {type}"
        return none
      if ← isProp type then obligations := obligations ++ [parameter.mvarId!]
      else unless ← synthesizeParameter parameter type do
        trace[Zkc.construction] "unfixed parameter {parameter}: {type}"
        return none
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ expected _ := target | return none
  let premise ← mkFreshExprSyntheticOpaqueMVar
    (← mkAppM ``Lean.Order.PartialOrder.rel #[expected, (← instantiateMVars pre).beta info.excessArgs])
  let result ← mkAppM ``Lean.Order.PartialOrder.rel_trans #[premise, mkAppN proof info.excessArgs]
  unless ← isDefEq (← inferType result) target do return none
  goal.assign result
  return some (premise.mvarId! :: obligations)

/-- Expose a structural continuation before applying a law to the preceding operation.
Only the intermediate bound is synthesized; the actual program, interpretation, final event
and requested bound remain fixed. Monotonicity of the same WP interpretation composes them. -/
def prepareContinuation (goal : MVarId) : MetaM (Option (List MVarId × MVarId)) :=
    goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ expected rhs := target | return none
  let some info := isWPApp? rhs | return none
  let prepared ← withLocalDeclD (← mkFreshBinderNameForTactic `result) info.Value fun value => do
    let continuation ← whnfR (mkApp info.post value)
    let continuation := if continuation.isAppOf ``binderNameHint then
      continuation.getAppArgs.back! else continuation
    let some _ := isWPApp? continuation | return none
    let middle ← mkFreshExprSyntheticOpaqueMVar info.Pred
    let continuationGoal ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``Lean.Order.PartialOrder.rel #[middle, continuation])
    let post ← mkLambdaFVars #[value] middle
    let postProof ← mkLambdaFVars #[value] continuationGoal
    let postProof ← mkExpectedTypeHint postProof
      (← mkAppM ``Lean.Order.PartialOrder.rel #[post, info.post])
    return some (post, postProof, continuationGoal.mvarId!, middle.mvarId!)
  let some (post, postProof, continuationGoal, middle) := prepared | return none
  let arguments := info.args.set! 8 post
  let nextTarget ← mkAppM ``Lean.Order.PartialOrder.rel
    #[expected, mkAppN info.head (arguments ++ info.excessArgs)]
  let nextGoal ← mkFreshExprSyntheticOpaqueMVar nextTarget
  let consequence ← mkAppM ``Std.WP.WP.wp_consequence
    #[info.prog, post, info.post, info.args[9]!, postProof]
  let proof ← mkAppM ``Lean.Order.PartialOrder.rel_trans
    #[nextGoal, mkAppN consequence info.excessArgs]
  unless ← isDefEq (← inferType proof) target do return none
  goal.assign proof
  return some ([continuationGoal, nextGoal.mvarId!], middle)

/-- The marker is private to this construction run; no author choice can acquire it. -/
def isDerived (value : Expr) (derived : Array MVarId) : MetaM Bool := do
  unless value.getAppFn.isMVar && value.getAppArgs.all Expr.isFVar do return false
  unless value.getAppArgs.toList.eraseDups.length == value.getAppNumArgs do return false
  let wanted ← getDelayedMVarRoot value.getAppFn.mvarId!
  return derived.contains wanted

/-- Preserve dependency on branch hypotheses and on generalized state parameters.
Lean's delayed assignments record the exact abstraction map; substitute its arguments back
before assigning the owned bound. Author choices are never added to the owned marker set. -/
partial def assignDerived (value result : Expr) : MetaM Unit := do
  let marker := value.getAppFn.mvarId!
  if let some delayed ← getDelayedMVarAssignment? marker then
    let arguments := value.getAppArgs
    unless arguments.size ≥ delayed.fvars.size do
      throwError "incomplete application of a derived continuation bound"
    let actual := arguments.extract 0 delayed.fvars.size
    let result ← result.replaceFVarsM actual delayed.fvars
    let remaining ← (arguments.extract delayed.fvars.size arguments.size).mapM
      (·.replaceFVarsM actual delayed.fvars)
    assignDerived (mkAppN (mkMVar delayed.mvarIdPending) remaining) result
  else
    let assigned ← mkLambdaFVars value.getAppArgs result
    unless ← occursCheck marker assigned do
      throwError "cyclic structural continuation bound"
    marker.assign assigned

/-- The answer of a `Decidable` instance that reduces to a fixed Boolean. `Decidable` is a
structure; `Decidable.isTrue` and `Decidable.isFalse` abbreviate its constructor, so the weak
head normal form of a decided instance is `Decidable.intro b proof` with `b` a Boolean literal. -/
def decidedAnswer? (decision : Expr) : MetaM (Option Bool) := do
  unless decision.isAppOfArity ``Decidable.intro 3 do return none
  let answer ← withDefault (whnf decision.getAppArgs[1]!)
  if answer.isConstOf ``Bool.true then return some true
  if answer.isConstOf ``Bool.false then return some false
  return none

/-- The branch that a decided `ite` or `dite` selects, exactly as written. The branch is not
reduced: a named program in it stays named, so its law still applies. -/
def selectedBranch (selected : Expr) (answer : Bool) : MetaM Expr := do
  let arguments := selected.getAppArgs
  let branch := if answer then arguments[3]! else arguments[4]!
  let extra := arguments.extract 5 arguments.size
  if selected.isAppOf ``ite then return mkAppN branch extra
  let decided ← mkEqRefl (toExpr answer)
  let proof ← mkAppOptM (if answer then ``of_decide_eq_true else ``of_decide_eq_false)
    #[some arguments[1]!, some arguments[2]!, some decided]
  return (mkAppN (branch.app proof) extra).headBeta

def prepareConditional (goal : MVarId) (derived : Array MVarId) :
    MetaM (Option (List MVarId × Array MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ left right := target | return none
  let selected := match isWPApp? right with | some info => info.prog | none => right
  unless selected.isAppOf ``ite || selected.isAppOf ``dite do return none
  let decision ← withDefault (whnf selected.getAppArgs[2]!)
  if let some answer ← decidedAnswer? decision then
    let branch ← selectedBranch selected answer
    let target := match isWPApp? right with
      | some info => mkAppN info.head ((info.args.set! 7 branch) ++ info.excessArgs)
      | none => branch
    let next ← goal.change (← mkAppM ``Lean.Order.PartialOrder.rel #[left, target])
    return some ([next], #[])
  let mut added := #[]
  if ← isDerived left derived then
    let condition := selected.getAppArgs[1]!
    let predicate ← inferType left
    let yes ← mkFreshExprSyntheticOpaqueMVar (← mkArrow condition predicate)
    let no ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← mkAppM ``Not #[condition]) predicate)
    let selectedBound ← mkAppOptM ``dite
      #[some predicate, some condition, some selected.getAppArgs[2]!, some yes, some no]
    assignDerived left selectedBound
    added := #[yes.mvarId!, no.mvarId!]
    -- Split on the condition the bound is built for: `SplitIf.splitIfAt?` would select an `if`
    -- nested inside that condition and leave the derived branches unassigned.
    let (yes, no) ← goal.byCasesDec condition selected.getAppArgs[2]!
      (← mkFreshBinderNameForTactic `h)
    return some ([← simpIfTarget yes.mvarId (useNewSemantics := true),
      ← simpIfTarget no.mvarId (useNewSemantics := true)], added)
  if let some (yes, no) ← SplitIf.splitIfAt? goal selected none then
    return some ([← simpIfTarget yes.mvarId (useNewSemantics := true),
      ← simpIfTarget no.mvarId (useNewSemantics := true)], added)
  return none

/-- Only structural intermediate bounds can be inferred from a checked law. A residual WP
is not silently accepted as a mathematical premise or exported to a protocol author. -/
def finishDerived (goal : MVarId) (derived : Array MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ left right := target | return false
  unless ← isDerived left derived do
    return false
  if (right.find? fun expression => (isWPApp? expression).isSome).isSome then return false
  -- A structural bound may depend on another owned continuation bound. Keep that
  -- dependency without solving mathematical choices or leaving a cyclic assignment.
  for dependency in ← getMVars right do
    unless derived.contains (← getDelayedMVarRoot dependency) do
      return false
  unless ← occursCheck left.getAppFn.mvarId! right do return false
  trace[Zkc.construction] "derive {left} := {right}"
  assignDerived left right
  goal.assign (← mkAppOptM ``Lean.Order.PartialOrder.rel_refl #[none, none, some right])
  return true

def applyDependentSpec (goal : MVarId) (regionOnly : Bool := false) (equationsOnly : Bool := false) :
    TacticM (Option (List MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .app _ rhs := target | return none
  let some info := isWPApp? rhs | return none
  if regionOnly && !(info.prog.isAppOf ``Zkc.Source.Region.denote ||
        info.prog.isAppOf ``Zkc.Source.Region.component) then return none
  if info.prog.isAppOf ``ite || info.prog.isAppOf ``dite then
    if let some (yes, no) ← SplitIf.splitIfAt? goal info.prog none then
      return some [← simpIfTarget yes.mvarId (useNewSemantics := true),
        ← simpIfTarget no.mvarId (useNewSemantics := true)]
  if (info.prog.isAppOf ``Zkc.Source.Region.denote ||
        info.prog.isAppOf ``Zkc.Source.Region.component) then
    trace[Zkc.construction]
      "region body head {info.prog.getAppArgs[info.prog.getAppNumArgs - 2]!.getAppFn}"
  let database ← SpecAttr.getSpecTheorems
  let indexed ← Sym.SymM.run (database.findSpecs info.prog)
  -- Definitional expansion of a dependent meaning can change discrimination-tree keys.
  -- Discovery may over-approximate; application still checks the actual complete program.
  let contextual := database.specs.values.filter fun candidate =>
    candidate.pattern.pattern.getAppFn == info.prog.getAppFn &&
      !database.erased.contains candidate.proof && !indexed.contains candidate
  let candidates := (indexed ++ contextual).insertionSort (·.priority > ·.priority)
  let mut named := #[]
  let mut structural := #[]
  for candidate in candidates do
    if ← namesActualRegion candidate.pattern.pattern info.prog then
      named := named.push candidate
    else
      structural := structural.push candidate
  for candidate in named ++ structural do
    if equationsOnly then
      match candidate.kind with
      | .triple => continue
      | .simp _ => pure ()
    unless ← compatibleRegionRule candidate.pattern.pattern info.prog do continue
    if candidate.kind matches .simp _ then
      unless ← compatibleEquation candidate.pattern.pattern info.prog do continue
    trace[Zkc.construction] "candidate {candidate.proof} for {info.prog.getAppFn}"
    let saved ← saveState
    try
      if let some goals ← applyExactPostSpec goal candidate info then
        if let some goals ← settleDecided goals then return some goals
        saved.restore
        continue
      saved.restore
      let some rule ← (tryMkBackwardRuleFromSpec candidate info).run |
        saved.restore
        continue
      if let some goals ← settleDecided (← goal.apply rule.expr) then return some goals
      saved.restore
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      let message ← error.toMessageData.toString
      trace[Zkc.construction] "application failed: {message.take 600}"
      for failure in [Kernel.Exception.deterministicTimeout, .deepRecursion, .excessiveMemory] do
        if message == (← (failure.toMessageData (← getOptions)).toString) then throw error
      saved.restore
  return none

/-- Reduce an already selected dependent equation using its actual discriminants. The
standard restricted-transparency matcher may otherwise try to split an operation which is
already fixed by the source. This does not unfold named calls or choose a different rule. -/
def reduceSelectedMatcher (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ expected rhs := target | return none
  let some info := isWPApp? rhs | return none
  let some program ← withDefault (reduceRecMatcher? info.prog) | return none
  if program == info.prog then return none
  let next := mkAppN info.head ((info.args.set! 7 program) ++ info.excessArgs)
  return some (← goal.change (← mkAppM ``Lean.Order.PartialOrder.rel #[expected, next]))

/-- Give reply-dependent primitive continuations to the same monadic construction path.
The atomic call rule leaves no residual execution fold for an author to assemble. -/
def prepareCall (goal : MVarId) : MetaM (Option (List MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ _ rhs := target | return none
  let some info := isWPApp? rhs | return none
  unless info.prog.isAppOf ``PIR.Process.call do return none
  let arguments := info.prog.getAppArgs
  let next := arguments.back!
  if next.eta.getAppFn.isConstOf ``PIR.Process.done then return none
  let equality ← mkAppOptM ``ProtocolProof.Construction.processCallBind
    #[some arguments[0]!, some arguments[1]!, some arguments[2]!, some next]
  let rewritten ← goal.rewrite target equality (config := { occs := .pos [1] })
  let child ← goal.replaceTargetEq rewritten.eNew rewritten.eqProof
  return some (child :: rewritten.mvarIds)

/-- Whether a reduction stopped at a match or a recursor whose scrutinee is not decided, or at
a function that still awaits arguments. -/
def undecided (result : Expr) : MetaM Bool := do
  let environment ← getEnv
  return match result.getAppFn with
    | .const name _ => isMatcherCore environment name || isAuxRecursor environment name ||
        isRecCore environment name
    | .proj .. | .lam .. => true
    | _ => false

/-- One application of a definition, or of a match of its body, evaluated: the definition is
unfolded and the matches are reduced, their scrutinees decided by evaluation. A number that
evaluation decides becomes its numeral. No result is returned when a match is not decided, or
when the definition is applied to fewer arguments than its body binds. -/
def evaluateDecided (term : Expr) : MetaM (Option Expr) := withDefault do
  let some name := term.getAppFn.constName? | return none
  unless term.isApp do return none
  if (← whnfR (← inferType term)).isConstOf ``Nat then
    if let some number := (← whnf term).rawNatLit? then return some (mkNatLit number)
  let unfolded ← if isMatcherCore (← getEnv) name then pure term else
    match ← unfoldDefinition? term (ignoreTransparency := true) with
    | some unfolded => pure unfolded
    | none => return none
  let result ← whnfCore unfolded
  if ← undecided result then return none
  return some result

/-- The definitions of typed slot access. -/
def slotAccess : List Name :=
  [``Zkc.Source.Environment.prepend, ``Zkc.Source.Environment.push, ``Zkc.Source.Values.get]

/-- Normalize typed slot access with the actual context, even when its type list is a
named dialect signature. Environment projections are reduced, and applications of the
definitions registered for evaluation whose matches are decided; named bodies and calls
remain visible to the specification database. Slot access is reduced with reducible unfolding,
which suffices for a context written as a list; when that stops at a match, because the context
is a list only after evaluation, the access is evaluated instead. A match that an earlier
reduction left from the body of one of these definitions is evaluated in the same way. -/
def reduceEnvironment (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let evaluated := constructionEvaluated.getState (← getEnv)
  let environment ← getEnv
  let reduced ← Meta.transform target (post := fun term => do
    if term.isAppOfArity ``Zkc.Source.Environment.prepend 8 ||
        term.isAppOfArity ``Zkc.Source.Environment.push 8 ||
        term.isAppOfArity ``Zkc.Source.Values.get 6 then
      if let some unfolded ← unfoldDefinition? term (ignoreTransparency := true) then
        let reduced ← whnfR unfolded
        if ← undecided reduced then
          if let some result ← evaluateDecided term then return .visit result
        return .visit reduced
      return .done term
    if let some name := term.getAppFn.constName? then
      let owner := if isMatcherCore environment name then name.getPrefix else name
      if evaluated.contains owner || (owner != name && slotAccess.contains owner) then
        if let some result ← evaluateDecided term then return .visit result
    return .done term)
  if reduced == target then return goal
  goal.change reduced

def construct (choices : Array (TSyntax `term)) : TacticM Unit := do
  let roots ← getGoals
  let mut requests := []
  for goal in ← getGoals do
    let fixed ← goal.withContext <| instantiateMVars (← goal.getType)
    if fixed.hasMVar then
      throwError "source construction requires a fixed request before rule or choice selection"
    -- A request may name its reading through a reducible triple abbreviation.
    let exposed ← goal.withContext <| whnfR fixed
    if !fixed.isAppOf ``Std.WP.Triple && exposed.isAppOf ``Std.WP.Triple then
      requests := requests ++ [← goal.change exposed]
    else
      requests := requests ++ [goal]
  setGoals requests
  let mut derived : Array MVarId := #[]
  let mut choiceIndex := 0
  let mut pending ← getGoals
  let mut remaining : List MVarId := []
  let mut steps : Nat := 0
  while !pending.isEmpty do
    checkSystem "source proof construction"
    steps := steps + 1
    if steps > 4096 then throwError "source construction exceeded its step limit"
    let goal := pending.head!
    pending := pending.tail!
    setGoals [← reduceEnvironment goal]
    evalTactic (← `(tactic| all_goals simp (config := { failIfUnchanged := false }) only
      [construction_simp, ite_true, ite_false, dite_true, dite_false, id_eq, eq_self, binderNameHint, Zkc.Source.Regions.denote, Zkc.Source.Operands.eval,
       Zkc.Source.Values.get_here, Zkc.Source.Values.get_there,
       Zkc.Source.Values.get, Zkc.Source.Values.singleton,
       Zkc.Source.Environment.push_here, Zkc.Source.Environment.push_there,
       Zkc.Source.Environment.prepend_weakenPrefix, Zkc.Source.Environment.prepend_here,
       Zkc.Source.Environment.prepend_weakenSuffix,
       Zkc.Source.Environment.prepend_empty, Zkc.Source.Environment.prepend_there, Zkc.Source.Values.tail,
       Zkc.Source.Environment.prepend, Zkc.Source.Environment.push]))
    if (← getGoals).isEmpty then continue
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    trace[Zkc.construction] "step {steps}: {target}"
    let structural ← goal.withContext <| forallTelescope target fun _ body => do
      if body.isAppOf ``Std.WP.Triple then return true
      let_expr Lean.Order.PartialOrder.rel _ _ _ rhs := body | return false
      return (isWPApp? rhs).isSome
    if target.isAppOf ``Std.WP.Triple then
      let unfolded ← goal.withContext <| goal.apply (← mkConstWithFreshMVarLevels ``Std.WP.Triple.intro)
      pending := unfolded ++ pending
      continue
    if target.isForall then
      let .forallE name _ _ _ := target | unreachable!
      let name ← goal.withContext <| mkFreshBinderNameForTactic name
      let (_, child) ← goal.intro name
      setGoals [child]
      pending := (← getGoals) ++ pending
      continue
    if let some child ← reduceSelectedMatcher goal then
      pending := child :: pending
      continue
    if let some children ← prepareCall goal then
      pending := children ++ pending
      continue
    if let some (children, middle) ← prepareContinuation goal then
      derived := derived.push middle
      pending := children ++ pending
      continue
    -- An already derived mathematical expression is one bound, including its
    -- conditionals. Only split an execution that still needs structural rules.
    if ← finishDerived goal derived then continue
    if let some (children, added) ← prepareConditional goal derived then
      derived := derived ++ added
      pending := children ++ pending
      continue
    if let some children ← applyDependentSpec goal true then
      pending := children ++ pending
      continue
    if let some children ← applyDependentSpec goal (equationsOnly := true) then
      pending := children ++ pending
      continue
    if structural then
      let saved ← saveState
      evalTactic (← `(tactic| vcgen (stepLimit := 1) (errorOnMissingSpec := false)))
      let children ← getGoals
      let unchanged ← match children with
        | [child] => do pure ((← instantiateMVars (← child.getType)) == target)
        | _ => pure false
      if !unchanged then
        pending := children ++ pending
        continue
      saved.restore
    evalTactic (← `(tactic| all_goals try simp only [Zkc.Source.Regions.denote,
      Zkc.Source.Operands.eval, Zkc.Source.Values.get_here, Zkc.Source.Values.get_there,
       Zkc.Source.Values.get, Zkc.Source.Values.singleton,
      Zkc.Source.Environment.push_here, Zkc.Source.Environment.push_there,
       Zkc.Source.Environment.prepend_weakenPrefix, Zkc.Source.Environment.prepend_here,
       Zkc.Source.Environment.prepend_weakenSuffix,
       Zkc.Source.Environment.prepend_empty, Zkc.Source.Environment.prepend_there, Zkc.Source.Values.tail,
      Zkc.Source.Environment.prepend, Zkc.Source.Environment.push]))
    evalTactic (← `(tactic| all_goals try exact Lean.Order.PartialOrder.rel_refl))
    for current in ← getGoals do
      let type ← current.withContext <| instantiateMVars (← current.getType)
      if Do.SpecAttr.isSpecInvariantType (← getEnv) type && choiceIndex < choices.size then
        if type.hasMVar then throwError "mathematical choice type is not fixed: {type}"
        let value ← current.withContext do
          let value ← Term.withoutErrToSorry <| Term.elabTermEnsuringType choices[choiceIndex]! type
          Term.synthesizeSyntheticMVarsNoPostponing
          let value ← instantiateMVars value
          if value.hasMVar then throwError "mathematical choice leaves unsolved arguments"
          return value
        current.assign value
        choiceIndex := choiceIndex + 1
      else if ← finishDerived current derived then
        pure ()
      else if let some children ← applyDependentSpec current then
        pending := children ++ pending
      else
        remaining := remaining ++ [current]
  if choiceIndex < choices.size then throwError "unused mathematical choice"

  -- A false branch has no executions, but its inferred predicate is still a term.
  -- Give such owned holes their canonical empty elimination rather than leaving an
  -- unresolved data metavariable behind a discharged implication.
  for bound in derived do
    unless ← bound.isAssigned do
      let saved ← saveState
      try
        setGoals [bound]
        evalTactic (← `(tactic| solve | intros; apply False.elim; simp_all))
      catch error =>
        if error.isInterrupt || error.isRuntime then throw error
        saved.restore
  -- Choice premises are processed in source order. Revisit earlier consequence goals
  -- once those choices and the continuation predicates are known.
  let mut unresolved := []
  for goal in remaining do
    unless ← goal.isAssigned do
      unless ← finishDerived goal derived do
        -- A choice assigned after a goal was set aside may have exposed slot access in it.
        unresolved := unresolved ++ [← reduceEnvironment goal]
  setGoals unresolved
  evalTactic (← `(tactic| all_goals simp (config := { failIfUnchanged := false }) only [
    construction_simp, ProtocolProof.OperationSpec.wp_upper, ProtocolProof.OperationSpec.wp_lower,
    ProtocolProof.wpFold_done, ProtocolProof.wpFold_halt, ProtocolProof.wpFold_bind,
    ProtocolProof.wpFold_call, ProtocolProof.wpFold_ite,
    ProtocolProof.OperationSpec.outcomePost, ProtocolProof.upper_entailment,
    ProtocolProof.lower_entailment, OrderDual.ofDual_toDual, OrderDual.toDual_ofDual, binderNameHint,
    Zkc.Source.Regions.denote,
    Zkc.Source.Values.get_here, Zkc.Source.Values.get_there,
       Zkc.Source.Values.get, Zkc.Source.Values.singleton,
    Zkc.Source.Operands.eval, Zkc.Source.Environment.push_here, Zkc.Source.Environment.push_there,
       Zkc.Source.Environment.prepend_weakenPrefix, Zkc.Source.Environment.prepend_here,
    Zkc.Source.Environment.prepend_weakenSuffix,
       Zkc.Source.Environment.prepend_empty, Zkc.Source.Environment.prepend_there, Zkc.Source.Values.tail, Zkc.Source.Environment.prepend,
    Zkc.Source.Environment.push]))
  evalTactic (← `(tactic| all_goals try exact Lean.Order.PartialOrder.rel_refl))

  normalizeRemaining
  evalTactic (← `(tactic| all_goals try exact Lean.Order.PartialOrder.rel_refl))
  evalTactic (← `(tactic| all_goals try solve | apply le_rfl))
  evalTactic (← `(tactic| all_goals try contradiction))

  for goal in ← getGoals do
    let type ← goal.withContext <| instantiateMVars (← goal.getType)
    if type.hasMVar then
      throwError "construction left an unfixed mathematical choice or intermediate bound:\n{type}"
    let isProp ← goal.withContext <| Meta.isProp type
    unless isProp do
      throwError "missing typed mathematical choice:\n{type}"
    if (type.find? fun expression =>
        (isWPApp? expression).isSome || expression.isAppOf ``Std.WP.Triple ||
        expression.isAppOf ``ProtocolProof.wpFold ||
        expression.isAppOf ``Zkc.Source.Region.denote ||
        expression.isAppOf ``Zkc.Source.Region.component).isSome then
      throwError "missing common construction rule; execution structure is not a mathematical obligation:\n{type}"

  -- A derived predicate may be assigned after its enclosing lambda was abstracted.
  -- Finalize those delayed wrappers from their already fixed bodies. This supplies no
  -- mathematical value: each abstraction keeps its recorded binders and checked type.
  for root in roots do
    while true do
      checkSystem "finalizing source proof abstractions"
      let proof ← instantiateMVars (mkMVar root)
      let mut progress := false
      for missing in ← getMVars proof do
        if let some delayed ← getDelayedMVarAssignment? missing then
          let value ← instantiateMVars (mkMVar delayed.mvarIdPending)
          unless value.hasMVar do
            let closed ← delayed.mvarIdPending.withContext <| mkLambdaFVars delayed.fvars value
            missing.withContext do
              unless ← isDefEq (← inferType closed) (← missing.getType) do
                throwError "derived continuation abstraction changed its type"
              missing.assign closed
            progress := true
      unless progress do break
    if (← getGoals).isEmpty then
      let proof ← instantiateMVars (mkMVar root)
      for missing in ← getMVars proof do
        missing.withContext do
          throwError "construction left an unresolved proof argument:\n{← missing.getType}"

/-- Reuse the existing obligation record with the actual local context on demand.
An open authoring goal is not evidence that a request or security endpoint holds. -/
elab "report_construction_goals" : tactic => do
  for goal in ← getGoals do
    let record ← goal.withContext do
      let expected ← instantiateMVars (← goal.getType)
      if expected.hasMVar then throwError "cannot report an unfixed construction obligation"
      ZkcTools.Companions.report {
        identity := (← goal.getTag).toString,
        responsibility := "mathematical construction obligation", expected := expected }
        (.openObligation "mathematical proof remains required" #[])
    logInfo m!"{record.compress}"

elab "construct_region" : tactic => construct #[]

elab "construct_region" " with_invariants " "[" choices:term,* "]" : tactic =>
  construct choices.getElems

end ProtocolProof.Tools.Construction
