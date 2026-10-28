module

public import ZkcSecurity.Obligations.Derivation
public import Zkc.Obligations.RepeatedComponent
public meta import ZkcSecurity.Tools.ComponentAuthoringReport
public meta import Lean.Elab.Tactic
public meta import Mathlib.Tactic.Tauto

@[expose] public meta section

/-! Assemble rejection certificates from installed component contracts. The
actual process supplies sequencing, branches and stops. Mathematical admission
conditions are proved or split into two checked cases. A component may be
forgotten only when the continuation still proves the requested postcondition.
Every continuation is checked at its actual returned value and reached history.
The tactic constructs ordinary Derivation terms, interpreted by the existing
reduction engine; it introduces no new proof or probability semantics. -/

namespace ZkcSecurity.Tools.ComponentDerivation
open Lean Meta Elab Tactic

def derivationGoals : TacticM (List MVarId) := do
  (← getGoals).filterM fun goal => goal.withContext do
    forallTelescope (← goal.getType) fun _ body =>
      pure (body.isAppOf ``Zkc.Obligations.Derivation)

def proveSide (goal : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [goal]
    evalTactic (← `(tactic| solve | assumption | tauto))
    if (← getGoals).isEmpty then return true
  catch _ => pure ()
  saved.restore
  return false

partial def derive (goal : MVarId) (leaves definitions : Array (TSyntax `term))
    (finish : TSyntax `tactic) : TacticM Unit := goal.withContext <| classical <| Term.withoutErrToSorry <| withoutRecover do
  setGoals [goal]
  let simpTerms := definitions ++ #[← `(PIR.Process.bind_assoc), ← `(PIR.Process.bind)]
  let simpLemmas ← simpTerms.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  evalTactic (← `(tactic| try simp only [$simpLemmas,*]))
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let process := target.getAppArgs.back!
  if process.isAppOf ``PIR.Process.halt then
    evalTactic (← `(tactic| exact Zkc.Obligations.Derivation.halt _))
    return
  if process.isAppOf ``PIR.Process.done then
    evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.done))
    evalTactic finish
    unless (← getGoals).isEmpty do throwError "terminal obligation remains: {← ppGoal (← getMainGoal)}"
    return
  if process.isAppOf ``ite then
    evalTactic (← `(tactic| split))
    for branch in ← getGoals do derive branch leaves definitions finish
    return
  unless process.isAppOf ``PIR.Process.bind do
    throwError "no installed structural derivation for {process.getAppFn}"
  let original ← saveState
  let mut missing : Option Expr := none
  let mut errors : Array MessageData := #[]
  for leaf in leaves do
    original.restore
    try
      evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.bind))
      let [head, continuation] ← derivationGoals | throwError "unexpected bind goals"
      setGoals [head]
      -- Elaborate indices normally, but do not unfold an opaque component
      -- body while trying to match the next installed theorem.
      let proof ← Term.elabTerm leaf none
      setGoals (← withReducible <| head.apply proof)
      let obligations ← getGoals
      let mut ready := true
      for obligation in obligations do
        unless ← proveSide obligation do
          let ty ← instantiateMVars (← obligation.getType)
          if (← isProp ty) && !ty.hasMVar then missing := some ty
          ready := false
      if ready then
        setGoals [continuation]
        evalTactic (← `(tactic| intro reached value holds))
        derive (← getMainGoal) leaves definitions finish
        return
    catch error => errors := errors.push error.toMessageData
  original.restore
  if let some premise := missing then
    -- Splitting a mathematical admission condition supplies no new assumption:
    -- both branches must produce derivations of the same actual process.
    let negative ← mkFreshExprMVar (mkNot premise)
    let refuted ← proveSide negative.mvarId!
    original.restore
    if !refuted then
      let conditionSyntax ← Term.exprToSyntax premise
      evalTactic (← `(tactic| by_cases componentCondition : $conditionSyntax))
      for branch in ← getGoals do derive branch leaves definitions finish
      return
  evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.bind))
  let [head, continuation] ← derivationGoals | throwError "unexpected bind goals"
  setGoals [head]
  evalTactic (← `(tactic| exact ZkcSecurity.Obligations.unrestricted _ _))
  setGoals [continuation]
  evalTactic (← `(tactic| intro reached value holds))
  try
    derive (← getMainGoal) leaves definitions finish
  catch error =>
    throwError "component derivation failed: {error.toMessageData}\ninstalled rules: {errors}"

elab "derive_component_rejection " "[" leaves:term,* "]" " unfolding " "[" definitions:term,* "]" " finishing " finish:tactic : tactic =>
    withMainContext <| withoutRecover do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Zkc.Obligations.Derivation do
    throwError "derive_component_rejection expects a component derivation"
  let pending := (← getGoals).tail
  derive (← getMainGoal) leaves.getElems definitions.getElems finish
  setGoals ((← getGoals) ++ pending)
end ZkcSecurity.Tools.ComponentDerivation

namespace ZkcSecurity.Tools.ComponentDerivation
open Lean Meta Elab Tactic
open ComponentAuthoringReport

/-! The property builder retains unsolved mathematical premises as ordinary
goals. Installed rules are tried before unfolding, and a symbolic loop uses a
single supplied invariant, independently of its count. Speculative rules and
unrestricted-prefix attempts are rolled back when they cannot build the suffix.
Only the main goal is processed; unrelated pending caller goals are preserved. -/

structure AssemblyResult where
  pending : List MVarId := []
  entries : Array Entry := #[]

def residual (goal : MVarId) (address : List String) (layer method : String) : TacticM AssemblyResult := do
  return ⟨[goal], #[← capture goal address layer method]⟩

def sideObligations (goals : List MVarId) (address : List String) : TacticM AssemblyResult := do
  let mut result : AssemblyResult := {}
  for goal in goals do
    unless ← proveSide goal do
      let target ← instantiateMVars (← goal.getType)
      unless ← isProp target do throwError "installed rule left a non-propositional parameter"
      if target.hasMVar then throwError "installed rule left an undetermined mathematical premise"
      result := ⟨result.pending ++ [goal], result.entries.push
        (← capture goal address "mathematical premise" "installed law premise")⟩
  return result

partial def assemble (goal : MVarId) (leaves definitions invariants : Array (TSyntax `term))
    (finish : TSyntax `tactic) (address : List String) : TacticM AssemblyResult :=
    goal.withContext <| classical <| Term.withoutErrToSorry <| withoutRecover do
  setGoals [goal]
  -- Introduce only the telescope of this obligation, retaining every local
  -- returned value, accumulated history and invariant hypothesis in reports.
  evalTactic (← `(tactic| intros))
  let goal ← getMainGoal
  let original ← saveState
  for leaf in leaves do
    original.restore
    try
      let record ← capture goal address "installed component" "installed law"
      let proof ← Term.elabTerm leaf none
      let obligations ← withReducible <| goal.apply proof
      let result ← sideObligations obligations (address ++ ["premise"])
      return ⟨result.pending, #[record] ++ result.entries⟩
    catch _ => pure ()
  original.restore
  let terms := definitions ++ #[← `(PIR.Process.bind_assoc), ← `(PIR.Process.bind)]
  let simplifiers ← terms.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  evalTactic (← `(tactic| try simp only [$simplifiers,*]))
  if (← getGoals).isEmpty then return {}
  let goal ← getMainGoal
  let target ← whnf (← instantiateMVars (← goal.getType))
  unless target.isAppOf ``Zkc.Obligations.Derivation do
    return ← residual goal address "mathematical premise" "normalization residual"
  let process := target.getAppArgs.back!
  if process.isAppOf ``PIR.Process.done then
    let record ← capture goal address "structural assembly" "return"
    evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.done))
    let saved ← saveState
    try evalTactic finish catch _ => saved.restore
    let pending ← getGoals
    let mut entries := #[record]
    for obligation in pending do
      entries := entries.push (← capture obligation (address ++ ["return property"])
        "mathematical premise" "terminal property")
    return ⟨pending, entries⟩
  if process.isAppOf ``PIR.Process.halt then
    let record ← capture goal address "structural assembly" "stop (partial safety only)"
    evalTactic (← `(tactic| exact Zkc.Obligations.Derivation.halt _))
    return ⟨[], #[record]⟩
  if process.isAppOf ``ite then
    let record ← capture goal address "structural assembly" "actual branch"
    evalTactic (← `(tactic| split))
    let branches ← getGoals
    let mut result : AssemblyResult := ⟨[], #[record]⟩
    for branch in branches, index in List.range branches.length do
      let next ← assemble branch leaves definitions invariants finish (address ++ [s!"branch {index}"])
      result := ⟨result.pending ++ next.pending, result.entries ++ next.entries⟩
    return result
  if process.isAppOf ``PIR.Process.call then
    let saved ← saveState
    -- Try only the installed absorption's definitional constructor. Receives
    -- cover every recovered reply; queries here use the empty exceptional set.
    -- A nonempty escape always needs an installed mathematical rule.
    let rules : Array (TSyntax `tactic) := #[
      ← `(tactic| apply Zkc.Obligations.Derivation.send rfl),
      ← `(tactic| apply Zkc.Obligations.Derivation.receive rfl),
      ← `(tactic| exact Zkc.Obligations.Derivation.refuse rfl),
      ← `(tactic| apply Zkc.Obligations.Derivation.query rfl (fun _ => False)
        (by simp [ZkcSecurity.Obligations.boundedEscape]))]
    for rule in rules do
      saved.restore
      try
        let record ← capture goal address "installed operation" "all replies; empty query escape"
        evalTactic rule
        let obligations ← getGoals
        let mut result : AssemblyResult := ⟨[], #[record]⟩
        for obligation in obligations do
          let next ← assemble obligation leaves definitions invariants finish (address ++ ["operation continuation"])
          result := ⟨result.pending ++ next.pending, result.entries ++ next.entries⟩
        return result
      catch _ => pure ()
    saved.restore
  if process.isAppOf ``PIR.repeatN then
    let saved ← saveState
    for invariant in invariants do
      saved.restore
      try
        let record ← capture goal address "structural assembly" "symbolic repeat invariant"
        evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.repeatN _ $invariant))
        let [body, initial] ← getGoals | throwError "unexpected repeat obligations"
        let checked ← assemble body leaves definitions invariants finish (address ++ ["shared repeat body"])
        let entered ← sideObligations [initial] (address ++ ["repeat entry"])
        return ⟨checked.pending ++ entered.pending, #[record] ++ checked.entries ++ entered.entries⟩
      catch _ => pure ()
    saved.restore
    return ← residual goal address "component contract" "missing compatible repeat invariant"
  if process.isAppOf ``PIR.Process.bind then
    let saved ← saveState
    -- The head's intermediate postcondition is inferred from a selected law
    -- or repeat invariant. Never invent it from the requested terminal fact.
    let headRules := leaves ++ (← invariants.mapM fun invariant =>
      `(Zkc.Obligations.Derivation.repeatN _ $invariant))
    for rule in headRules do
      saved.restore
      try
        let record ← capture goal address "structural assembly" "bind at reached history"
        evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.bind))
        let [head, continuation] ← derivationGoals | throwError "unexpected bind obligations"
        let proof ← Term.elabTerm rule none
        let obligations ← withReducible <| head.apply proof
        let mut headResult : AssemblyResult := ⟨[], #[← capture head (address ++ ["head"])
          "installed component" "installed law or repeat invariant"]⟩
        for obligation in obligations do
          let ty ← instantiateMVars (← obligation.getType)
          let next ← if (← forallTelescope ty fun _ body => pure (body.isAppOf ``Zkc.Obligations.Derivation)) then
              assemble obligation leaves definitions invariants finish (address ++ ["shared repeat body"])
            else sideObligations [obligation] (address ++ ["head premise"])
          headResult := ⟨headResult.pending ++ next.pending, headResult.entries ++ next.entries⟩
        let tailResult ← assemble continuation leaves definitions invariants finish (address ++ ["continuation"])
        return ⟨headResult.pending ++ tailResult.pending,
          #[record] ++ headResult.entries ++ tailResult.entries⟩
      catch _ => pure ()
    saved.restore
    try
      let record ← capture goal address "structural assembly" "unrestricted prefix; universal suffix"
      evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.bind))
      let [head, continuation] ← derivationGoals | throwError "unexpected bind obligations"
      setGoals [head]
      evalTactic (← `(tactic| exact ZkcSecurity.Obligations.unrestricted _ _))
      let suffix ← assemble continuation leaves definitions invariants finish (address ++ ["universal continuation"])
      unless suffix.pending.isEmpty do throwError "unrestricted prefix needs a proved universal suffix"
      return ⟨[], #[record] ++ suffix.entries⟩
    catch _ => saved.restore
  return ← residual goal address "component contract" "unsupported component or missing installed law"

elab "assemble_component_property " "[" leaves:term,* "]" " unfolding " "[" definitions:term,* "]"
    " repeating " "[" invariants:term,* "]" " finishing " finish:tactic
    " reporting " association:str " from " source:term : tactic =>
    withMainContext <| Term.withoutErrToSorry <| withoutRecover do
  let goal ← getMainGoal
  let target ← whnf (← instantiateMVars (← goal.getType))
  unless target.isAppOf ``Zkc.Obligations.Derivation do
    throwError "assemble_component_property expects an existing Derivation goal: {target}"
  let source ← Term.elabTerm source none
  let pending := (← getGoals).tail
  let result ← assemble goal leaves.getElems definitions.getElems invariants.getElems finish []
  setGoals (result.pending ++ pending)
  emit association.getString source target result.entries

/-- The default terminal solver has no user tactic to run when an installed
law already discharges the component. An explicit `finishing` clause remains
available for nontrivial terminal mathematics. -/
macro "assemble_component_property " "[" leaves:term,* "]" " unfolding " "[" definitions:term,* "]"
    " repeating " "[" invariants:term,* "]" " reporting " association:str " from " source:term : tactic =>
  `(tactic| assemble_component_property [$leaves,*] unfolding [$definitions,*]
    repeating [$invariants,*] finishing (first | assumption | simp_all)
    reporting $association from $source)

end ZkcSecurity.Tools.ComponentDerivation
