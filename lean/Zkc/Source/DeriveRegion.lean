module

public import Zkc.Source.DerivationLaws
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Proof-producing traversal of the actual typed source index. Local rules
select operation targets; the tactic never asks for a whole-region equation.
A failed local solver leaves its operation law as an ordinary Lean goal. -/

namespace Zkc.Source
open Lean Meta Elab Tactic

namespace DeriveRegion

private meta def applyRule (goal : MVarId) (rule : Name) : TacticM (List MVarId) :=
  goal.withContext do
    goal.apply (← mkConstWithFreshMVarLevels rule) { newGoals := .nonDependentOnly }

private meta def localLaw (goal : MVarId) (solver : Syntax) : TacticM (List MVarId) := do
  let saved ← saveState
  try
    evalTacticAt solver goal
  catch _ =>
    saved.restore
    pure [goal]

/-- Traverse each structural subtree once. Local targets select the rule;
pending mathematical obligations are retained when reusing the subtree proof. -/
private meta partial def derive (goal : MVarId) (solver : Syntax) : TacticM (List MVarId) :=
  goal.withContext do
    let type ← whnf (← instantiateMVars (← goal.getType))
    if type.isForall then
      let (_, next) ← goal.intro1
      let nextType ← next.withContext <| whnf (← instantiateMVars (← next.getType))
      if nextType.isAppOf ``Region.Derivation then
        let nextArgs := nextType.getAppArgs
        let environment := nextArgs[nextArgs.size - 2]!.eta
        if environment.isAppOf ``Environment.prepend then
          return ← next.withContext do
            let fields := environment.getAppArgs
            -- Fix the split context and operation interpretation before `apply`;
            -- higher-order unification cannot reliably infer them from prepend.
            let rule ← mkAppOptM ``Region.Derivation.prepend_reified
              (#[nextArgs[0]!, nextArgs[1]!, nextArgs[3]!, nextArgs[2]!, nextArgs[4]!,
                 fields[2]!, fields[3]!, nextArgs[6]!, nextArgs[7]!,
                 fields[fields.size - 2]!, fields.back!, nextArgs.back!].map some)
            let .forallE _ premise _ _ ← whnf (← inferType rule)
              | throwError "derive_region: unexpected environment rule shape"
            let normalized ← mkFreshExprMVar premise
            next.assign (mkApp rule normalized)
            derive normalized.mvarId! solver
      return ← derive next solver
    let args := type.getAppArgs
    if type.isAppOf ``Regions.Derivation then
      let source ← whnf args[args.size - 2]!
      if source.isAppOf ``Regions.nil then
        return ← applyRule goal ``Regions.Derivation.nil
      if source.isAppOf ``Regions.cons then
        let [body, tail] ← applyRule goal ``Regions.Derivation.cons
          | throwError "derive_region: unexpected callback rule shape"
        return (← derive body solver) ++ (← derive tail solver)
      return [goal]
    unless type.isAppOf ``Region.Derivation do
      throwError "derive_region expects Region.Derivation, got {type}"
    let source ← whnf args[args.size - 3]!
    if source.isAppOf ``Region.ret then
      return ← applyRule goal ``Region.Derivation.ret
    if source.isAppOf ``Region.stop then
      return ← applyRule goal ``Region.Derivation.stop
    if source.isAppOf ``Region.letOp then
      -- Solve the local law once with a fresh result, then select the structural
      -- rule. Speculating on `.done` first can force expensive semantic reduction.
      let candidateTarget ← mkFreshExprMVar (← inferType args.back!)
      let candidate ← mkFreshExprMVar
        (mkAppN type.getAppFn (args.set! (args.size - 1) candidateTarget))
      let [callbacks, operation, _] ← applyRule candidate.mvarId! ``Region.Derivation.letOp
        | throwError "derive_region: unexpected operation rule shape"
      let pending ← derive callbacks solver
      let obligations ← localLaw operation solver
      let operationType ← instantiateMVars (← operation.getType)
      let step ← whnf operationType.getAppArgs.back!
      let rule := if step.isAppOf ``PIR.Proc.done then ``Region.Derivation.letOpReturn
        else if step.isAppOf ``PIR.Proc.halt then ``Region.Derivation.letOpStop
        else ``Region.Derivation.letOp
      let newGoals ← applyRule goal rule
      let newCallbacks :: newOperation :: rest := newGoals
        | throwError "derive_region: unexpected selected operation rule shape"
      for (fresh, proven) in [(newCallbacks, callbacks), (newOperation, operation)] do
        unless ← isDefEq (← fresh.getType) (← proven.getType) do
          throwError "derive_region: local rule does not match its source occurrence"
        fresh.assign (mkMVar proven)
      match rest with
      | [] => return pending ++ obligations
      | [next] => return pending ++ obligations ++ (← derive next solver)
      | _ => throwError "derive_region: unexpected suffix rule shape"
    if source.isAppOf ``Region.bind then
      let candidateTarget ← mkFreshExprMVar (← inferType args.back!)
      let candidate ← mkFreshExprMVar
        (mkAppN type.getAppFn (args.set! (args.size - 1) candidateTarget))
      let [body, _] ← applyRule candidate.mvarId! ``Region.Derivation.bind
        | throwError "derive_region: unexpected bind rule shape"
      let pending ← derive body solver
      let bodyType ← instantiateMVars (← body.getType)
      let first ← whnf bodyType.getAppArgs.back!
      let rule := if first.isAppOf ``PIR.Proc.done then ``Region.Derivation.bindReturn
        else if first.isAppOf ``PIR.Proc.halt then ``Region.Derivation.bindStop
        else ``Region.Derivation.bind
      let newBody :: rest ← applyRule goal rule
        | throwError "derive_region: unexpected selected bind rule shape"
      unless ← isDefEq (← newBody.getType) (← body.getType) do
        throwError "derive_region: derived body does not match its lexical occurrence"
      newBody.assign (mkMVar body)
      match rest with
      | [] => return pending
      | [next] => return pending ++ (← derive next solver)
      | _ => throwError "derive_region: unexpected bind suffix rule shape"
    -- Abstract bodies remain visible rather than being replaced by an equality.
    pure [goal]

/-- Synthesize the target independently of the expected target. A mismatch is
an error, never an automatically introduced whole-program equality premise. -/
meta def run (solver : Syntax) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let type ← whnf (← instantiateMVars (← goal.getType))
  unless type.isAppOf ``Region.Derivation || type.isAppOf ``Regions.Derivation do
    throwError "derive_region expects a Region.Derivation or Regions.Derivation goal"
  let args := type.getAppArgs
  let target := args.back!
  let generated ← mkFreshExprMVar (← inferType target)
  let proof ← mkFreshExprMVar (mkAppN type.getAppFn (args.set! (args.size - 1) generated))
  let pending ← derive proof.mvarId! solver
  if target.isMVar then
    target.mvarId!.assign (← instantiateMVars generated)
  else unless ← isDefEq generated target do
    throwError "derive_region: generated target does not match the requested target"
  goal.assign (← instantiateMVars proof)
  replaceMainGoal pending

end DeriveRegion

/-- Recursively derive the actual typed region, applying the supplied tactic
only to occurrence-local operation laws. Unproved laws remain explicit goals. -/
syntax (name := deriveRegion) "derive_region" " using " "(" tacticSeq ")" : tactic
elab_rules : tactic
  | `(tactic| derive_region using ($solver:tacticSeq)) => DeriveRegion.run solver

/-- Prove a body's whole process equation `body.denote meaning env = target` by
structural derivation. Each operation occurrence uses the first applicable
supplied local law, or else its own meaning unchanged; the derived process must
be definitionally equal to the stated target. -/
syntax (name := deriveProcess) "derive_process" (" using " "(" tacticSeq ")")? : tactic
macro_rules
  | `(tactic| derive_process) => `(tactic|
      (refine Zkc.Source.Region.Derivation.sound_identity ?_
       derive_region using (apply Zkc.Source.RegionMeaning.OperationLaw.identity; rfl)))
  | `(tactic| derive_process using ($laws:tacticSeq)) => `(tactic|
      (refine Zkc.Source.Region.Derivation.sound_identity ?_
       derive_region using
         (first | ($laws) | (apply Zkc.Source.RegionMeaning.OperationLaw.identity; rfl))))

end Zkc.Source
