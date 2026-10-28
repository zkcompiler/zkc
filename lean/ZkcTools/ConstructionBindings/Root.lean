module

public import ZkcTools.ConstructionBindings.RootData
public import ZkcTools.ConstructionBindings.Inputs
public import ZkcTools.ConstructionBindings.Alignment
public meta import Lean.Elab.Tactic

public meta section

/-! One untrusted root proposer. Source roles and scopes, an explicit capability
association and the generated constructed view determine its finite obligations.
The kernel checks every field; failure does not weaken the connection meaning.
-/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Root
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private def finite (goal : MVarId) : TacticM Unit := do
  setGoals [goal]
  evalTactic (← `(tactic| first | rfl | decide +kernel))

private def input (goal : MVarId) (capabilities : Expr) : TacticM Unit := goal.withContext do
  let expected ← instantiateMVars (← goal.getType)
  let args := expected.getAppArgs
  let signature := args[0]!
  let context := args[1]!
  let role := args[2]!
  let sorts := args[3]!
  let candidate ← mkAppM ``RootData.locations #[signature, role, capabilities]
  let result ← withTransparency .all <| whnf candidate
  unless result.isAppOf ``Except.ok do throwError "root-input-proposal-refused: {result}"
  let locations := result.getAppArgs.back!
  let types ← mkAppM ``ProtocolSignature.inputs #[signature]
  let pattern ← mkFreshExprMVar (← mkAppM ``NormalForm.InputPattern #[types])
  let shape ← mkFreshExprMVar (← mkAppM ``ConnectionInputs.Shape #[pattern, locations])
  setGoals [shape.mvarId!]
  evalTactic (← `(tactic| derive_connection_inputs))
  let pattern ← instantiateMVars pattern
  let shape ← instantiateMVars shape
  let suite ← mkAppM ``Context.suite #[context]
  let history ← mkAppM ``ConnectionInputs.historySlot #[context, sorts]
  let layout ← mkAppM ``RootData.layout #[pattern, locations, suite, history, sorts]
  let [locationsGoal, patternGoal, shapeGoal, sortedGoal, visibleGoal,
      layoutGoal, cellsGoal, lengthGoal, historyGoal] ←
      goal.apply (← mkConstWithFreshMVarLevels ``ConnectionInputs.InputLayout.mk) { newGoals := .all }
    | throwError "root-input-certificate-shape"
  locationsGoal.assign locations
  patternGoal.assign pattern
  shapeGoal.assign shape
  layoutGoal.assign layout
  setGoals [cellsGoal]
  evalTactic (← `(tactic| derive_connection_inputs))
  for next in [sortedGoal, visibleGoal, lengthGoal, historyGoal] do finite next

elab "derive_root_connection" &"target" target:term:max
    &"correspondence" correspondence:term:max &"services" services:term : tactic => withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    let goal ← getMainGoal
    let remaining := (← getGoals).tail
    let expected ← instantiateMVars (← goal.getType)
    unless expected.isAppOf ``ConnectionRoot.RootCertificate do
      throwError "expected a RootCertificate for an actual source and constructed artifact"
    let args := expected.getAppArgs
    let target ← Term.elabTerm target (some (mkConst ``ConnectionCertificate.Block))
    let correspondenceType ← withLocalDeclD `model (mkConst ``DomainModel) fun model => do
      let context ← mkAppM ``Original.Routing.context #[args[1]!]
      let instructions ← mkAppM ``Participant.instructions #[args[3]!]
      let conclusion ← mkAppOptM ``Domain.Correspondence.Block
        #[some model, some args[0]!, some context, some instructions, some (mkApp target model)]
      mkForallFVars #[model] conclusion
    let correspondence ← Term.elabTerm correspondence (some correspondenceType)
    let capabilities ← Term.elabTerm services (some (← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]]))
    let [snapshotGoal, roleGoal, distinctGoal, inputGoal, outputGoal,
        targetGoal, correspondenceGoal, alignmentGoal] ←
        goal.apply (← mkConstWithFreshMVarLevels ``ConnectionRoot.RootCertificate.mk) { newGoals := .all }
      | throwError "root-certificate-shape"
    targetGoal.assign target
    correspondenceGoal.assign correspondence
    let pending := [snapshotGoal, roleGoal, distinctGoal, inputGoal, outputGoal, alignmentGoal]
    for next in pending do
      let type ← instantiateMVars (← next.getType)
      if type.isAppOf ``ConnectionInputs.InputLayout then input next capabilities
      else if type.isAppOf ``ConnectionInstallation.ReturnLayout then
        setGoals [next]
        evalTactic (← `(tactic| exact
          (Zkc.Construction.ConnectionInstallation.ReturnLayout.build _ _ _ _).toOption.get (by decide +kernel)))
      else if type.isAppOf ``NormalForm.RosterDistinct then
        setGoals [next]
        evalTactic (← `(tactic| exact Zkc.Source.Structured.NormalForm.RosterDistinct.root _ _))
      else if type.isAppOf ``ConnectionCertificate.Certificate then
        setGoals [next]
        evalTactic (← `(tactic| derive_connection_alignment))
      else finite next
    setGoals remaining

end ZkcTools.ConstructionBindings.Root
