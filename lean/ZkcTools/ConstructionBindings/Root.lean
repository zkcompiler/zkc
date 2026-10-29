module

public import ZkcTools.ConstructionBindings.LibraryBuilder
public import Zkc.Construction.ConnectionRootInputs
public import Zkc.Construction.ConnectionRootCertificate
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
  -- Input certificates repeatedly inspect these finite indices. Normalize
  -- them once, including projections out of a modified actual artifact, so
  -- a refused candidate cannot force the whole input proposal to reduce the
  -- same artifact expression at every constructor. Ordinary definitional
  -- equality still checks the normalized goal against its original indices.
  let cache ← Syntax.newCache
  let signature ← Syntax.normalize cache args[0]!
  let context ← Syntax.normalize cache args[1]!
  let role ← Syntax.normalize cache args[2]!
  let sorts ← Syntax.normalize cache args[3]!
  goal.setType (mkAppN expected.getAppFn #[signature, context, role, sorts])
  Alignment.tracePhase "root input indices normalized"
  let candidate ← mkAppM ``ConnectionRootInputs.locations #[signature, role, capabilities]
  let result ← withTransparency .all <| whnf candidate
  unless result.isAppOf ``Except.ok do throwError "root-input-proposal-refused: {result}"
  let locations := result.getAppArgs.back!
  let types ← mkAppM ``ProtocolSignature.inputs #[signature]
  let pattern ← mkFreshExprMVar (← mkAppM ``NormalForm.InputPattern #[types])
  let shape ← mkFreshExprMVar (← mkAppM ``ConnectionInputs.Shape #[pattern, locations])
  setGoals [shape.mvarId!]
  evalTactic (← `(tactic| derive_connection_inputs))
  Alignment.tracePhase "root input shape checked"
  let pattern ← instantiateMVars pattern
  let shape ← instantiateMVars shape
  let suite ← mkAppM ``Context.suite #[context]
  let history ← mkAppM ``ConnectionInputs.historySlot #[context, sorts]
  let layout ← mkAppM ``ConnectionRootInputs.layout #[pattern, locations, suite, history, sorts]
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
  Alignment.tracePhase "root input cells checked"
  for (label, next) in [("sorts", sortedGoal), ("visibility", visibleGoal),
      ("length", lengthGoal), ("history", historyGoal)] do
    Alignment.tracePhase s!"root input finite {label}"
    finite next

private def deriveRoot (target correspondence services : Syntax)
    (selectedLibrary : Option Syntax) : TacticM Unit := withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    Alignment.tracePhase "root start"
    let goal ← getMainGoal
    let remaining := (← getGoals).tail
    let expected ← instantiateMVars (← goal.getType)
    unless expected.isAppOf ``ConnectionRoot.RootCertificate do
      throwError "expected a RootCertificate for an actual source and constructed artifact"
    let mut args := expected.getAppArgs
    -- Freeze the finite role before it becomes an index of every derivation
    -- node. The generated type can name a projection of the checked context;
    -- keep this computation out of the repeated role indices.
    let role ← withTransparency .all <| whnf args[2]!
    args := args.set! 2 role
    goal.setType (mkAppN expected.getAppFn args)
    let target ← Term.elabTerm target (some (mkConst ``ConnectionCertificate.Block))
    let correspondenceType ← withLocalDeclD `model (mkConst ``DomainModel) fun model => do
      let context ← mkAppM ``Original.Routing.context #[args[1]!]
      let instructions ← mkAppM ``Participant.instructions #[args[3]!]
      let conclusion ← mkAppOptM ``Domain.Correspondence.Block
        #[some model, some args[0]!, some context, some instructions, some (mkApp target model)]
      mkForallFVars #[model] conclusion
    let correspondence ← Term.elabTerm correspondence (some correspondenceType)
    let capabilities ← Term.elabTerm services (some (← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]]))
    let [libraryGoal, snapshotGoal, roleGoal, distinctGoal, inputGoal, outputGoal,
        targetGoal, correspondenceGoal, alignmentGoal] ←
        goal.apply (← mkConstWithFreshMVarLevels ``ConnectionRoot.RootCertificate.mk) { newGoals := .all }
      | throwError "root-certificate-shape"
    let libraryType ← libraryGoal.getType
    let library ← match selectedLibrary with
      | some selectionSyntax => Term.elabTerm selectionSyntax (some libraryType)
      | none => mkAppM ``ConnectionLibrary.Bundle.empty #[← mkAppM ``Program.payload #[args[0]!]]
    libraryGoal.assign library
    targetGoal.assign target
    correspondenceGoal.assign correspondence
    let pending := [snapshotGoal, roleGoal, distinctGoal, inputGoal, outputGoal, alignmentGoal]
    for next in pending do
      Alignment.tracePhase s!"root finite {(← next.getType).getAppFn.constName?}"
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
    Alignment.tracePhase "root proposal complete"
    setGoals remaining

elab "derive_root_connection" &"target" target:term:max
    &"correspondence" correspondence:term:max &"services" services:term : tactic =>
  deriveRoot target correspondence services none

elab "derive_root_connection_with_library" &"target" target:term:max
    &"correspondence" correspondence:term:max &"services" services:term:max
    &"library" selectedLibrary:term : tactic =>
  deriveRoot target correspondence services (some selectedLibrary)

end ZkcTools.ConstructionBindings.Root
