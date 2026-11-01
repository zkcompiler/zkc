import ZkcTools.ConstructionBindings.Readback

/-! Controls for generated readbacks and stale transcript designations. -/
set_option autoImplicit false
namespace Tests.ConnectionFrame
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.ConnectionFrame
open ZkcTools.ConstructionBindings.Readback
open Lean Meta Elab Tactic

abbrev scope : NormalForm.Scope := [.value .boolean, .value .index]
def outputs : Values (NormalForm.Comp [] scope) [.boolean, .index] :=
  .cons (.present (.var .here)) (.cons (.present (.var (.there .here))) .nil)
def layout : Layout scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here))),
    .history "suite", .unused]

def readback : Readback layout outputs [.data 0, .data 1] := by derive_source_readback

-- Location inference remains available when a caller has not fixed the row.
def inferred : Sigma fun locations => Readback layout outputs locations :=
  ⟨_, by derive_source_readback⟩

example : inferred.1 = [.data 0, .data 1] := rfl

example : ¬ (layout.map Cell.retireHistory)[2]? = some (.history "suite") := by
  simp [layout, Cell.retireHistory]

-- A physical location with the wrong source expression cannot be admitted.
example : IsEmpty (Readback layout outputs [.data 1, .data 0]) := by
  constructor
  intro certificate
  cases certificate with
  | guardedOriginal reference checked tail => simp [layout] at checked
  | data reference checked tail =>
    change some (.data (.present (.var (.there .here))) : Cell scope) =
      some (.data (.present (.var .here))) at checked
    cases checked

example (model : DomainModel) (accepted : Bool) (residual : Nat)
    (history : Domain.History model.toCarriers) :
    Original.ValuesHolds (types := [.boolean, .index])
      [.data (.boolean accepted), .data (.index residual), .transcript "suite" history, .indices [1, 2]]
      [.data 0, .data 1]
      (.cons (some accepted) (.cons (some residual) .nil)) := by
  apply readback.sound (model := model)
    (binders := .cons accepted (.cons residual .nil)) (history := history)
  exact .cons ⟨accepted, rfl, rfl⟩ (.cons ⟨residual, rfl, rfl⟩ (.cons rfl (.cons trivial .nil)))

-- History advancement keeps source data facts but does not reinterpret stale bytes.
example (model : DomainModel) (accepted : Bool) (residual : Nat)
    (before after : Domain.History model.toCarriers) :
    Holds model (.cons accepted (.cons residual .nil)) after (layout.map Cell.retireHistory)
      [.data (.boolean accepted), .data (.index residual), .transcript "suite" before, .indices [1, 2]] := by
  apply Holds.retireHistory (history := before)
  exact .cons ⟨accepted, rfl, rfl⟩ (.cons ⟨residual, rfl, rfl⟩ (.cons rfl (.cons trivial .nil)))

-- Family application creates ordinary metavariable operands before readback.
-- Inferring an earlier operand must leave later operand holes for the suffix.
elab "infer_readback_operands" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  let tupleTy ← whnf args[0]!
  let scope := tupleTy.getAppArgs[1]!
  let laws ← mkListLit (mkConst ``NormalForm.LawKey) []
  let head ← mkFreshExprMVar (← mkAppM ``NormalForm.Term #[laws, scope, mkConst ``Ty.boolean])
  let tail ← mkFreshExprMVar (← mkAppM ``NormalForm.Term #[laws, scope, mkConst ``Ty.index])
  let empty ← mkAppOptM ``NormalForm.Terms.nil #[some laws, some scope]
  let tuple ← mkAppM ``NormalForm.Terms.cons #[head, ← mkAppM ``NormalForm.Terms.cons #[tail, empty]]
  let tupleGoal ← mkFreshExprSyntheticOpaqueMVar ((mkApp args[1]! tuple).headBeta)
  setGoals [tupleGoal.mvarId!]
  evalTactic (← `(tactic| derive_source_readback))
  let proof ← mkAppOptM ``Sigma.mk #[some args[0]!, some args[1]!, some tuple, some tupleGoal]
  goal.assign proof
  setGoals []

noncomputable def inferredOperands : Sigma fun terms : NormalForm.Terms [] scope [.boolean, .index] =>
    Readback layout (ConnectionComputation.components terms) [.data 0, .data 1] := by
  infer_readback_operands

noncomputable def inferredReceivedOperands : Sigma fun terms :
    NormalForm.Terms [] (.value .index :: scope) [.boolean, .index] =>
    Readback (ConnectionCertificate.receiveLayout layout .index)
      (ConnectionComputation.components terms) [.data 0, .data 4] := by
  infer_readback_operands

example : inferredOperands.1 =
    .cons (.var .here) (.cons (.var (.there .here)) .nil) := rfl

example : inferredReceivedOperands.1 =
    .cons (.var (.there .here)) (.cons (.var .here) .nil) := rfl

-- Spine reduction does not inspect arbitrary term heads.
example {scope : NormalForm.Scope} {ty : Ty} {types : List Ty}
    (head : NormalForm.Term [] scope ty) (tail : NormalForm.Terms [] scope types) :
    ConnectionComputation.components (.cons head tail) =
      .cons (.present head) (ConnectionComputation.components tail) := rfl

end Tests.ConnectionFrame
