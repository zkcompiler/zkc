module

public import ZkcSecurity.Bindings.Subjects.ABI
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Kernel-checked structural elaboration for typed subject presentations.
The source printer lives in Generation.SubjectABI and is not a proof dependency. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SubjectABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair

/-- Read the actual admitted ordered selectors. This handles selectors obtained
through retained LetRefs because admission already resolved those references.
Outputs are refused; private inputs remain typed witness coordinates. -/
def selectorPositions {signature : ProtocolSignature} {types : List Ty} :
    Values (BoundarySelector signature) types → Except String (List Nat)
  | .nil => pure []
  | .cons selector rest => do
      let .input ref := selector.port | throw "subject-abi-target-output"
      pure (ref.index :: (← selectorPositions rest))

/-- Structural elimination builds kernel terms, rather than emitting a proof
script specialized to a source's arity. Optional elimination is used solely to
prove exact partial preparation; no arithmetic/formula goal is searched. -/
meta partial def casesValues (options : Bool)
    (finish? : Option (Lean.Elab.Tactic.TacticM Unit) := none) : Lean.Elab.Tactic.TacticM Unit := do
  let goals ← Lean.Elab.Tactic.getGoals
  if goals.isEmpty then return
  if let some finish := finish? then
    let saved ← Lean.Elab.Tactic.saveState
    try
      finish
      if (← Lean.Elab.Tactic.getGoals).isEmpty then return
      saved.restore
    catch _ => saved.restore
  let goal := goals.head!
  let found ← goal.withContext do
    for declaration in ← Lean.getLCtx do
      unless declaration.isImplementationDetail do
        let ty ← Lean.Meta.whnf declaration.type
        if ty.getAppFn.constName? == some ``Values ||
            (options && ty.getAppFn.constName? == some ``Option) then
          return some declaration.fvarId
    return none
  match found with
  | none => pure ()
  | some fvar =>
      let branches ← goal.cases fvar
      let mut results := []
      for branch in branches do
        Lean.Elab.Tactic.setGoals [branch.mvarId]
        casesValues options finish?
        results := results ++ (← Lean.Elab.Tactic.getGoals)
      Lean.Elab.Tactic.setGoals (results ++ goals.tail!)

meta partial def proveExists (target : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let target ← Lean.Meta.whnf target
  if target.isAppOfArity ``Exists 2 then
    let arguments := target.getAppArgs
    let witness ← Lean.Meta.mkFreshExprMVar arguments[0]!
    let proof ← proveExists (Lean.mkApp arguments[1]! witness)
    return ← Lean.Meta.mkAppOptM ``Exists.intro
      #[some arguments[0]!, some arguments[1]!, some witness, some proof]
  let some (_, left, right) := target.eq? | Lean.throwError "expected constructor equality"
  unless ← Lean.Meta.withTransparency .all <| Lean.Meta.isDefEq left right do
    Lean.throwError "ABI constructor is not extensionally the actual typed row"
  return ← Lean.Meta.mkEqRefl left

elab "subject_abi_surjective" : tactic => do
  casesValues false
  for goal in ← Lean.Elab.Tactic.getGoals do
    goal.withContext do
      goal.assign (← proveExists (← goal.getType))
  Lean.Elab.Tactic.setGoals []

/-- Eliminate only typed ABI rows and apply a supplied semantic law. This
constructs ordinary recursor/application terms and never selects a law itself. -/
elab "bind_subject_abi" "using" law:term : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intros))
  casesValues false
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals (apply $law <;> assumption)))

elab "subject_abi_options" : tactic => do
  casesValues false
  casesValues true (some do Lean.Elab.Tactic.evalTactic (← `(tactic| rfl)))
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals first | rfl | simp))


end ZkcSecurity.Tools.SubjectABI
