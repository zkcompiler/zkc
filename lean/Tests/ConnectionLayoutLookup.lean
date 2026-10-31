import ZkcTools.ConstructionBindings.LayoutLookup

/-! Focused kernel and transactional refusal controls for finite layout lookup. -/
set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Tests.ConnectionLayoutLookup
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate
open ZkcTools.ConstructionBindings.LayoutLookup

elab "solve_layout_lookup" : tactic => do
  unless ← propose (← getMainGoal) do throwError "layout lookup refused"
  replaceMainGoal []

elab "solve_length_with_operand_hole" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let cells := target.getAppArgs[1]!.getAppArgs.back!
  let values := cells.getAppArgs.back!
  let hole ← mkFreshExprMVar (← inferType values)
  let expected := target.replace fun expression =>
    if expression == values then some hole else none
  let fact ← mkFreshExprSyntheticOpaqueMVar expected
  unless ← proposeLengthEquality fact.mvarId! do throwError "size equation refused"
  if ← hole.mvarId!.isAssigned then throwError "size proof guessed the cell values"
  hole.mvarId!.assign values
  goal.assign fact
  replaceMainGoal []

-- Even an entirely unknown typed row has a fixed number of cells. The size
-- proposer must neither inspect nor invent the operand values.
theorem unknownRowLength {scope : Scope} (values : Values (Comp [] scope) [.index, .boolean]) :
    (ConnectionComputation.cells values).length = 2 := by
  solve_length_with_operand_hole

elab "solve_layout_length" : tactic => do
  unless ← proposeLengthEquality (← getMainGoal) do throwError "size equation refused"
  replaceMainGoal []

-- A wrong offset is refused even in a contradictory ambient proof context:
-- the finite arithmetic solver does not use semantic caller hypotheses.
example {scope : Scope} (values : Values (Comp [] scope) [.index, .boolean])
    (impossible : False) : (ConnectionComputation.cells values).length = 3 := by
  fail_if_success solve_layout_length
  exact impossible.elim

-- Create the equation metavariable directly so `refine` cannot discharge it
-- through elaborator conversion before the proposer gets to infer the hole.
elab "infer_layout_operand" : tactic => withMainContext do
  let goal ← getMainGoal
  let mut target ← goal.getType
  let mut fields : Array (Expr × Expr × Expr) := #[]
  while target.isAppOf ``Exists do
    let args := target.getAppArgs
    let operand ← mkFreshExprMVar args[0]!
    fields := fields.push (args[0]!, args[1]!, operand)
    target := (mkApp args[1]! operand).headBeta
  if fields.isEmpty then throwError "expected an existential lookup"
  let fact ← mkFreshExprSyntheticOpaqueMVar target
  unless ← propose fact.mvarId! do throwError "lookup did not infer the typed operand"
  let mut proof := fact
  for (type, predicate, operand) in fields.reverse do
    unless ← operand.mvarId!.isAssigned do throwError "lookup left its operand unassigned"
    proof ← mkAppOptM ``Exists.intro #[some type, some predicate, some operand, some proof]
  goal.assign proof
  replaceMainGoal []

theorem appended {scope : Scope} (caller : Layout scope) (cell : Cell scope) :
    (caller ++ [cell])[caller.length]? = some cell := by
  solve_layout_lookup

private def closedPrefix : Layout [] := [.unused, .unused]

theorem closedPrefixLiteral (cell : Cell []) :
    (closedPrefix ++ [cell])[2]? = some cell := by
  solve_layout_lookup

theorem suffixOffset {scope : Scope} (caller : Layout scope) (a b : Cell scope) :
    (caller ++ [a, b])[1 + caller.length]? = some b := by
  solve_layout_lookup

theorem mapSet {scope : Scope} (caller : Layout scope) (a b : Cell scope) :
    (((caller ++ [a, .unused]).set (caller.length + 1) b).map Cell.retireHistory)[caller.length]? =
      some (Cell.retireHistory a) := by
  solve_layout_lookup

theorem setSelf {scope : Scope} (caller : Layout scope) (a b : Cell scope) :
    ((caller ++ [a]).set caller.length b)[caller.length]? = some b := by
  solve_layout_lookup

theorem appendLeft {scope : Scope} (caller : Layout scope) (a b : Cell scope) :
    ((caller ++ [a]) ++ [b])[caller.length]? = some a := by
  solve_layout_lookup

theorem received {scope : Scope} (caller : Layout scope) (ty : Ty) :
    (receiveLayout caller ty)[caller.length]? = some (.data (.present (.var .here))) := by
  solve_layout_lookup

theorem receivedAgain {scope : Scope} (caller : Layout scope) (a b : Ty) :
    (receiveLayout (receiveLayout caller a) b)[caller.length + 1]? =
      some (.data (.present (.var .here))) := by
  solve_layout_lookup

theorem previousReceive {scope : Scope} (caller : Layout scope) (a b : Ty) :
    (receiveLayout (receiveLayout caller a) b)[caller.length]? =
      some (.data (.present (.var (.there .here)))) := by
  solve_layout_lookup

theorem guardRefined {scope : Scope} (caller : Layout scope) (condition : NormalForm.Term [] scope .boolean)
    (read : Readback (caller ++ [.data (.present condition)])
      (.cons (.present condition) .nil) [.data caller.length]) :
    (GuardReadback.boolean condition caller.length read).refine[caller.length]? =
      some (.guarded (.present condition)) := by
  solve_layout_lookup

theorem receiveAfterGuard {scope : Scope} (caller : Layout scope) (condition : NormalForm.Term [] scope .boolean)
    (reference : Nat) (guard : GuardReadback caller .boolean condition (.bool true) reference) (ty : Ty) :
    (receiveLayout guard.refine ty)[caller.length]? = some (.data (.present (.var .here))) := by
  solve_layout_lookup

theorem observedHistory {scope : Scope} (caller : Layout scope) (suite : String) :
    (observedLayout caller suite)[caller.length]? = some (.history suite) := by
  solve_layout_lookup

theorem queryHistory {scope : Scope} (caller : Layout scope) (field suite : String) :
    (queryLayout caller field suite)[caller.length + 1]? = some (.history suite) := by
  solve_layout_lookup

theorem deliveryHistory {scope : Scope} (caller : Layout scope) (field suite : String) :
    (deliveryLayout caller field suite)[caller.length + 2]? = some (.history suite) := by
  solve_layout_lookup

theorem actionLengths {scope : Scope} (caller : Layout scope) (field suite : String) (ty : Ty) :
    (receiveLayout (observedReceiveLayout (deliveryLayout caller field suite) ty suite) ty)[caller.length + 5]? =
      some (.data (.present (.var .here))) := by
  solve_layout_lookup

theorem tupleCell {scope : Scope} (caller : Layout scope) :
    (ConnectionComputation.tupleLayout caller [.index])[caller.length]? =
      some (.data (.read .here .here)) := by
  solve_layout_lookup

theorem repeatFresh {scope : Scope} (caller : Layout scope) (context : Zkc.Construction.Context) (types : List Ty) :
    (repeatLayout context caller types)[caller.length]? = some (.data (.present (.var .here))) := by
  solve_layout_lookup

theorem projectedFresh {scope : Scope} (caller : Layout scope) (context : Zkc.Construction.Context) (types : List Ty)
    (role : Nat) (scopes : List (List Nat)) :
    (projectedLayout context role scopes caller types)[caller.length]? = some (.data (.present (.var .here))) := by
  solve_layout_lookup

theorem typedHole {scope : Scope} (caller : Layout scope) (term : NormalForm.Term [] scope .index) :
    ∃ value : NormalForm.Term [] scope .index,
      (caller ++ [.data (.present term)])[caller.length]? = some (.data (.present value)) := by
  infer_layout_operand

theorem coordinateHole {scope : Scope} (caller : Layout scope) (terms : List (NormalForm.Term [] scope .index)) :
    ∃ values : List (NormalForm.Term [] scope .index),
      (caller ++ [.coordinates terms])[caller.length]? = some (.coordinates values) := by
  infer_layout_operand

theorem componentHole {scope : Scope} (caller : Layout scope) (value : Comp [] scope .boolean) :
    ∃ component : Comp [] scope .boolean,
      (caller ++ [.data value])[caller.length]? = some (.data component) := by
  infer_layout_operand

theorem typeAndComponentHoles {scope : Scope} (caller : Layout scope) (term : NormalForm.Term [] scope .index) :
    ∃ ty : Ty, ∃ value : Comp [] scope ty,
      (caller ++ [.data (.present term)])[caller.length]? = some (.data value) := by
  infer_layout_operand

-- An opaque arbitrary caller cannot be enumerated by the proposer. Eight
-- nested suffixes and a concrete offset also exercise association of lengths.
theorem deepOpaque {scope : Scope} (caller : Layout scope) (cell : Cell scope) :
    ((((((((caller ++ [.unused]) ++ [.unused]) ++ [.unused]) ++ [.unused]) ++
      [.unused]) ++ [.unused]) ++ [.unused]) ++ [cell])[caller.length + 7]? = some cell := by
  solve_layout_lookup

private def assertRefused (type : Expr) : MetaM Unit := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let before ← getMCtx
  if ← propose goal.mvarId! then throwError "unexpected layout lookup success"
  let after ← getMCtx
  unless before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.mvarCounter == after.mvarCounter && before.lmvarCounter == after.lmvarCounter &&
      before.decls.toList.map (fun (id, decl) => (id, decl.type)) ==
        after.decls.toList.map (fun (id, decl) => (id, decl.type)) do
    throwError "refused lookup changed metavariables"

-- Fresh unknown determining inputs must neither be assigned nor be decided.
example : True := by
  run_tac do
    let scope ← mkListLit (mkConst ``Slot) []
    let cell ← mkAppOptM ``Cell.unused #[some scope]
    let layout ← mkListLit (← mkAppM ``Cell #[scope]) [cell]
    let index ← mkFreshExprMVar (mkConst ``Nat)
    let lhs ← mkAppM ``GetElem?.getElem? #[layout, index]
    assertRefused (← mkEq lhs (← mkAppM ``Option.some #[cell]))
    unless !(← index.mvarId!.isAssigned) do throwError "unknown index was assigned"
  trivial

-- The determining set index must be fixed even when its underlying cell is known.
example : True := by
  run_tac do
    let scope ← mkListLit (mkConst ``Slot) []
    let cell ← mkAppOptM ``Cell.unused #[some scope]
    let layout ← mkListLit (← mkAppM ``Cell #[scope]) [cell]
    let index ← mkFreshExprMVar (mkConst ``Nat)
    let updated ← mkAppM ``List.set #[layout, index, cell]
    let lhs ← mkAppM ``GetElem?.getElem? #[updated, mkNatLit 0]
    assertRefused (← mkEq lhs (← mkAppM ``Option.some #[cell]))
  trivial

example : True := by
  run_tac do
    let scope ← mkListLit (mkConst ``Slot) []
    let cell ← mkAppOptM ``Cell.unused #[some scope]
    let layout ← mkListLit (← mkAppM ``Cell #[scope]) [cell]
    let other ← mkAppOptM ``Cell.history #[some scope, some (mkStrLit "suite")]
    let lhs ← mkAppM ``GetElem?.getElem? #[layout, mkNatLit 0]
    assertRefused (← mkEq lhs (← mkAppM ``Option.some #[other]))
    let lhs ← mkAppM ``GetElem?.getElem? #[layout, mkNatLit 1]
    assertRefused (← mkEq lhs (← mkAppM ``Option.some #[cell]))
  trivial

-- A selected predecessor operand is not guessed from the requested result.
example : True := by
  run_tac do
    let scope ← mkListLit (mkConst ``Slot) []
    let ty ← mkAppM ``NormalForm.Term #[← mkListLit (mkConst ``LawKey) [], scope, mkConst ``Ty.index]
    let unknown ← mkFreshExprMVar ty
    let cell ← mkAppM ``Cell.data #[← mkAppM ``Comp.present #[unknown]]
    let expected ← mkAppM ``Cell.data #[← mkAppM ``Comp.present #[← mkAppOptM ``NormalForm.Term.index
      #[some (← mkListLit (mkConst ``LawKey) []), some scope, some (mkNatLit 9)]]]
    let layout ← mkListLit (← mkAppM ``Cell #[scope]) [cell]
    let lhs ← mkAppM ``GetElem?.getElem? #[layout, mkNatLit 0]
    assertRefused (← mkEq lhs (← mkAppM ``Option.some #[expected]))
  trivial

-- Refuse unrelated equality, including equality over arbitrary list elements.
example : True := by
  run_tac do
    assertRefused (← mkEq (mkNatLit 3) (mkNatLit 3))
    let layout ← mkListLit (mkConst ``Nat) [mkNatLit 3]
    let lhs ← mkAppM ``GetElem?.getElem? #[layout, mkNatLit 0]
    assertRefused (← mkEq lhs (← mkAppM ``Option.some #[mkNatLit 3]))
  trivial

-- Refusal rolls back an operand assignment made before a later concrete mismatch.
example : True := by
  run_tac do
    let scope ← mkListLit (mkConst ``Slot) []
    let laws ← mkListLit (mkConst ``LawKey) []
    let ty ← mkAppM ``NormalForm.Term #[laws, scope, mkConst ``Ty.index]
    let term := fun n => mkAppOptM ``NormalForm.Term.index #[some laws, some scope, some (mkNatLit n)]
    let hole ← mkFreshExprMVar ty
    let actual ← mkAppM ``Cell.coordinates #[← mkListLit ty [← term 1, ← term 2]]
    let expected ← mkAppM ``Cell.coordinates #[← mkListLit ty [hole, ← term 3]]
    let layout ← mkListLit (← mkAppM ``Cell #[scope]) [actual]
    let lhs ← mkAppM ``GetElem?.getElem? #[layout, mkNatLit 0]
    assertRefused (← mkEq lhs (← mkAppM ``Option.some #[expected]))
  trivial

-- No cache may retain a result across assignments and restored states.
example : True := by
  run_tac do
    let scope ← mkListLit (mkConst ``Slot) []
    let cell ← mkAppOptM ``Cell.unused #[some scope]
    let layout ← mkListLit (← mkAppM ``Cell #[scope]) [cell]
    let index ← mkFreshExprMVar (mkConst ``Nat)
    let saved ← saveState
    index.mvarId!.assign (mkNatLit 0)
    let some selected ← select? layout index | throwError "direct selector refused zero"
    let expected ← mkEq (← mkAppM ``GetElem?.getElem? #[layout, index])
      (← mkAppM ``Option.some #[cell])
    unless ← isDefEq (← inferType selected.proof) expected do throwError "selector proof has wrong type"
    saved.restore
    index.mvarId!.assign (mkNatLit 1)
    unless (← select? layout index).isNone do throwError "selector reused stale zero result"
    unless (← select? layout (mkNatLit 0) (fuel := 0)).isNone do throwError "selector ignored fuel"
  trivial

-- A 1024-cell explicit prefix exceeds the descent/length fuel. A fresh-cell
-- selection must bypass it. Install the returned proof for kernel checking.
run_meta do
  let scope ← mkListLit (mkConst ``Slot) []
  let cellType ← mkAppM ``Cell #[scope]
  let unused ← mkAppOptM ``Cell.unused #[some scope]
  let caller ← mkListLit cellType (List.replicate 1024 unused)
  let fresh ← mkAppOptM ``Cell.history #[some scope, some (mkStrLit "selected")]
  let layout ← mkAppM ``List.append #[caller, ← mkListLit cellType [fresh]]
  let index ← mkAppM ``List.length #[caller]
  let some selected ← select? layout index (fuel := 16)
    | throwError "selector traversed the explicit caller prefix"
  unless ← isDefEq selected.cell fresh do throwError "selector returned the wrong suffix cell"
  let type ← mkEq (← mkAppM ``GetElem?.getElem? #[layout, index]) (← mkAppM ``Option.some #[fresh])
  let proof ← instantiateMVars selected.proof
  addDecl <| .thmDecl {
    name := `Tests.ConnectionLayoutLookup.explicitPrefix
    levelParams := []
    type := type
    value := proof
  }
  logInfo "Explicit prefix control passed: 1024 caller cells, selection fuel 16"

-- A split introduces no instruction that names its internal reference. Infer
-- it from the exact typed cell, rather than an unrelated Nat in the context.
theorem inferredReference (_unrelated : Nat) :
    ∃ index : Nat, ([Cell.unused, .data (.present (.index 9))] : Layout [])[index]? =
      some (.data (.present (.index 9))) := by
  run_tac
    let goal ← getMainGoal
    let type ← goal.getType
    let predicate := type.getAppArgs[1]!
    let index ← mkFreshExprMVar (mkConst ``Nat)
    let fact ← mkFreshExprMVar (mkApp predicate index).headBeta
    unless ← inferIndex fact.mvarId! do throwError "exact cell reference was not inferred"
    goal.assign (← mkAppOptM ``Exists.intro
      #[some (mkConst ``Nat), some predicate, some index, some fact])

-- Opaque frames and unknown expected cells cannot manufacture a reference.
example (_caller : Layout []) : True := by
  run_tac withMainContext do
    let mut candidate : Option Expr := none
    for localDecl in ← getLCtx do
      if localDecl.userName.eraseMacroScopes == `_caller then candidate := some localDecl.toExpr
    let some caller := candidate | throwError "opaque caller is missing from the test context"
    let index ← mkFreshExprMVar (mkConst ``Nat)
    let expected ← mkAppOptM ``Cell.unused #[some (← mkListLit (mkConst ``Slot) [])]
    let fact ← mkFreshExprMVar (← mkEq
      (← mkAppM ``GetElem?.getElem? #[caller, index]) (← mkAppM ``Option.some #[expected]))
    unless !(← inferIndex fact.mvarId!) && !(← index.mvarId!.isAssigned) &&
        !(← fact.mvarId!.isAssigned) do throwError "opaque caller manufactured a reference"
  trivial

example : True := by
  run_tac
    let index ← mkFreshExprMVar (mkConst ``Nat)
    let row ← mkListLit (mkConst ``Nat) [mkNatLit 1]
    let fact ← mkFreshExprMVar (← mkEq
      (← mkAppM ``GetElem?.getElem? #[row, index]) (← mkAppM ``Option.some #[mkNatLit 1]))
    unless !(← inferIndex fact.mvarId!) && !(← index.mvarId!.isAssigned) do
      throwError "reference inference accepted a non-layout"
  trivial

#print axioms inferredReference

#print axioms appended
#print axioms mapSet
#print axioms guardRefined
#print axioms typedHole
#print axioms coordinateHole
#print axioms componentHole
#print axioms typeAndComponentHoles
#print axioms deepOpaque

-- Audit every declaration in both owned namespaces, including anonymous tests.
run_meta do
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (`Tests.ConnectionLayoutLookup).isPrefixOf name ||
        (`Zkc.Construction.ConnectionFrameLookup).isPrefixOf name then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "unexpected axiom in {name}: {axiomName}"
      checked := checked + 1
  logInfo m!"Layout lookup axiom audit passed: {checked} declarations; only standard Lean axioms allowed"

end Tests.ConnectionLayoutLookup
