import ZkcTools.ConstructionBindings.Alignment

/-! The generated interface may expose finite operands and checked readbacks,
but container wrappers must not admit functions or propositions as data. -/
open Lean Meta Elab Command Term
open ZkcTools.ConstructionBindings.Interface
open Zkc.Source Zkc.Source.Structured

run_cmd liftTermElabM do
  for (typeSyntax, expected) in [
      (← `(Nat), true),
      (← `(List (Option Nat)), true),
      (← `(Nat × Bool), true),
      (← `(Option (List Zkc.Construction.ValueSort)), true),
      (← `(Except String (NormalForm.Form [] [] [] [.index])), true),
      (← `(Except String Prop), false),
      (← `(NormalForm.Comp [] [] .index), true),
      (← `(Values (NormalForm.Comp [] []) [.index, .boolean]), true),
      (← `(Values (fun _ : Ty => Nat) [.index]), true),
      (← `(Nat → Nat), false),
      (← `(Prop), false),
      (← `(List Prop), false),
      (← `(Option (Nat → Nat)), false),
      (← `(Values (fun _ : Ty => Prop) [.index]), false),
      (← `(NormalForm.Form [] [] [] [.index]), true)] do
    let type ← elabType typeSyntax
    unless (← finiteData type) == expected do throwError "unexpected finite interface: {type}"
  for (typeSyntax, expected) in [
      (← `(0 = (0 : Nat)), true),
      (← `(([0] : List Nat) = [0]), true),
      (← `(True = False), false),
      (← `((fun n : Nat => n) = (fun n => n)), false),
      (← `(([] : List Prop) = []), false)] do
    let type ← elabType typeSyntax
    unless (← structural type) == expected do throwError "unexpected structural interface: {type}"

-- An interface data hole must not be filled from an unrelated local of the
-- same type. These are exactly the sorts shared by loop boundaries and roots.
set_option linter.unusedTactic false in
example (_unrelatedReference : Nat)
    (_unrelatedOutputs : List Zkc.Construction.Original.Location)
    (_unrelatedHistory : Option Nat) : True := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut decoys := 0
    for localDecl in ← getLCtx do
      if [`_unrelatedReference, `_unrelatedOutputs, `_unrelatedHistory].contains
          localDecl.userName.eraseMacroScopes then decoys := decoys + 1
    unless decoys == 3 do Lean.throwError "same-typed decoys are missing from the test context"
    for typeSyntax in [← `(Nat), ← `(List Zkc.Construction.Original.Location), ← `(Option Nat)] do
      let type ← Lean.Elab.Term.elabType typeSyntax
      let hole ← Lean.Meta.mkFreshExprMVar type
      withOptions (·.setBool `zkc.connection.collectFamilyPremises true) do
        ZkcTools.ConstructionBindings.Alignment.solveStructural hole.mvarId!
      if ← hole.mvarId!.isAssigned then
        Lean.throwError "family data was guessed from an unrelated local"
  trivial

open Zkc.Construction ConnectionFrame ConnectionCertificate

-- An unresolved guard changes a predecessor cell, but neither the appended
-- transcript position nor its suite. Solving that position must leave the
-- guard certificate for its own determining interface fact.
elab "read_history_without_guard" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let guard ← getFVarFromUserName `guard
  let hole ← mkFreshExprMVar (← inferType guard)
  let expected := (← goal.getType).replace fun expression =>
    if expression == guard then some hole else none
  let certificate ← mkFreshExprSyntheticOpaqueMVar expected
  ZkcTools.ConstructionBindings.Alignment.solveStructural certificate.mvarId!
  if ← hole.mvarId!.isAssigned then throwError "history lookup guessed its predecessor guard"
  hole.mvarId!.assign guard
  goal.assign certificate
  Lean.Elab.Tactic.replaceMainGoal []

noncomputable def historyAfterUnresolvedGuard {scope : NormalForm.Scope}
    (layout : Layout scope) (condition : NormalForm.Term [] scope .boolean)
    (reference : Nat) (guard : GuardReadback layout .boolean condition (.bool true) reference)
    (suite : String) :
    HistoryReadback (observedLayout guard.refine suite) suite (some layout.length) := by
  read_history_without_guard

elab "solve_finite_interface" : tactic => Lean.Elab.Tactic.withMainContext do
  ZkcTools.ConstructionBindings.Alignment.solveStructural (← Lean.Elab.Tactic.getMainGoal)
  Lean.Elab.Tactic.replaceMainGoal []

set_option linter.unusedTactic false in
example (impossible : False) : HistoryReadback ([.unused, .history "suite"] : Layout [])
    "suite" (some 0) := by
  fail_if_success solve_finite_interface
  exact impossible.elim

-- Source syntax fixes an optional subject through its component projection.
-- This is finite constructor inference, followed by checking the whole equation.
elab "infer_split_subject" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← goal.getType
  unless target.isAppOf ``Exists do throwError "expected a subject witness"
  let args := target.getAppArgs
  let subject ← mkFreshExprMVar args[0]!
  let fact ← mkFreshExprSyntheticOpaqueMVar ((mkApp args[1]! subject).headBeta)
  unless ← ZkcTools.ConstructionBindings.StructuralFacts.proposeSourceEquality fact.mvarId! do
    throwError "source subject was not determined"
  if (← instantiateMVars subject).hasExprMVar then throwError "unresolved subject"
  goal.assign (← mkAppOptM ``Exists.intro #[some args[0]!, some args[1]!, some subject, some fact])
  Lean.Elab.Tactic.replaceMainGoal []

example : ∃ subject : NormalForm.Subject [.component .index] .index,
    (NormalForm.Form.split (NormalForm.Subject.comp subject) (.halt .incomplete) (.halt .incomplete) :
      NormalForm.Form [] [] [.component .index] []) =
    NormalForm.Form.split (.input .here) (.halt .incomplete) (.halt .incomplete) := by
  infer_split_subject

example : ∃ subject : NormalForm.Subject [.tuple [.index, .boolean]] .boolean,
    (NormalForm.Form.split (NormalForm.Subject.comp subject) (.halt .incomplete) (.halt .incomplete) :
      NormalForm.Form [] [] [.tuple [.index, .boolean]] []) =
    NormalForm.Form.split (.read .here (.there .here)) (.halt .incomplete) (.halt .incomplete) := by
  infer_split_subject

set_option linter.unusedTactic false in
example (impossible : False) : ∃ subject : NormalForm.Subject [.component .index] .index,
    (NormalForm.Form.split (NormalForm.Subject.comp subject) (.halt .incomplete) (.halt .incomplete) :
      NormalForm.Form [] [] [.component .index] []) =
    NormalForm.Form.split (.present (.index 0)) (.halt .incomplete) (.halt .incomplete) := by
  fail_if_success infer_split_subject
  exact impossible.elim

-- Discovery keeps a source equation in the family interface. The use-site
-- solver can then infer its subject against the fixed source computation.
set_option linter.unusedTactic false in
example : True := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← elabType (← `(∃ subject : NormalForm.Subject [.component .index] .index,
      (NormalForm.Form.split (NormalForm.Subject.comp subject) (.halt .incomplete) (.halt .incomplete) :
        NormalForm.Form [] [] [.component .index] []) =
      NormalForm.Form.split (.input .here) (.halt .incomplete) (.halt .incomplete)))
    let args := target.getAppArgs
    let subject ← mkFreshExprMVar args[0]!
    let fact ← mkFreshExprSyntheticOpaqueMVar ((mkApp args[1]! subject).headBeta)
    withOptions (·.setBool `zkc.connection.collectFamilyPremises true) do
      ZkcTools.ConstructionBindings.Alignment.solveStructural fact.mvarId!
    if (← subject.mvarId!.isAssigned) || (← fact.mvarId!.isAssigned) then
      throwError "family discovery specialized an open source equation"
    ZkcTools.ConstructionBindings.Alignment.solveStructural fact.mvarId!
    unless (← subject.mvarId!.isAssigned) && (← fact.mvarId!.isAssigned) do
      throwError "application did not discharge the deferred source equation"
  trivial

-- Constructor inference may skip closed subtrees, but final conversion must
-- still reject a different stopping outcome after inferring the subject.
set_option linter.unusedTactic false in
example (impossible : False) : ∃ subject : NormalForm.Subject [.component .index] .index,
    (NormalForm.Form.split (NormalForm.Subject.comp subject) (.halt .incomplete) (.halt .incomplete) :
      NormalForm.Form [] [] [.component .index] []) =
    NormalForm.Form.split (.input .here) (.halt .reject) (.halt .incomplete) := by
  fail_if_success infer_split_subject
  exact impossible.elim

-- A profile inversion can determine the data row before discovering a bad
-- history policy. Refusing it must restore that row and the proof goal.
run_cmd liftTermElabM do
  let context ← elabTerm (← `(Context.plain "entry" ["P", "V"] 0 1)) none
  let data ← mkFreshExprMVar (← mkAppM ``List #[mkConst ``Nat])
  let history ← mkAppM ``Option.some #[mkNatLit 0]
  let projected ← mkAppM ``Original.profileReferences #[context, data, history]
  let result ← mkAppM ``Option.some #[← mkListLit (mkConst ``Nat) [mkNatLit 7]]
  let rejected ← mkFreshExprSyntheticOpaqueMVar (← mkEq projected result)
  if ← ZkcTools.ConstructionBindings.StructuralFacts.propose rejected.mvarId! then
    throwError "plain profile accepted a transcript slot"
  if (← data.mvarId!.isAssigned) || (← rejected.mvarId!.isAssigned) then
    throwError "refused profile inversion changed metavariable state"
  let projected ← mkAppM ``Original.profileReferences
    #[context, data, ← mkAppOptM ``Option.none #[some (mkConst ``Nat)]]
  let accepted ← mkFreshExprSyntheticOpaqueMVar (← mkEq projected result)
  unless ← ZkcTools.ConstructionBindings.StructuralFacts.propose accepted.mvarId! do
    throwError "valid plain profile did not infer its data row"
  unless ← isDefEq data (← mkListLit (mkConst ``Nat) [mkNatLit 7]) do
    throwError "profile inversion inferred the wrong data row"
