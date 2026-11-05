import ZkcTools.ConstructionBindings.Alignment

/-! Finite typed-service premises replayed at reusable-family placements.
The solver must retain the exact request kind, physical shape and nominal context. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionTypedServiceFamilies
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionServiceRequests
open Lean Meta Elab Tactic in
elab "solve_service_interface" : tactic => withMainContext do
  withTransparency .all <|
    ZkcTools.ConstructionBindings.Alignment.solveStructural (← getMainGoal)
  replaceMainGoal []

def drawContext : Context :=
  .fiatShamir "entry" ["P", "V"] 0 1 0 "random.field/0" (some (.draw "field")) "suite" []

def wrongContractContext : Context :=
  .fiatShamir "entry" ["P", "V"] 0 1 0 "random.other/0" (some (.draw "field")) "suite" []

def wrongRequestContext : Context :=
  .fiatShamir "entry" ["P", "V"] 0 1 0 "random.field/0" (some (.sampleIndex 8)) "suite" []

def plainContext : Context := .plain "entry" ["P", "V"] 0 1

def repeatedTemplate : Template := ⟨"entry", [.repeat "entry" "loop"], ["query"]⟩

def drawTarget (context : Context) (template : Template) (state path : Nat) : ServiceBlock :=
  fun _ => Domain.View.challenge context context.suite "field" template state path
    [.data (.field "field"), .transcript context.suite]

def placedDraw {scope : Scope} (layout : Layout scope) (template : Template) (state path : Nat) :
    Challenge layout drawContext template state path (.draw "field" 0)
      (drawTarget drawContext template state path) := by
  solve_service_interface

def placedIndex {scope : Scope} (layout : Layout scope) (context : Context)
    (template : Template) (state path reference bound : Nat)
    (read : layout[reference]? = some (.data (.present (.index bound)))) :
    Challenge layout context template state path (.index "contract" 0 bound)
      (fun _ => Domain.View.indexChallenge context context.suite bound template state reference path
        [.data .index, .transcript context.suite]) := by
  solve_service_interface

def placedIndices {scope : Scope} (layout : Layout scope) (context : Context)
    (template : Template) (state path bound count : Nat) :
    Challenge layout context template state path (.indices "contract" 0 bound count)
      (fun _ => Domain.View.blockChallenge context context.suite bound count template state path
        [.data .indices, .transcript context.suite]) := by
  solve_service_interface

-- Replay the same draw family at different physical offsets and repeat ancestry.
example : Challenge ([.unused, .history "suite"] : Layout []) drawContext repeatedTemplate 1 2
    (.draw "field" 0) (drawTarget drawContext repeatedTemplate 1 2) :=
  placedDraw _ _ _ _

-- The scalar request requires the bound cell; a block request has no such scalar reference.
example : Challenge ([.data (.present (.index 8))] : Layout []) drawContext repeatedTemplate 1 2
    (.index "contract" 0 8)
    (fun _ => Domain.View.indexChallenge drawContext "suite" 8 repeatedTemplate 1 0 2
      [.data .index, .transcript "suite"]) := placedIndex _ _ _ _ _ _ _ rfl

example : Challenge ([] : Layout []) drawContext repeatedTemplate 3 4
    (.indices "contract" 0 8 3)
    (fun _ => Domain.View.blockChallenge drawContext "suite" 8 3 repeatedTemplate 3 4
      [.data .indices, .transcript "suite"]) := placedIndices _ _ _ _ _ _ _

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let mutations ← #[
    -- A draw cannot acquire another suite, field, output row, state or path.
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.draw "field" 0)
      (fun _ => Domain.View.challenge drawContext "other-suite" "field" repeatedTemplate 1 2
        [.data (.field "field"), .transcript "other-suite"])),
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.draw "field" 0)
      (fun _ => Domain.View.challenge drawContext "suite" "other-field" repeatedTemplate 1 2
        [.data (.field "other-field"), .transcript "suite"])),
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.draw "field" 0)
      (fun _ => Domain.View.challenge drawContext "suite" "field" repeatedTemplate 1 2
        [.data (.field "field")])),
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.draw "field" 0)
      (drawTarget drawContext repeatedTemplate 2 1)),
    -- Shape matching cannot discharge nominal, selected-request or mode checks.
    `(Challenge ([] : Layout []) wrongContractContext repeatedTemplate 1 2 (.draw "field" 0)
      (drawTarget wrongContractContext repeatedTemplate 1 2)),
    `(Challenge ([] : Layout []) wrongRequestContext repeatedTemplate 1 2 (.draw "field" 0)
      (drawTarget wrongRequestContext repeatedTemplate 1 2)),
    `(Challenge ([] : Layout []) plainContext repeatedTemplate 1 2 (.draw "field" 0)
      (drawTarget plainContext repeatedTemplate 1 2)),
    -- Matching a result sort does not authorize a different request kind.
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.index "contract" 0 8)
      (drawTarget drawContext repeatedTemplate 1 2)),
    -- The scalar bound has to be read at the actual target reference.
    `(Challenge ([.data (.present (.index 7))] : Layout []) drawContext repeatedTemplate 1 2
      (.index "contract" 0 8)
      (fun _ => Domain.View.indexChallenge drawContext "suite" 8 repeatedTemplate 1 0 2
        [.data .index, .transcript "suite"])),
    -- Block count is part of the fixed request, even when the result sort agrees.
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.indices "contract" 0 8 3)
      (fun _ => Domain.View.blockChallenge drawContext "suite" 8 2 repeatedTemplate 1 2
        [.data .indices, .transcript "suite"])),
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.indices "contract" 0 8 3)
      (fun _ => Domain.View.blockChallenge drawContext "suite" 7 3 repeatedTemplate 1 2
        [.data .indices, .transcript "suite"])),
    -- Repeat ancestry is retained in the exact target template.
    `(Challenge ([] : Layout []) drawContext repeatedTemplate 1 2 (.draw "field" 0)
      (drawTarget drawContext { repeatedTemplate with steps := [] } 1 2))].mapM id
  for mutation in mutations do
    let goal ← mkFreshExprSyntheticOpaqueMVar (← Term.elabType mutation)
    let saved ← saveState
    let refusal ← try
      let _ ← Elab.Tactic.run goal.mvarId! do
        ZkcTools.ConstructionBindings.Alignment.solveStructural goal.mvarId!
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    saved.restore
    unless refusal.any (·.startsWith "alignment-typed-service-shape-or-mode") do
      throwError "malformed typed service did not refuse at its shape boundary: {refusal}"
  logInfo m!"TYPED-SERVICE-REFUSALS {mutations.size}"

#print axioms placedDraw
#print axioms placedIndex
#print axioms placedIndices

-- A family may still have unrelated finite source operands when its target
-- fixes the service references. Checking the shape must leave those operands
-- to their own determining equations, rather than try to synthesize them.
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let laws ← mkListLit (mkConst ``LawKey) []
  let scope ← mkListLit (mkConst ``Slot) []
  let datum ← mkFreshExprMVar (← mkAppOptM ``NormalForm.Term
    #[some laws, some scope, some (mkConst ``Ty.index)])
  let cell ← mkAppM ``Cell.data #[← mkAppM ``Comp.present #[datum]]
  let layout ← mkListLit (← inferType cell) [cell]
  let target ← mkAppM ``drawTarget
    #[mkConst ``drawContext, mkConst ``repeatedTemplate, mkNatLit 1, mkNatLit 2]
  let service ← mkAppM ``Service.draw #[mkStrLit "field", mkNatLit 0]
  let expected ← mkAppM ``Challenge #[layout, mkConst ``drawContext,
    mkConst ``repeatedTemplate, mkNatLit 1, mkNatLit 2, service, target]
  let goal ← mkFreshExprSyntheticOpaqueMVar expected
  let _ ← Elab.Tactic.run goal.mvarId! do
    ZkcTools.ConstructionBindings.Alignment.solveStructural goal.mvarId!
  unless (← goal.mvarId!.isAssigned) && !(← datum.mvarId!.isAssigned) do
    throwError "service-shape-did-not-preserve-unrelated-data"
  datum.mvarId!.assign (← mkAppOptM ``NormalForm.Term.index
    #[some laws, some scope, some (mkNatLit 8)])
  let value ← instantiateMVars goal
  let type ← instantiateMVars expected
  if value.hasMVar || value.hasSorry then throwError "unfinished-open-layout-control"
  let name := `Tests.ConnectionTypedServiceFamilies.checkedOpenLayout
  let declaration ← mkDefinitionValInferringUnsafe name [] type value .abbrev
  withOptions (Elab.async.set · false) <| addDecl (.defnDecl declaration)
  for axiomName in ← collectAxioms name do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected-open-layout-axiom: {axiomName}"
  logInfo m!"TYPED-SERVICE-OPEN-DATA preserved-and-kernel-checked"
end Tests.ConnectionTypedServiceFamilies
