import Zkc.Tests.IR.ConnectionTypedServiceFamilies
import Zkc.IR.Source.Structured.UnitViews
import Zkc.Tools.IR.ConstructionBindings.Root

/-! A tiny actual source entry generates one reusable typed-service body.
Two different caller prefixes must replay that same family, with exact source identity. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionTypedServiceInstallation
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionTargetPlacement
open Tests.ConnectionTypedServiceFamilies

abbrev field := "bls12-381.fr"
abbrev contract := "random.bls12-381.fr/0"
def querySignature : ProtocolSignature := ⟨"query", ["P", "V"], [.service contract], [], [[1]], []⟩
def queryBody : Region protocolDialect [.service contract] [] :=
  .letOp (.mark "q") .nil .nil <|
  .letOp (.draw 1 field "q") (.cons .here .nil) .nil <| .ret .nil

def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "query"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"query", .protocol, .publicDef, [.service contract], [],
    some ⟨["P", "V"], [["V"]], []⟩, [], some (.protocol ⟨"query", []⟩),
    .block [.instruction (.draw "V" field) [0] [.field field] [] "q"] (.ret [])⟩]
  contracts := [⟨"query", []⟩]
  catalogue := blsCatalogue

structured_views snapshot helpers [] protocols [query]
example : Structured.check snapshot = .ok program := kernel_admission

def pattern : InputPattern [.service contract] := .cons (.capability contract 0) .nil
def sourceTemplate : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 1 pattern).toOption.get
    (by decide +kernel)
def entry : Entry program.payload sourceTemplate.key := ⟨[], .empty, sourceTemplate, rfl⟩
def context : Context := .fiatShamir "query" ["P", "V"] 0 1 0 contract
  (some (.draw field)) "suite" []
def template : Template := ⟨"query", [], ["query", "query", "q", "input_0", contract, "draw", "V"]⟩
def routing : Original.Routing := ⟨snapshot, context, .validator, 0, [], [template], [], []⟩

def placement (padding : Nat) : Placement sourceTemplate.key where
  context := {}
  scope := []
  arguments := .nil
  frames := []
  -- Both coordinate cells admit the same readback. The target uses the last
  -- one, so finding the first matching cell cannot determine its reference.
  layout := List.replicate padding .unused ++
    [.coordinates [], .history "suite", .coordinates []]
  outputs := []
  history := some (padding + 4)
  returns := .nil
  spine := .step (fun _ => Domain.View.challenge context "suite" field template
    (padding + 1) (padding + 2)
    [.data (.field field), .transcript "suite"]) .empty
  extent := padding + 5

def discovery : CheckedBody entry routing .unselected (placement 0) := by
  derive_connection_target_body

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let body ← mkAppM ``CheckedBody.alignment #[mkConst ``discovery]
  let selection := (← inferType body).getAppArgs[4]!
  let goal ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let _ ← Elab.Tactic.run goal.mvarId! do
    let _ ← ZkcTools.ConstructionBindings.Alignment.installDiscoveredBody
      (mkConst ``entry) (mkConst ``routing) selection
      (mkApp (mkConst ``placement) (mkNatLit 0)) body
    pure ()

open Lean Meta Elab Tactic in
elab "reuse_service_family" : tactic => withMainContext do
  let goal ← getMainGoal
  let expected ← whnf (← goal.getType)
  let bodyGoal ← mkFreshExprSyntheticOpaqueMVar expected
  let alignment ← mkAppM ``CheckedBody.alignment #[bodyGoal]
  let alignmentGoal ← mkFreshExprSyntheticOpaqueMVar (← inferType alignment)
  let args := expected.getAppArgs
  let some used ← ZkcTools.ConstructionBindings.TargetPlacement.propose alignmentGoal.mvarId!
    args[2]! args[5]! ZkcTools.ConstructionBindings.Alignment.solveStructural
    | throwError "test-service-family-refused"
  goal.assign used.body
  setGoals []

def first : CheckedBody entry routing .unselected (placement 0) := by reuse_service_family
def second : CheckedBody entry routing .unselected (placement 3) := by reuse_service_family

def otherTemplate : SourceTemplate program.payload [] := { sourceTemplate with pins := [some 0] }
def otherEntry : Entry program.payload otherTemplate.key := ⟨[], .empty, otherTemplate, rfl⟩
def otherPlacement : Placement otherTemplate.key := ⟨{}, [], .nil, [],
  (placement 0).layout, [], (placement 0).history, .nil, (placement 0).spine, 5⟩
def malformedPlacement : Placement sourceTemplate.key := { placement 0 with
  spine := .step (fun _ => Domain.View.challenge context "other-suite" field template 1 2
    [.data (.field field), .transcript "other-suite"]) .empty }

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let first := (← getConstInfo ``first).value!
  let second := (← getConstInfo ``second).value!
  let families := ZkcTools.ConstructionBindings.TargetPlacement.checkedBodies.getState (← getEnv)
  unless families.size == 1 && first.getAppFn == second.getAppFn &&
      families.contains first.getAppFn.constName! do
    throwError "test-service-family-was-not-reused"
  let family := first.getAppFn.constName!
  let info ← getConstInfo family
  ZkcTools.ConstructionBindings.Interface.auditFamilyType info.type
  if info.value!.hasSorry || info.value!.hasMVar then throwError "unfinished-service-family"
  for name in [family, ``discovery, ``first, ``second] do
    for axiomName in ← collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected service-family axiom: {axiomName}"
  for mutation in #[
      ← `(CheckedBody entry routing .unselected malformedPlacement),
      ← `(CheckedBody otherEntry routing .unselected otherPlacement)] do
    let bodyGoal ← mkFreshExprSyntheticOpaqueMVar (← Term.elabType mutation)
    let type ← whnf (← inferType bodyGoal)
    let alignment ← mkAppM ``CheckedBody.alignment #[bodyGoal]
    let goal ← mkFreshExprSyntheticOpaqueMVar (← inferType alignment)
    let saved ← saveState
    let _ ← Elab.Tactic.run goal.mvarId! do
      let used ← ZkcTools.ConstructionBindings.TargetPlacement.propose goal.mvarId!
        type.getAppArgs[2]! type.getAppArgs[5]!
        ZkcTools.ConstructionBindings.Alignment.solveStructural
      unless used.isNone && !(← goal.mvarId!.isAssigned) do
        throwError "malformed-service-family-was-reused"
    saved.restore
  logInfo m!"TYPED-SERVICE-FAMILY reused=2; source-and-target-refusals=2; family={family}"

#print axioms discovery
#print axioms first
#print axioms second
end Tests.ConnectionTypedServiceInstallation
