import Tests.SourceConnectionPilot
import Tests.ConnectionRefusal
import ZkcTools.ConstructionBindings.Root
import Zkc.Construction.ConnectionRouteCoverageRoot

/-! Direct typed source/target fixtures for nested reusable families. The
guarded leaf is called by an intermediate declaration. Two intermediate calls
have distinct occurrence contexts, source scopes and physical prefix lengths.
The same source is connected with plain and retained-transcript boundaries.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
noncomputable section
namespace Tests.ConnectionNestedFamilies
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings

meta section
open Lean Meta Elab Command

private def applicationFamily (application : Expr) : MetaM Name := do
  let fields ← Family.constructorFields application
  let field := fun name => (fields.find? (·.1 == name)).get!.2
  let alignment := field `bodyCertificate
  let extent := field `physicalExtent
  unless alignment.isAppOf ``ConnectionTargetPlacement.CheckedBody.alignment &&
      extent.isAppOf ``ConnectionTargetPlacement.CheckedBody.physicalExtent do
    throwError "nested application reconstructed its child"
  let body := alignment.getAppArgs.back!
  unless body == extent.getAppArgs.back! do
    throwError "nested alignment and extent use different bodies"
  let some family := body.getAppFn.constName?
    | throwError "nested application has no family constant"
  return family

elab "audit_nested_families " root:ident retained:(&"retained")? : command => liftTermElabM do
  let root ← realizeGlobalConstNoOverloadWithInfo root
  let registry := TargetPlacement.checkedBodies.getState (← getEnv)
  unless registry.size == 2 do throwError "expected exactly one leaf and one parent family"
  let value := (← getConstInfo root).value!
  if value.hasSorry || value.hasMVar then throwError "unfinished nested root"
  let applications ← Family.applications value
  unless applications.size == 2 do throwError "expected two parent applications"
  let expected := if retained.isSome then ``ConnectionCertificate.Alignment.applicationRetainedHistory
    else ``ConnectionCertificate.Alignment.application
  for application in applications do
    unless application.isAppOf expected do throwError "wrong application history rule"
  let parent ← applicationFamily applications[0]!
  unless registry.contains parent && (← applicationFamily applications[1]!) == parent do
    throwError "repeated placements do not reuse the same parent constant"
  let first ← Family.application applications[0]!
  let second ← Family.application applications[1]!
  let field := fun name placement => mkAppM name #[placement]
  for name in [``ConnectionTargetPlacement.Placement.context, ``ConnectionTargetPlacement.Placement.scope] do
    if ← withTransparency .all <| isDefEq (← field name first.placement) (← field name second.placement) then
      throwError "fixture lost its distinct caller contexts or scopes"
  let length := fun placement => do
    let layout ← field ``ConnectionTargetPlacement.Placement.layout placement
    let some size ← getNatValue? (← whnf (← mkAppM ``List.length #[layout]))
      | throwError "fixture has no concrete prefix length"
    pure size
  let firstLength ← length first.placement
  let secondLength ← length second.placement
  unless secondLength == firstLength + 1 do throwError "fixture lost its growing physical prefix"
  let nested ← Family.applications (← getConstInfo parent).value!
  unless nested.size == 1 && nested[0]!.isAppOf expected do
    throwError "parent has no checked nested application"
  let child ← applicationFamily nested[0]!
  unless registry.contains child && child != parent do
    throwError "parent does not reference the distinct checked leaf family"
  unless (← Family.applications (← getConstInfo child).value!).isEmpty do
    throwError "leaf unexpectedly contains another application"
  let guarded ← IO.mkRef false
  (← getConstInfo child).value!.forEach fun expression => do
    if expression.isAppOf ``ConnectionCertificate.Alignment.guard then guarded.set true
  unless ← guarded.get do throwError "leaf family lost the source guard"
  for name in registry do
    let info ← getConstInfo name
    if info.value!.hasSorry || info.value!.hasMVar then throwError "unfinished checked family"
    Interface.auditFamilyType info.type
    forallTelescopeReducing info.type fun parameters result => do
      unless result.isAppOf ``ConnectionTargetPlacement.CheckedBody do
        throwError "family has no checked body result"
      for parameter in parameters do
        let type ← whnf (← inferType parameter)
        if type.isAppOf ``ConnectionCertificate.Alignment || type.isAppOf ``ConnectionTargetPlacement.CheckedBody then
          throwError "family takes its body as a premise"
        if (← isProp type) && !(← Interface.structural type) then
          throwError "family has a nonfinite proof premise: {type}"
      logInfo m!"NESTED-INTERFACE {name}: parameters={parameters.size}"
  logInfo m!"NESTED-REFERENCES {root}: parent={parent}; child={child}; parent_uses=2; child_uses=1; prefixes={firstLength},{secondLength}"
end

def leafSignature : ProtocolSignature :=
  ⟨"leaf", ["P", "V"], [.boolean], [.boolean], [[0,1]], [[0,1]]⟩
def middleSignature : ProtocolSignature := {leafSignature with name := "middle"}
def runSignature : ProtocolSignature := {leafSignature with name := "main"}
def leafBody : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "guard") .nil .nil <|
  .letOp (.guard 1 "guard") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)
def middleBody : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "inside") .nil .nil <|
  .letOp (.protocolApply leafSignature [0,1] "inside") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)
def runBody : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "first") .nil .nil <|
  .letOp (.protocolApply middleSignature [0,1] "first") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanAnd rfl) (.cons .here (.cons .here .nil)) .nil <|
  .letOp (.mark "second") .nil .nil <|
  .letOp (.protocolApply middleSignature [0,1] "second") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

private def protocol (name : String) (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, [.boolean], [.boolean],
    some ⟨["P", "V"], [["P", "V"]], [["P", "V"]]⟩,
    [], some (.protocol ⟨name, []⟩), body⟩

def snapshot : Snapshot := {Tests.SourceConnectionPilot.snapshot with
  definitions := [protocol "leaf" (.block [
      .instruction (.guard "V") [0] [] [] "guard"] (.ret [0])),
    protocol "middle" (.block [
      .instruction (.protocolApply "leaf" ["P", "V"]) [0] [.boolean] [] "inside"] (.ret [0])),
    protocol "main" (.block [
      .instruction (.protocolApply "middle" ["P", "V"]) [0] [.boolean] [] "first",
      .instruction .booleanAnd [0,0] [.boolean] [] "",
      .instruction (.protocolApply "middle" ["P", "V"]) [0] [.boolean] [] "second"] (.ret [0]))]
  contracts := [⟨"leaf", []⟩, ⟨"middle", []⟩, ⟨"main", []⟩]}
structured_views snapshot helpers [] protocols [leaf, middle, run]
example : Structured.check snapshot = .ok program := kernel_admission

def policy : Policy := ⟨"main", "P", "V", 0, "", [], [0], [], "zkc.framed/0", ""⟩
def instructions (fresh : Nat) : List Zkc.Construction.Instruction := [
  ⟨.guard "first/inside/guard", [0], [], []⟩,
  ⟨.calculate .booleanAnd, [0,0], [.data .boolean], []⟩,
  ⟨.guard "second/inside/guard", [fresh], [], []⟩]
def target (fresh : Nat) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.guard 0 []) <|
  Domain.View.sequence (Domain.View.calculation model .booleanAnd [0,0] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.guard fresh []) Domain.View.empty

def plainContext : Context := .plain "main" ["P", "V"] 0 1
def retainedContext : Context := .fiatShamir "main" ["P", "V"] 0 1 0 "random.field/0"
  (some (.draw "field")) "suite" []
def plainRouting : Original.Routing := ⟨snapshot, plainContext, .validator, 0, [], [], [], []⟩
def retainedRouting : Original.Routing := {plainRouting with context := retainedContext}
def plainArtifact : Participant :=
  ⟨snapshot.source, snapshot.source, policy, "main.V", [.data .boolean], [.data .boolean],
    instructions 1, [1], []⟩
def retainedArtifact : Participant :=
  {plainArtifact with
    inputs := [.data .boolean, .transcript "suite"]
    outputs := [.data .boolean, .transcript "suite"]
    instructions := instructions 2
    returned := [2,1]}

theorem target_eq (model : DomainModel) (context : Context) (fresh : Nat) :
    Domain.Correspondence.Block (model := model) (program := program)
      (context := context) (instructions fresh) (target fresh model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.guard _ _ _) <|
  Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _) <|
  Domain.Correspondence.sequence (Domain.Correspondence.guard _ _ _) Domain.Correspondence.empty

def pattern : NormalForm.InputPattern [.boolean] := .cons .optional .nil
def leafTemplate : ConnectionLibrary.SourceTemplate program.payload [] :=
  (ConnectionLibrary.SourceTemplate.build program.payload [] ⟨0, by decide⟩ 1 pattern).toOption.get (by decide +kernel)
def middleTemplate : ConnectionLibrary.SourceTemplate program.payload [leafTemplate.key] :=
  (ConnectionLibrary.SourceTemplate.build program.payload [leafTemplate.key] ⟨1, by decide⟩ 1 pattern).toOption.get
    (by decide +kernel)
def library : ConnectionLibrary.Bundle program.payload := by
  derive_connection_library roles [1]

-- Changing pins preserves the normalized form but changes the exact source
-- entry. Such an entry must not inherit the installed parent's certificate.
def pinnedMiddle : ConnectionLibrary.SourceTemplate program.payload [leafTemplate.key] :=
  {middleTemplate with pins := [some 0]}
def pinnedEntry : ConnectionLibrary.Entry program.payload pinnedMiddle.key :=
  ⟨[leafTemplate.key], .extend .empty leafTemplate, pinnedMiddle, rfl⟩
def pinnedLeaf : ConnectionLibrary.SourceTemplate program.payload [] :=
  {leafTemplate with pins := [none]}
def changedEarlierMiddle : ConnectionLibrary.SourceTemplate program.payload [pinnedLeaf.key] :=
  (ConnectionLibrary.SourceTemplate.build program.payload [pinnedLeaf.key] ⟨1, by decide⟩ 1 pattern).toOption.get
    (by decide +kernel)
def changedEarlierEntry : ConnectionLibrary.Entry program.payload changedEarlierMiddle.key :=
  ⟨[pinnedLeaf.key], .extend .empty pinnedLeaf, changedEarlierMiddle, rfl⟩

set_option zkc.connection.generateReusableBodies true

def plain : RootCertificate program plainRouting 1 plainArtifact := by
  derive_root_connection_with_library target (target 1) correspondence (fun model => target_eq model plainContext 1)
    services [] library library

set_option zkc.connection.generateReusableBodies false
set_option zkc.connection.requireReusableBodies true

def strictPlain : RootCertificate program plainRouting 1 plainArtifact := by
  derive_root_connection_with_library target (target 1) correspondence (fun model => target_eq model plainContext 1)
    services [] library library

audit_nested_families plain
audit_nested_families strictPlain

example : True := by
  expect_connection_refusal "nested target reads a missing cell" because "alignment-reusable-body-refused"
    have : RootCertificate program plainRouting 1
        {plainArtifact with instructions := instructions 9} := by
      derive_root_connection_with_library target (target 9)
        correspondence (fun model => target_eq model plainContext 9) services [] library library
  trivial

example : True := by
  run_tac
    let applications ← Family.applications (← Lean.getConstInfo ``strictPlain).value!
    let input ← Family.application applications[0]!
    for name in [``pinnedEntry, ``changedEarlierEntry] do
      let entry := Lean.mkConst name
      if ← TargetPlacement.hasEntry entry then Lean.throwError "changed source matched an installed Entry"
      let goal ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.inferType input.guide)
      let found ← TargetPlacement.propose goal.mvarId! entry input.placement
        (fun _ => Lean.throwError "source-entry control unexpectedly requested an interface fact")
      unless found.isNone do Lean.throwError "parent family accepted changed source entry"
      if ← goal.mvarId!.isAssigned then Lean.throwError "refused entry left an assigned body"
      Lean.logInfo m!"checked_refusal: nested exact source entry {name}"
  trivial

example : True := by
  expect_connection_refusal "nested Boolean operand has an index cell" because "Application type mismatch"
    have : ConnectionFrame.Readback ([.data (.present (.index 1))] : ConnectionFrame.Layout [])
        (.cons (.present (.bool true)) .nil) [.data 0] := .data 0 rfl .nil
  trivial

section
-- Each profile discovers its own families: the registry deliberately refuses
-- reconstruction after an exact Entry has already been registered.
run_cmd Lean.modifyEnv fun env => TargetPlacement.checkedBodies.modifyState env (fun _ => #[])
set_option zkc.connection.generateReusableBodies true
set_option zkc.connection.requireReusableBodies false

def retained : RootCertificate program retainedRouting 1 retainedArtifact := by
  derive_root_connection_with_library target (target 2) correspondence (fun model => target_eq model retainedContext 2)
    services [] library library

set_option zkc.connection.generateReusableBodies false
set_option zkc.connection.requireReusableBodies true

def strictRetained : RootCertificate program retainedRouting 1 retainedArtifact := by
  derive_root_connection_with_library target (target 2) correspondence (fun model => target_eq model retainedContext 2)
    services [] library library

audit_nested_families retained retained
audit_nested_families strictRetained retained

example : True := by
  expect_connection_refusal "nested retained history points at data" because "alignment-reusable-body-refused"
    have : RootCertificate program retainedRouting 1 {retainedArtifact with returned := [2,0]} := by
      derive_root_connection_with_library target (target 2)
        correspondence (fun model => target_eq model retainedContext 2) services [] library library
  trivial

example : True := by
  expect_connection_refusal "nested retained history has another nominal suite" because "Application type mismatch"
    have : ConnectionCertificate.HistoryReadback
        ([.history "other"] : ConnectionFrame.Layout []) "suite" (some 0) := .transcript 0 rfl
  trivial

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  strictPlain.simulation model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  strictRetained.simulation model physical
def plainFacts := strictPlain.facts
def retainedFacts := strictRetained.facts
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  plainFacts.coverage model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  retainedFacts.coverage model physical

#print axioms strictPlain
#print axioms strictRetained
#print axioms plainFacts
#print axioms retainedFacts
#print axioms ConnectionTargetPlacement.historySeparationCheck_sound
end
end Tests.ConnectionNestedFamilies
