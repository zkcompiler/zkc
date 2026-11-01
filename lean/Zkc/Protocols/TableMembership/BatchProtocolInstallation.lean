module

public import Zkc.Protocols.TableMembership.ReferenceInstallation
public import Zkc.Source.Structured.Template

@[expose] public section

/-! Whole-source installation for a transmitted point/value batch. The same
body theorem retains arbitrary replies, absent validator inputs, exhaustion,
and both ordered outputs. Source linking fixes the helper closure. -/
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Protocols.TableMembership.BatchSource
open Zkc.Source Zkc.Source.Structured

attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions runSignature

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The owned helper reference keeps optional-input failure and finite exhaustion.
It is independent of the surrounding protocol, application site and role name. -/
def ownedCheckReference (point value : Option F) (batch : Option (Batch F)) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) [.boolean]) :=
  match point, value, batch with
  | some point, some value, some batch =>
      if batch.length < indexLimit then .done (.cons (some (decision point value batch)) .nil)
      else .halt .exhausted
  | _, _, _ => .halt .incomplete

theorem owned_check_equation {field : String} {bindings : Names}
    (payload : UnitPayload) (bodies : Bodies payload.definitions field bindings)
    (self : Nat) (point value : Option F) (batch : Option (Batch F)) :
    Participant.owned self self
      (invoke (Occurrence.helpers (ringModel F G) payload).closed (checkBatchHelper field bindings))
      (.cons point (.cons value (.cons batch .nil))) =
      ownedCheckReference (G := G) point value batch := by
  simp only [Participant.owned, ↓reduceIte]
  cases point with
  | none => rfl
  | some point =>
    cases value with
    | none => rfl
    | some value =>
      cases batch with
      | none => rfl
      | some batch =>
        change (invoke (Occurrence.helpers (ringModel F G) payload).closed
          (checkBatchHelper field bindings) (.cons point (.cons value (.cons batch .nil)))).bind _ = _
        unfold Occurrence.helpers
        rw [Evaluation.closed_invoke_componentTablesOn, closed_ring,
          check_equation payload.linked bodies]
        simp only [ownedCheckReference]
        split <;> simp_all only [PIR.Process.interpret, PIR.Process.bind]
        rfl

/-- Every receive answer is retained even when the returned decision is false. -/
def validatorReference (field : String) (bindings : Names) (protocol : ProtocolNames)
    (ctx : ProtocolContext) (point value : Option F) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) (runSignature field bindings protocol).outputs) :=
  .call (.action (.receive (.sequence (openingTy field bindings))
    (qualifyProtocolSite ctx.applicationPrefix protocol.messageSite) (ctx.roles 0))) fun batch =>
    match point, value with
    | some point, some value =>
        if batch.length < indexLimit then
          .done (.cons (some (decision point value batch)) (.cons (some batch) .nil))
        else .halt .exhausted
    | _, _ => .halt .incomplete

abbrev validatorPattern (field : String) (bindings : Names) (protocol : ProtocolNames) :
    NormalForm.InputPattern (runSignature field bindings protocol).inputs :=
  .cons .optional (.cons .optional (.cons .absent .nil))

theorem validator_body_reference {field : String} {bindings : Names} {protocol : ProtocolNames}
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions field bindings)
    (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
    (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2)
    (point value : Option F) :
    (runBody field bindings protocol).denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        (definitions.foldl (Evaluation.ComponentTablesOn.extend (ringModel F G) (.silent _)) ⟨[], []⟩)
        (ctx.roles 1) protocols ctx Occurrence.iterations)
      (Values.cons point (.cons value (.cons none .nil))).get =
      validatorReference (G := G) field bindings protocol ctx point value := by
  have different := distinct 0 (by decide +kernel) (by decide +kernel)
  simp only [runBody, runSignature, ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions, Region.denote, participantMeaningWithOn, protocolOperationWithOn,
    Operands.eval, Values.get, Regions.denote, SiteObservations.silent, PIR.Process.bind,
    Environment.prepend, Environment.push, Participant.exchange, different, ↓reduceIte,
    PIR.Process.interpret, Occurrence.actions]
  unfold validatorReference
  congr 1
  funext batch
  simp only [Participant.restrict, List.map_cons, List.map_nil,
    List.contains_cons, List.contains_nil, beq_self_eq_true, Bool.true_or, ↓reduceIte,
    Participant.owned]
  cases point with
  | none => rfl
  | some point =>
    cases value with
    | none => rfl
    | some value =>
      change ((invoke
        (definitions.foldl (Evaluation.ComponentTablesOn.extend (ringModel F G)
          (.silent (Occurrence.signature (uniformCarriers F G)))) ⟨[], []⟩).closed
        (checkBatchHelper field bindings) (.cons point (.cons value (.cons batch .nil)))).bind
          (fun results => .done results.present)).bind _ = _
      rw [Evaluation.closed_invoke_componentTablesOn, closed_ring]
      rw [check_equation linked bodies]
      split <;> rfl

/-- Exact source association installs the whole Process, including its full
output mask. Other private input values cannot select the received batch. -/
theorem validator_installed {field : String} {bindings : Names} {protocol : ProtocolNames}
    (payload : UnitPayload) (bodies : Bodies payload.definitions field bindings)
    (association : Template.Association payload (runSignature field bindings protocol)
      (runBody field bindings protocol))
    (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2)
    (point value : Option F) (privateBatch : Option (Batch F)) :
    invokeProtocol (Occurrence.table (ringModel F G) payload)
      (runSignature field bindings protocol) ctx (ctx.roles 1)
      (.cons point (.cons value (.cons privateBatch .nil))) =
      validatorReference (G := G) field bindings protocol ctx point value := by
  have installed := association.invoke (model := ringModel F G) 1 ctx distinct (validatorPattern field bindings protocol)
    rfl (.cons point (.cons value .nil)) (.cons privateBatch .nil)
    (validatorReference (G := G) field bindings protocol ctx point value)
    (validator_body_reference (protocol := protocol) payload.definitions payload.linked bodies
      (Occurrence.table (ringModel F G) payload) ctx distinct point value) rfl rfl
  exact installed.trans (by
    unfold validatorReference
    simp only [PIR.Process.bind]
    congr 1
    funext batch
    cases point <;> cases value <;> simp only [PIR.Process.bind]
    split <;> rfl)

/-- Existing normal forms can keep a local batch check and apply one installed
batch protocol. This signature is independent of the caller's body and outputs. -/
def callSignature (field : String) (bindings : Names) (protocol : ProtocolNames) :
    NormalForm.Signature where
  kept := [checkBatchHelper field bindings]
  callees := [⟨runSignature field bindings protocol, 1, validatorPattern field bindings protocol, []⟩]

def validatorCallees (field : String) (bindings : Names) (protocol : ProtocolNames) :
    NormalForm.CalleeProcesses (ringModel F G) (callSignature field bindings protocol).callees
      (Occurrence.signature (uniformCarriers F G)) :=
  Fin.cases (fun ctx args => validatorReference (G := G) field bindings protocol ctx
    (args.get .here) (args.get (.there .here))) (fun entry => entry.elim0)

/-- The callee installation uses the existing full source theorem and masks;
clients supply no helper/callee positions or interpreter proofs. -/
theorem validator_callees_hold {field : String} {bindings : Names} {protocol : ProtocolNames}
    (payload : UnitPayload) (bodies : Bodies payload.definitions field bindings)
    (association : Template.Association payload (runSignature field bindings protocol)
      (runBody field bindings protocol)) {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    NormalForm.CalleesHold (Occurrence.table (ringModel F G) payload)
      (validatorCallees (G := G) field bindings protocol) input := by
  intro entry ctx args others _ distinct
  have only : entry = (0 : Fin 1) := Fin.eq_zero entry
  subst entry
  cases args with | cons point rest => ?_
  cases rest with | cons value rest => ?_
  cases rest
  cases others with | cons privateBatch rest => ?_
  cases rest
  change invokeProtocol (Occurrence.table (ringModel F G) payload)
      (runSignature field bindings protocol) ctx (ctx.roles 1)
      (.cons point (.cons value (.cons privateBatch .nil))) =
    (validatorReference (F := F) (G := G) field bindings protocol ctx point value).bind
      (fun out => .done (NormalForm.staticMask 1 out [[1], [1]]
        (Operands.identity (runSignature field bindings protocol).outputs)))
  have installed := validator_installed (F := F) (G := G) payload bodies association ctx distinct point value privateBatch
  exact installed.trans (by
    unfold validatorReference
    simp only [PIR.Process.bind]
    congr 1
    funext batch
    cases point <;> cases value <;> simp only [PIR.Process.bind]
    split <;> rfl)

end Zkc.Protocols.TableMembership.BatchSource
