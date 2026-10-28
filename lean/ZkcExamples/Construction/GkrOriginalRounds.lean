module

public import ZkcExamples.Construction.GkrOriginalCoefficient
public import Zkc.Construction.OriginalHeadReduction
public meta import Zkc.Construction.ArtifactBindingTactic
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.CasesM
public meta import Zkc.Construction.ProcessViewTactic

@[expose] public section
/-! A shared nominal round certificate, instantiated at both qualified s9
applications. The layer and round coordinates stay in their original order. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Zkc.Construction.Original.receive Zkc.Construction.Original.send Zkc.Construction.Original.query
noncomputable section
namespace ZkcExamples.Construction.GkrOriginalRounds
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrRoundsNormalForms GkrSourceRouting
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def messageSite (side : Side) (packet : Fin 3) : String :=
  if packet = 0 then round0Site (roundContext side)
  else if packet = 1 then round1Site (roundContext side) else round2Site (roundContext side)

theorem site0 (side : Side) : round0Site (roundContext side) = messageSite side 0 := rfl
theorem site1 (side : Side) : round1Site (roundContext side) = messageSite side 1 := rfl
theorem site2 (side : Side) : round2Site (roundContext side) = messageSite side 2 := by
  simp only [messageSite]; rfl

def messageTemplate (side : Side) (packet : Fin 3) : Template :=
  match side with
  | .left => if packet = 0 then templates[2]'(by decide +kernel)
    else if packet = 1 then templates[3]'(by decide +kernel) else templates[4]'(by decide +kernel)
  | .right => if packet = 0 then templates[7]'(by decide +kernel)
    else if packet = 1 then templates[8]'(by decide +kernel) else templates[9]'(by decide +kernel)
def drawTemplate : Side → Template
  | .left => templates[5]'(by decide +kernel)
  | .right => templates[10]'(by decide +kernel)
def deliveryTemplate : Side → Template
  | .left => templates[6]'(by decide +kernel)
  | .right => templates[11]'(by decide +kernel)

abbrev message (side : Side) (packet : Fin 3) (layer index : Nat) :=
  Domain.atCoordinates (context.message (messageSite side packet) 0 1) [layer, index]
abbrev draw (side : Side) (layer index : Nat) :=
  Domain.atCoordinates (context.query (challengeSite (roundContext side)) (.draw scalarDomain)) [layer, index]
abbrev delivery (side : Side) (layer index : Nat) :=
  Domain.atCoordinates (context.message (deliverySite (roundContext side)) 1 0) [layer, index]

theorem draw_request (side : Side) (layer index : Nat) :
    (draw side layer index).request = some (.draw scalarDomain) := rfl

theorem compiled_message (side : Side) (packet : Fin 3) (layer index : Nat) :
    Domain.templateOrigin context (messageTemplate side packet) [layer, index] =
      some (message side packet layer index) := by
  cases side <;> fin_cases packet <;> kernel_rfl

theorem compiled_draw (side : Side) (layer index : Nat) :
    Domain.queryOrigin context context.suite scalarDomain (drawTemplate side) [layer, index] =
      some (draw side layer index) := by cases side <;> kernel_rfl

theorem compiled_delivery (side : Side) (layer index : Nat) :
    Domain.templateOrigin context (deliveryTemplate side) [layer, index] =
      some (delivery side layer index) := by cases side <;> kernel_rfl

structure Routes (mode : Domain.Mode) (side : Side) (handle layer index : Nat) : Prop where
  message : ∀ packet, (routing handle mode).message (roundFrames side layer index)
    (messageSite side packet) 0 1 = some (GkrOriginalRounds.message side packet layer index)
  draw : (routing handle mode).draw (roundFrames side layer index)
    (challengeSite (roundContext side)) scalarDomain handle = some (GkrOriginalRounds.draw side layer index)
  delivered : (routing handle mode).message (roundFrames side layer index)
    (deliverySite (roundContext side)) 1 0 = some (delivery side layer index)
  delivery : (routing handle mode).delivery (roundFrames side layer index)
    (deliverySite (roundContext side)) scalarDomain 1 =
      some (GkrOriginalRounds.draw side layer index, GkrOriginalRounds.delivery side layer index)

theorem validator_receive (side : Side) (handle layer index : Nat)
    (routes : Routes .validator side handle layer index) (packet : Fin 3)
    (history : Domain.History (uniformCarriers F G)) :
    Original.receive (routing handle .validator) ⟨roundFrames side layer index, history⟩
      (.field scalarDomain) (messageSite side packet) 0 =
      .call (.receive (.field scalarDomain) (messageSite side packet) (messageSite side packet) (context.role 0))
        (fun value => .call (.observe (.message (message side packet layer index) (.field scalarDomain value)))
          (fun _ => .done (value, ⟨roundFrames side layer index,
            history ++ [.message (message side packet layer index) (.field scalarDomain value)]⟩))) :=
  Original.validator_receive (routing handle .validator) ⟨roundFrames side layer index, history⟩
    (messageSite side packet) scalarDomain 0 (message side packet layer index) rfl (routes.message packet)

theorem validator_query (side : Side) (handle layer index : Nat)
    (routes : Routes .validator side handle layer index)
    (history : Domain.History (uniformCarriers F G)) :
    Original.query (routing handle .validator) ⟨roundFrames side layer index, history⟩
      (challengeSite (roundContext side)) scalarDomain handle =
      .call (.query history (draw side layer index)) (fun reply =>
        .done (Original.fieldReply (draw side layer index) scalarDomain rfl reply,
          ⟨roundFrames side layer index, history ++ [.challenge (draw side layer index)]⟩)) :=
  Original.public_query (routing handle .validator) ⟨roundFrames side layer index, history⟩
    (challengeSite (roundContext side)) scalarDomain handle (draw side layer index) rfl routes.draw

theorem validator_send (side : Side) (handle layer index : Nat)
    (routes : Routes .validator side handle layer index)
    (history : Domain.History (uniformCarriers F G)) (value : F) :
    Original.send (routing handle .validator) ⟨roundFrames side layer index, history⟩
      (.field scalarDomain) (deliverySite (roundContext side)) 0 value =
      .call (.observe (.message (delivery side layer index) (.field scalarDomain value)))
        (fun _ => .done ((), ⟨roundFrames side layer index,
          history ++ [.message (delivery side layer index) (.field scalarDomain value)]⟩)) := by
  simp only [Original.send, show (routing handle .validator).mode = .validator from rfl,
    show (routing handle .validator).context.validator = 1 from rfl, routes.delivered,
    Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record]

def validatorCarried (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector scalarDomain point), .data (.field scalarDomain claim), .transcript context.suite history]

def ValidatorReturns (layer : Nat)
    (source : Values (Component (assignment F G)) roundState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point claim history, source = (verifierState (some point) (some claim), ⟨GkrOriginalCoefficient.outer layer, history⟩) ∧
    frame = validatorCarried point claim history

def validatorBody (model : DomainModel) (side : Side) (offset layerRef : Nat) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.receive (messageSite side 0) (messageSite side 0) (context.role 0) (.field scalarDomain) [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 5) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 6) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (messageTemplate side 0) (offset + 3) (offset + 4) (offset + 7) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.receive (messageSite side 1) (messageSite side 1) (context.role 0) (.field scalarDomain) [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 10) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 11) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (messageTemplate side 1) (offset + 8) (offset + 9) (offset + 12) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.receive (messageSite side 2) (messageSite side 2) (context.role 0) (.field scalarDomain) [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 15) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 16) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (messageTemplate side 2) (offset + 13) (offset + 14) (offset + 17) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldAdd scalarDomain) [(offset + 4), (offset + 4)] [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldAdd scalarDomain) [(offset + 19), (offset + 9)] [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldAdd scalarDomain) [(offset + 20), (offset + 14)] [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldEqual scalarDomain) [(offset + 2), (offset + 21)] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.guard (offset + 22) []) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 23) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 24) offset [.indices]) <|
  Domain.View.sequence (Domain.View.challenge context context.suite scalarDomain (drawTemplate side) (offset + 18) (offset + 25) [.data (.field scalarDomain), .transcript context.suite]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 28) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 29) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (deliveryTemplate side) (offset + 27) (offset + 26) (offset + 30) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.helper model GkrSourceViews.program GkrSourceBodies.appendHelper.name [(offset + 1), (offset + 26)] [.data (.vector scalarDomain)]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldMultiply scalarDomain) [(offset + 26), (offset + 14)] [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldAdd scalarDomain) [(offset + 9), (offset + 33)] [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldMultiply scalarDomain) [(offset + 26), (offset + 34)] [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.calculation model (Calculation.fieldAdd scalarDomain) [(offset + 4), (offset + 35)] [.data (.field scalarDomain)]) <|
  Domain.View.empty

def validatorCallback (side : Side) (handle offset layerRef layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (layerRead : captured[layerRef]? = some (.data (.index layer)))
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .validator side handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ValidatorReturns layer) (GkrOriginalCoefficient.outer layer)
        (qualifyProtocolSite (roundContext side).applicationPrefix "s9") index
        [offset + 32, offset + 36, offset + 31]
        [.data (.vector scalarDomain), .data (.field scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        ((roundFn (F := F) (G := G) (roundContext side) 1
          (.cons (some index) ((verifierState (some point) (some claim)).append
            (.cons (some handle) .nil)))).interpret Occurrence.actions)
        ⟨roundFrames side layer index, history⟩)
      (validatorBody (ringModel F G) side offset layerRef
        (captured ++ .data (.index index) :: validatorCarried point claim history)) := by
  have inside : layerRef < offset := by
    rw [← size]; exact (List.getElem?_eq_some_iff.mp layerRead).choose
  have role : 1 = (roundContext side).roles 1 := by cases side <;> rfl
  have separate : (roundContext side).roles 0 ≠ 1 := by cases side <;> decide
  have role0 : (roundContext side).roles 0 = 0 := by cases side <;> rfl
  apply Classical.choice
  obtain ⟨replacement, profile⟩ := Original.Routing.draw_profile routes.draw
  refine ⟨?_⟩
  rw [verifier_process (roundContext side) 1 role separate index (some handle) (some point) (some claim)]
  clear role
  simp only [verifierProcess, PIR.Process.interpret_bind, Original.fold_bind,
    PIR.Process.bind_assoc, validatorBody, Domain.View.sequence]
  derive_artifact_binding normalizing (
    saturate_artifact (
      conv => arg -1; simp (config := { failIfUnchanged := false }) (disch := omega) only
          [↓Original.stopAtCall, List.append_assoc, List.cons_append, List.nil_append, List.length_cons, List.length_nil, List.length_append, List.getElem?_append_left, List.getElem?_append_right,
           size, inside, layerRead, Nat.add_sub_cancel_left, Nat.sub_self,
           List.getElem?_cons_zero, List.getElem?_cons_succ]
      normalize_artifact_operations
          [GkrDomainHelpers.append (F := F) (G := G), compiled_message, compiled_draw, compiled_delivery, draw_request,
           (validator_receive (F := F) (G := G) side handle layer index routes 0),
           (validator_receive (F := F) (G := G) side handle layer index routes 1),
           (validator_receive (F := F) (G := G) side handle layer index routes 2),
           (validator_query (F := F) (G := G) side handle layer index routes),
           (validator_send (F := F) (G := G) side handle layer index routes)] unfolding
          [site0, site1, site2, List.append_assoc, apply_ite, PIR.Process.bind_ite, validatorCarried, Original.fieldReply, Domain.Raw, Request.draw,
           Original.fold_done, Original.fold_halt, Original.foldIf,
           Original.foldActionCall, Original.foldActionDone, Original.foldActionHalt,
           Original.fold_bind, PIR.Process.interpret_bind, Original.operations, profile, role0,
           GkrRoundsReading.append_plain, Values.get]))
    solving (first
      | solve | simp [ArtifactBinding.Captures, List.append_assoc]
      | (unfold Original.IterationReturns ValidatorReturns
         refine ⟨rfl, _, ?_, rfl, _, _, _, rfl, rfl⟩
         simp (disch := omega) [Domain.read, validatorCarried, List.getElem?_append_left,
           List.getElem?_append_right, size, Nat.add_sub_cancel_left, Environment.prepend,
           Values.get, Bind.bind, Option.bind]; rfl))


theorem producer_send (side : Side) (handle layer index : Nat)
    (routes : Routes .producer side handle layer index) (packet : Fin 3)
    (history : Domain.History (uniformCarriers F G)) (value : F) :
    Original.send (routing handle .producer) ⟨roundFrames side layer index, history⟩
      (.field scalarDomain) (messageSite side packet) 1 value =
      .call (.send (messageSite side packet) (messageSite side packet) (context.role 1) (.field scalarDomain value))
        (fun _ => .call (.observe (.message (message side packet layer index) (.field scalarDomain value)))
          (fun _ => .done ((), ⟨roundFrames side layer index,
            history ++ [.message (message side packet layer index) (.field scalarDomain value)]⟩))) := by
  simp only [Original.send, show (routing handle .producer).mode = .producer from rfl,
    show (routing handle .producer).context.producer = 0 from rfl, routes.message,
    Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record]
  rfl

theorem producer_receive (side : Side) (handle layer index : Nat)
    (routes : Routes .producer side handle layer index)
    (history : Domain.History (uniformCarriers F G)) :
    Original.receive (routing handle .producer) ⟨roundFrames side layer index, history⟩
      (.field scalarDomain) (deliverySite (roundContext side)) 1 =
      .call (.query history (draw side layer index)) (fun reply =>
        let value := Original.fieldReply (draw side layer index) scalarDomain rfl reply
        .call (.observe (.message (delivery side layer index) (.field scalarDomain value))) (fun _ =>
          .done (value, ⟨roundFrames side layer index,
            history ++ [.challenge (draw side layer index),
              .message (delivery side layer index) (.field scalarDomain value)]⟩))) :=
  Original.producer_delivery (routing handle .producer) ⟨roundFrames side layer index, history⟩
    (deliverySite (roundContext side)) scalarDomain 1 (draw side layer index) (delivery side layer index)
    rfl routes.delivery rfl

def producerCarried (add mul left right point : List F)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector scalarDomain add), .data (.vector scalarDomain mul),
    .data (.vector scalarDomain left), .data (.vector scalarDomain right),
    .data (.vector scalarDomain point), .transcript context.suite history]

def ProducerReturns (layer : Nat)
    (source : Values (Component (assignment F G)) roundState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ add mul left right point history,
    source = (proverState (some add) (some mul) (some left) (some right) (some point),
      ⟨GkrOriginalCoefficient.outer layer, history⟩) ∧ frame = producerCarried add mul left right point history

def producerBody (model : DomainModel) (side : Side) (offset layerRef : Nat) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.helper model GkrSourceViews.program GkrSourceBodies.helper41Helper.name [(offset + 1), (offset + 2), (offset + 3), (offset + 4)] (GkrSourceBodies.helper41Helper.outputs.map ValueSort.data)) <|
  Domain.View.sequence (Domain.View.send (messageSite side 0) (messageSite side 0) (context.role 1) (offset + 7) []) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 10) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 11) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (messageTemplate side 0) (offset + 6) (offset + 7) (offset + 12) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.send (messageSite side 1) (messageSite side 1) (context.role 1) (offset + 8) []) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 14) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 15) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (messageTemplate side 1) (offset + 13) (offset + 8) (offset + 16) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.send (messageSite side 2) (messageSite side 2) (context.role 1) (offset + 9) []) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 18) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 19) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (messageTemplate side 2) (offset + 17) (offset + 9) (offset + 20) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 22) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 23) offset [.indices]) <|
  Domain.View.sequence (Domain.View.challenge context context.suite scalarDomain (drawTemplate side) (offset + 21) (offset + 24) [.data (.field scalarDomain), .transcript context.suite]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 27) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 28) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite (deliveryTemplate side) (offset + 26) (offset + 25) (offset + 29) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.helper model GkrSourceViews.program GkrSourceBodies.helper45Helper.name [(offset + 1), (offset + 2), (offset + 3), (offset + 4), (offset + 25)] (GkrSourceBodies.helper45Helper.outputs.map ValueSort.data)) <|
  Domain.View.sequence (Domain.View.helper model GkrSourceViews.program GkrSourceBodies.appendHelper.name [(offset + 5), (offset + 25)] [.data (.vector scalarDomain)]) <|
  Domain.View.empty


def producerCallback (side : Side) (handle offset layerRef layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (layerRead : captured[layerRef]? = some (.data (.index layer)))
    (add mul left right point : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .producer side handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ProducerReturns layer) (GkrOriginalCoefficient.outer layer)
        (qualifyProtocolSite (roundContext side).applicationPrefix "s9") index
        [offset + 31, offset + 32, offset + 33, offset + 34, offset + 35, offset + 30]
        [.data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain),
          .data (.vector scalarDomain), .data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        ((roundFn (F := F) (G := G) (roundContext side) 0
          (.cons (some index) ((proverState (some add) (some mul) (some left) (some right) (some point)).append
            (.cons none .nil)))).interpret Occurrence.actions)
        ⟨roundFrames side layer index, history⟩)
      (producerBody (ringModel F G) side offset layerRef
        (captured ++ .data (.index index) :: producerCarried add mul left right point history)) := by
  have inside : layerRef < offset := by
    rw [← size]; exact (List.getElem?_eq_some_iff.mp layerRead).choose
  have role : 0 = (roundContext side).roles 0 := by cases side <;> rfl
  have separate : (roundContext side).roles 1 ≠ 0 := by cases side <;> decide
  have role1 : (roundContext side).roles 1 = 1 := by cases side <;> rfl
  apply Classical.choice
  obtain ⟨replacement, profile⟩ := Original.Routing.delivery_profile routes.delivery
  refine ⟨?_⟩
  rw [prover_process (roundContext side) 0 role separate index none
    (some add) (some mul) (some left) (some right) (some point)]
  clear role
  simp only [proverProcess, PIR.Process.interpret_bind, Original.fold_bind,
    producerBody, Domain.View.sequence, PIR.Process.bind_assoc]
  derive_artifact_binding [GkrOriginalHelpers.continuation] normalizing (
    saturate_artifact (
      try cases_type* Values
      simp (config := { failIfUnchanged := false }) (disch := omega) only
          [↓Original.stopAtCall, List.append_assoc, List.cons_append, List.nil_append, List.getElem?_append_left,
           List.getElem?_append_right, size, inside, layerRead, Nat.add_sub_cancel_left,
           Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ]
      normalize_component_operations
          [compiled_message, compiled_draw, compiled_delivery, draw_request,
           (producer_send (F := F) (G := G) side handle layer index routes 0),
           (producer_send (F := F) (G := G) side handle layer index routes 1),
           (producer_send (F := F) (G := G) side handle layer index routes 2),
           (producer_receive (F := F) (G := G) side handle layer index routes)] unfolding
          [site0, site1, site2, List.append_assoc, producerCarried, Original.encodeHelperResult, Domain.encodeValues,
           Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, Option.map_some, Option.map_none,
           Original.foldActionCall, Original.foldActionDone, Original.foldActionHalt,
           Original.fold_bind, PIR.Process.interpret_bind, Original.operations, profile, role1,
           Original.fieldReply, Domain.Raw, Request.draw, Values.get]))
    solving (first
      | solve | simp [ArtifactBinding.Captures, List.append_assoc]
      | solve | decide +kernel
      | (unfold Original.IterationReturns ProducerReturns
         refine ⟨rfl, _, ?_, rfl, _, _, _, _, _, _, rfl, rfl⟩
         simp (disch := omega) [Domain.read, producerCarried, List.getElem?_append_left,
           List.getElem?_append_right, size, Nat.add_sub_cancel_left, Environment.prepend,
           Values.get, Bind.bind, Option.bind]; rfl)
      | solve | simp (disch := omega) [Domain.read, Domain.encodeValues, Domain.Value.encode,
          Domain.Payload.ofValue, Ty.isHandle, List.getElem?_append_left, List.getElem?_append_right,
          List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.bind_some, Option.pure_def, size, Nat.add_sub_cancel_left]; rfl)

end ZkcExamples.Construction.GkrOriginalRounds
