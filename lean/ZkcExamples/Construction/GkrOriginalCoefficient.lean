module

public import ZkcExamples.Construction.GkrOriginalOutput
public import ZkcExamples.Construction.GkrOriginalHelpers
public meta import Zkc.Construction.ArtifactBindingTactic
public meta import Mathlib.Tactic.FailIfNoProgress

@[expose] public section
/-! Exact nested coefficient callbacks, retaining the complete original frame
stack and both physical coordinate reads, including an index equal to zero. -/
set_option Elab.async false
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Zkc.Construction.Original.receive Zkc.Construction.Original.send Zkc.Construction.Original.query
noncomputable section
namespace ZkcExamples.Construction.GkrOriginalCoefficient
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks GkrSourceRouting
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def frames (layer index : Nat) : Original.Frames := [⟨"s57", layer⟩, ⟨"s91", index⟩]
def outer (layer : Nat) : Original.Frames := [⟨"s57", layer⟩]
abbrev site := "label_6c696e655f636f656666696369656e74_0"
abbrev origin (layer index : Nat) := Domain.atCoordinates (context.message site 0 1) [layer, index]
def template : Template := templates[13]'(by decide +kernel)

theorem compiled_origin (layer index : Nat) :
    Domain.templateOrigin context template [layer, index] = some (origin layer index) := by
  kernel_rfl

structure Routes (mode : Domain.Mode) (handle layer index : Nat) : Prop where
  message : (routing handle mode).message (frames layer index) site 0 1 = some (origin layer index)

def carried (coefficients : List F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector scalarDomain coefficients), .transcript context.suite history]

def ValidatorReturns (layer : Nat)
    (source : Values (Component (assignment F G)) coefficientState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ coefficients history, source = (verifierCoefficientState (some coefficients), ⟨outer layer, history⟩) ∧
    frame = carried coefficients history

def validatorBody (model : DomainModel) (offset layerRef : Nat) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.receive site site (context.role 0) (.field scalarDomain)
    [.data (.field scalarDomain)]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 4) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 5) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite template
    (offset + 2) (offset + 3) (offset + 6) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.helper model GkrSourceViews.program
    GkrSourceBodies.appendHelper.name [offset + 1, offset + 3] [.data (.vector scalarDomain)])
    Domain.View.empty

theorem validator_source (handle layer index : Nat) (coefficients : List F)
    (history : Domain.History (uniformCarriers F G)) (routes : Routes .validator handle layer index) :
    Original.fold (routing handle .validator)
      ((coefficientFn (F := F) (G := G) {} 1
        (.cons (some index) ((verifierCoefficientState (some coefficients)).append (.cons none .nil)))).interpret
          Occurrence.actions) ⟨frames layer index, history⟩ =
      .call (.receive (.field scalarDomain) site site (context.role 0)) (fun value =>
        .call (.observe (.message (origin layer index) (.field scalarDomain value))) fun _ =>
          .done (verifierCoefficientState (some (coefficients ++ [value])),
            ⟨frames layer index, history ++ [.message (origin layer index) (.field scalarDomain value)]⟩)) := by
  rw [verifierCoefficient_process {} 1 rfl (by decide) index none (some coefficients)]
  simp only [verifierCoefficientProcess, PIR.Process.interpret_bind, Original.fold_bind,
    Original.fold_actions, PIR.Process.interpretState, GkrRoundsReading.append_plain,
    PIR.Process.bind, Original.operations]
  erw [Original.validator_receive (routing handle .validator) ⟨frames layer index, history⟩
    site scalarDomain 0 (origin layer index) rfl routes.message]
  rfl

def validatorCallback (handle offset layerRef layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (layerRead : captured[layerRef]? = some (.data (.index layer)))
    (coefficients : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .validator handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ValidatorReturns layer) (outer layer) "s91" index
        [offset + 8, offset + 7] [.data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        ((coefficientFn (F := F) (G := G) {} 1
          (.cons (some index) ((verifierCoefficientState (some coefficients)).append (.cons none .nil)))).interpret
            Occurrence.actions) ⟨frames layer index, history⟩)
      (validatorBody (ringModel F G) offset layerRef
        (captured ++ .data (.index index) :: carried coefficients history)) := by
  have inside : layerRef < offset := by
    rw [← size]
    exact (List.getElem?_eq_some_iff.mp layerRead).choose
  rw [validator_source handle layer index coefficients history routes]
  simp only [validatorBody, Domain.View.sequence]
  derive_artifact_binding normalizing (
    repeat' (first
      | (fail_if_no_progress simp (disch := omega) only
          [List.append_assoc, List.getElem?_append_left, List.getElem?_append_right, size, inside, layerRead,
           Nat.add_sub_cancel_left, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ])
      | (fail_if_no_progress normalize_artifact_operations
          [GkrDomainHelpers.append (F := F) (G := G), compiled_origin] unfolding [carried])))
    solving (first
      | solve | simp [ArtifactBinding.Captures, List.append_assoc]
      | (unfold Original.IterationReturns ValidatorReturns
         refine ⟨rfl, _, ?_, rfl, _, _, rfl, rfl⟩
         simp (disch := omega) [Domain.read, carried, List.getElem?_append_left, List.getElem?_append_right, size,
           Nat.add_sub_cancel_left, Environment.prepend, Values.get, Bind.bind, Option.bind]; rfl))


def ProducerReturns (layer : Nat)
    (source : Values (Component (assignment F G)) coefficientState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ history, source = (proverCoefficientState, ⟨outer layer, history⟩) ∧
    frame = [.transcript context.suite history]

def producerSuffix (model : DomainModel) (offset layerRef : Nat) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.send site site (context.role 1) (offset + 2) []) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 3) layerRef [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 4) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite template
    (offset + 1) (offset + 2) (offset + 5) [.transcript context.suite]) Domain.View.empty

def producerBody (model : DomainModel) (offset layerRef lineRef : Nat) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.helper model GkrSourceViews.program
    GkrSourceBodies.helper70Helper.name [lineRef, offset] [.data (.field scalarDomain)])
    (producerSuffix model offset layerRef)

def fieldResult (result : Values (assignment F G) [.field scalarDomain]) :
    Domain.Environment (uniformCarriers F G) := [.data (.field scalarDomain (result.get .here))]

theorem helper70_present : GkrSourceBodies.helper70Helper ∈
    GkrSourceViews.program.payload.definitions.map CheckedDefinition.helper := by decide +kernel

/-- The producer's read-after call is certified for every closed outcome. No
line coefficient, helper success or precomputed packet is an input premise. -/
def producerCallback (handle offset layerRef lineRef layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (layerRead : captured[layerRef]? = some (.data (.index layer)))
    (line : List F) (lineRead : captured[lineRef]? = some (.data (.vector scalarDomain line)))
    (history : Domain.History (uniformCarriers F G))
    (routes : Routes .producer handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ProducerReturns layer) (outer layer) "s91" index
        [offset + 6] [.transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        ((coefficientFn (F := F) (G := G) {} 0
          (.cons (some index) (proverCoefficientState.append (.cons (some line) .nil)))).interpret
            Occurrence.actions) ⟨frames layer index, history⟩)
      (producerBody (ringModel F G) offset layerRef lineRef
        (captured ++ [.data (.index index), .transcript context.suite history])) := by
  have layerInside : layerRef < offset := by
    rw [← size]; exact (List.getElem?_eq_some_iff.mp layerRead).choose
  have lineInside : lineRef < offset := by
    rw [← size]; exact (List.getElem?_eq_some_iff.mp lineRead).choose
  rw [proverCoefficient_process {} 0 rfl (by decide) index (some line)]
  simp only [proverCoefficientProcess, PIR.Process.interpret_bind, Original.fold_bind,
    Original.fold_done, PIR.Process.bind_assoc, producerBody, Domain.View.sequence]
  apply Original.Simulation.checkpoint
  · simp [ArtifactBinding.Captures]
  apply (GkrOriginalHelpers.certificate (routing handle .producer) GkrSourceBodies.helper70Helper
    helper70_present (.cons line (.cons index .nil)) _ rfl fieldResult
    (by intro result; cases result with | cons value rest => cases rest; rfl)
    (by intro result; rfl) ⟨frames layer index, history⟩ _ [lineRef, offset] ?_).bind
  · intro process frame equal
    subst frame
    simp [ArtifactBinding.Captures]
  · intro original final related
    apply Classical.choice
    obtain ⟨result, rfl, rfl⟩ := related
    cases result with | cons value rest =>
      cases rest
      refine ⟨?_⟩
      simp only [producerSuffix, Domain.View.sequence, Original.fold_actions,
        PIR.Process.interpretState, Original.operations]
      derive_artifact_binding normalizing (
        repeat' (first
          | (fail_if_no_progress simp (disch := omega) only
              [List.append_assoc, List.getElem?_append_left, List.getElem?_append_right, size, layerInside, layerRead,
               Nat.add_sub_cancel_left, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ])
          | (fail_if_no_progress normalize_artifact_operations [compiled_origin] unfolding
              [Original.send, routes.message, fieldResult, Values.get, Ty.isService,
               show (routing handle .producer).context = context from rfl,
               GkrSourceProtocol.context, Context.fiatShamir,
               show (routing handle .producer).mode = .producer from rfl,
               show (routing handle .producer).context.producer = 0 from rfl,
               Original.record, lineCoefficientSite, qualifyProtocolSite, id_eq, ProtocolContext.roles])))
        solving (first
          | solve | simp [ArtifactBinding.Captures, List.append_assoc]
          | (unfold Original.IterationReturns ProducerReturns
             refine ⟨rfl, _, ?_, rfl, _, rfl, rfl⟩
             simp (disch := omega) [Domain.read, fieldResult, List.getElem?_append_left, List.getElem?_append_right, size,
               Nat.add_sub_cancel_left, Environment.prepend, Values.get, Bind.bind, Option.bind]; rfl))
  · simp (disch := omega) [Domain.read, List.getElem?_append_left, List.getElem?_append_right, size, lineInside, lineRead,
      Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_some, Option.pure_def]
    exact (List.getElem_of_getElem? lineRead).choose_spec

end ZkcExamples.Construction.GkrOriginalCoefficient
