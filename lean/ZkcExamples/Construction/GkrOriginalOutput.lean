module

public import Zkc.Construction.OriginalLoop
public import Zkc.Construction.OriginalEffects
public import ZkcExamples.Construction.GkrSourceRoutingData
public import ZkcExamples.Construction.GkrDomainHelpers
public import ZkcExamples.Structured.GkrSourceCallbacks
public meta import Zkc.Construction.ArtifactBindingTactic
public meta import Mathlib.Tactic.FailIfNoProgress

@[expose] public section
/-! One nominal output-loop callback template for both actual GKR roles.
All source optional components, dynamic coordinates and physical yields remain
explicit. The checked source normalizer supplies the callback's source view. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrOriginalOutput
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks GkrSourceRouting
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def role : Domain.Mode → Nat | .producer => 0 | .validator => 1
def service (mode : Domain.Mode) (handle : Nat) : Option Nat :=
  match mode with | .producer => none | .validator => some handle
def values (mode : Domain.Mode) (point : List F) :
    Values (Component (assignment F G)) outputState :=
  match mode with
  | .producer => proverOutputState (some point)
  | .validator => verifierOutputState (some point)

def carried (point : List F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector scalarDomain point), .transcript context.suite history]

def Returns (mode : Domain.Mode)
    (source : Values (Component (assignment F G)) outputState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point history, source = (values mode point, ⟨[], history⟩) ∧ frame = carried point history

def drawTemplate : Template := templates[0]'(by decide +kernel)
def deliveryTemplate : Template := templates[1]'(by decide +kernel)

/-- A parameterized physical layout, checked against each actual generated
callback at instantiation. No root or instruction-count recognizer is used. -/
def body (model : DomainModel) (offset : Nat) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 3) offset [.indices]) <|
  Domain.View.sequence (Domain.View.challenge context context.suite scalarDomain drawTemplate
    (offset + 2) (offset + 4) [.data (.field scalarDomain), .transcript context.suite]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend (offset + 7) offset [.indices]) <|
  Domain.View.sequence (Domain.View.observe context context.suite deliveryTemplate
    (offset + 6) (offset + 5) (offset + 8) [.transcript context.suite]) <|
  Domain.View.sequence (Domain.View.helper model GkrSourceViews.program
    GkrSourceBodies.appendHelper.name [offset + 1, offset + 5] [.data (.vector scalarDomain)])
    Domain.View.empty

abbrev draw (index : Nat) :=
  Domain.atCoordinates (context.query "label_6f7574707574" (.draw scalarDomain)) [index]
abbrev delivery (index : Nat) :=
  Domain.atCoordinates (context.message "label_6f75747075745f64656c6976657279_0" 1 0) [index]

theorem draw_request (index : Nat) : (draw index).request = some (.draw scalarDomain) := rfl

theorem compiled_draw (index : Nat) :
    Domain.queryOrigin context context.suite scalarDomain drawTemplate [index] = some (draw index) := by
  kernel_rfl

theorem compiled_delivery (index : Nat) :
    Domain.templateOrigin context deliveryTemplate [index] = some (delivery index) := by
  kernel_rfl

/-- Primitive source-resolution obligations, owned independently of the
artifact template. These are exact individual routes, never a helper-success
or whole-program correspondence premise. -/
structure Routes (mode : Domain.Mode) (handle index : Nat) : Prop where
  draw : (routing handle mode).draw [⟨"s37", index⟩]
    "label_6f7574707574" scalarDomain handle = some (GkrOriginalOutput.draw index)
  message : (routing handle mode).message [⟨"s37", index⟩]
    "label_6f75747075745f64656c6976657279_0" 1 0 = some (delivery index)
  delivery : (routing handle mode).delivery [⟨"s37", index⟩]
    "label_6f75747075745f64656c6976657279_0" scalarDomain 1 =
      some (GkrOriginalOutput.draw index, GkrOriginalOutput.delivery index)

/-- The source side is the checked original callback, folded with its actual
source routes. Both roles have the same public query and delivered observation. -/
theorem source (mode : Domain.Mode) (handle index : Nat) (point : List F)
    (history : Domain.History (uniformCarriers F G)) (routes : Routes mode handle index) :
    Original.fold (routing handle mode)
      ((outputFn (F := F) (G := G) {} (role mode)
        (.cons (some index) ((values mode point).append (.cons (service mode handle) .nil)))).interpret
          Occurrence.actions) ⟨[⟨"s37", index⟩], history⟩ =
      .call (.query history (draw index)) (fun reply =>
        let value := Original.fieldReply (draw index) scalarDomain (draw_request index) reply
        .call (.observe (.message (delivery index) (.field scalarDomain value))) fun _ =>
          .done (values mode (point ++ [value]),
            ⟨[⟨"s37", index⟩], history ++
              [.challenge (draw index), .message (delivery index) (.field scalarDomain value)]⟩)) := by
  cases mode with
  | producer =>
    simp only [role, service, values]
    rw [proverOutput_process {} 0 rfl (by decide) index none (some point)]
    simp only [proverOutputProcess, PIR.Process.interpret_bind, Original.fold_bind,
      Original.fold_actions, PIR.Process.interpretState, GkrRoundsReading.append_plain,
      PIR.Process.bind, Original.operations]
    erw [Original.producer_delivery (routing handle .producer) _ _ _ 1 _ _ rfl
      routes.delivery rfl]
    rfl
  | validator =>
    obtain ⟨replacement, profile⟩ := Original.Routing.draw_profile routes.draw
    simp only [role, service, values]
    rw [verifierOutput_process {} 1 rfl (by decide) index (some handle) (some point)]
    simp only [verifierOutputProcess, PIR.Process.interpret_bind, Original.fold_bind,
      Original.fold_actions, PIR.Process.interpretState, GkrRoundsReading.append_plain,
      PIR.Process.bind, Original.operations, profile]
    erw [Original.public_query (routing handle .validator) _ _ _ handle _ rfl
      routes.draw]
    simp only [PIR.Process.bind]
    simp only [Original.send,
      show (routing handle .validator).mode = .validator from rfl,
      show (routing handle .validator).context.validator = 1 from rfl,
      show outputDeliverySite {} = "label_6f75747075745f64656c6976657279_0" from rfl,
      id_eq, routes.message, Domain.Payload.ofValue,
      Ty.isService, ↓reduceDIte, Original.record, PIR.Process.bind, List.append_assoc]
    rfl

/-- Every typed reply establishes the exact source return, closing frame,
compiled yield map, transcript and immutable captured prefix. -/
def callback (mode : Domain.Mode) (handle offset index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes mode handle index) :
    Original.Simulation
      (Original.IterationReturns (Returns mode) [] "s37" index
        [offset + 10, offset + 9] [.data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle mode)
        ((outputFn (F := F) (G := G) {} (role mode)
          (.cons (some index) ((values mode point).append (.cons (service mode handle) .nil)))).interpret
            Occurrence.actions) ⟨[⟨"s37", index⟩], history⟩)
      (body (ringModel F G) offset (captured ++ .data (.index index) :: carried point history)) := by
  rw [source mode handle index point history routes]
  simp only [body, Domain.View.sequence]
  derive_artifact_binding normalizing (
    repeat' (first
      | (fail_if_no_progress simp (disch := omega) only
          [List.append_assoc, List.getElem?_append_right, size, Nat.add_sub_cancel_left,
           Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ])
      | (fail_if_no_progress normalize_artifact_operations
          [GkrDomainHelpers.append (F := F) (G := G), compiled_draw, compiled_delivery] unfolding
          [carried, Original.fieldReply, Domain.Raw, draw_request, Request.draw])))
    solving (first
      | solve | simp [ArtifactBinding.Captures, List.append_assoc]
      | (unfold Original.IterationReturns Returns
         refine ⟨rfl, _, ?_, rfl, _, _, rfl, rfl⟩
         simp (disch := omega) [Domain.read, carried, List.getElem?_append_right, size,
           Nat.add_sub_cancel_left, Environment.prepend, Values.get, Bind.bind,
           Option.bind]; rfl))

end ZkcExamples.Construction.GkrOriginalOutput
