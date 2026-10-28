module

public import ZkcExamples.Construction.GkrOriginalRoutes

@[expose] public section
/-! Primitive line actions inside the exact enclosing layer coordinate. These
are source-route instances, shared by the producer and validator assemblies. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrOriginalLine
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceRouting
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev constantSite := "label_6c696e655f636f6e7374616e74_0"
abbrev challengeSite := "label_6c696e655f6368616c6c656e6765"
abbrev deliverySite := "label_6c696e655f64656c6976657279_0"
abbrev frames (layer : Nat) : Original.Frames := [⟨"s57", layer⟩]
abbrev constant (layer : Nat) := Domain.atCoordinates (context.message constantSite 0 1) [layer]
abbrev draw (layer : Nat) := Domain.atCoordinates (context.query challengeSite (.draw scalarDomain)) [layer]
abbrev delivery (layer : Nat) := Domain.atCoordinates (context.message deliverySite 1 0) [layer]

theorem compiled_constant (layer : Nat) :
    Domain.templateOrigin context template12 [layer] = some (constant layer) := by kernel_rfl
theorem compiled_draw (layer : Nat) :
    Domain.queryOrigin context context.suite scalarDomain template14 [layer] = some (draw layer) := by kernel_rfl
theorem compiled_delivery (layer : Nat) :
    Domain.templateOrigin context template15 [layer] = some (delivery layer) := by kernel_rfl
theorem draw_request (layer : Nat) : (draw layer).request = some (.draw scalarDomain) := rfl

theorem validator_receive (handle layer : Nat) (history : Domain.History (uniformCarriers F G)) :
    Original.receive (routing handle .validator) ⟨frames layer, history⟩
      (.field scalarDomain) constantSite 0 =
      .call (.receive (.field scalarDomain) constantSite constantSite (context.role 0)) (fun value =>
        .call (.observe (.message (constant layer) (.field scalarDomain value))) fun _ =>
          .done (value, ⟨frames layer, history ++ [.message (constant layer) (.field scalarDomain value)]⟩)) :=
  Original.validator_receive (routing handle .validator) ⟨frames layer, history⟩
    constantSite scalarDomain 0 (constant layer) rfl (constant_message handle layer .validator)

theorem producer_send (handle layer : Nat) (history : Domain.History (uniformCarriers F G)) (value : F) :
    Original.send (routing handle .producer) ⟨frames layer, history⟩ (.field scalarDomain) constantSite 1 value =
      .call (.send constantSite constantSite (context.role 1) (.field scalarDomain value)) (fun _ =>
        .call (.observe (.message (constant layer) (.field scalarDomain value))) fun _ =>
          .done ((), ⟨frames layer, history ++ [.message (constant layer) (.field scalarDomain value)]⟩)) := by
  simp only [Original.send, show (routing handle .producer).mode = .producer from rfl,
    show (routing handle .producer).context.producer = 0 from rfl, constant_message,
    Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record]
  rfl

theorem validator_query (handle layer : Nat) (history : Domain.History (uniformCarriers F G)) :
    Original.query (routing handle .validator) ⟨frames layer, history⟩ challengeSite scalarDomain handle =
      .call (.query history (draw layer)) (fun reply =>
        .done (Original.fieldReply (draw layer) scalarDomain rfl reply,
          ⟨frames layer, history ++ [.challenge (draw layer)]⟩)) :=
  Original.public_query (routing handle .validator) ⟨frames layer, history⟩
    challengeSite scalarDomain handle (draw layer) rfl (line_draw handle layer .validator)

theorem validator_send (handle layer : Nat) (history : Domain.History (uniformCarriers F G)) (value : F) :
    Original.send (routing handle .validator) ⟨frames layer, history⟩ (.field scalarDomain) deliverySite 0 value =
      .call (.observe (.message (delivery layer) (.field scalarDomain value))) (fun _ =>
        .done ((), ⟨frames layer, history ++ [.message (delivery layer) (.field scalarDomain value)]⟩)) := by
  simp only [Original.send, show (routing handle .validator).mode = .validator from rfl,
    show (routing handle .validator).context.validator = 1 from rfl, line_message,
    Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record]

theorem producer_receive (handle layer : Nat) (history : Domain.History (uniformCarriers F G)) :
    Original.receive (routing handle .producer) ⟨frames layer, history⟩ (.field scalarDomain) deliverySite 1 =
      .call (.query history (draw layer)) (fun reply =>
        let value := Original.fieldReply (draw layer) scalarDomain rfl reply
        .call (.observe (.message (delivery layer) (.field scalarDomain value))) fun _ =>
          .done (value, ⟨frames layer,
            history ++ [.challenge (draw layer)] ++ [.message (delivery layer) (.field scalarDomain value)]⟩)) :=
  by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    Original.producer_delivery (routing handle .producer) ⟨frames layer, history⟩
    deliverySite scalarDomain 1 (draw layer) (delivery layer) rfl
      (line_delivery handle layer .producer) rfl

end ZkcExamples.Construction.GkrOriginalLine
