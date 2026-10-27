module

public import ZkcExamples.Construction.GkrSourceRoutingChecks
public import Zkc.Construction.Uniform.OccurrenceSourceProcess
public import Zkc.Construction.OccurrenceReindex

@[expose] public section

/-! Source-owned delivery and occurrence routes for the current GKR entry.
Discovery proposes paths; the existing source resolver checks each path and
its exact dynamic repeat stack before any nominal oracle is called. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrSourceRouting
open Zkc.Source Zkc.Source.Structured Zkc.Construction

@[simp] theorem message_coordinates (ctx : Context) (site : String) (sender receiver : Nat)
    (coordinates : List Nat) :
    (Domain.atCoordinates (ctx.message site sender receiver) coordinates).withoutCoordinates =
      ctx.message site sender receiver :=
  Origin.withoutCoordinates_atCoordinates _ _ rfl

@[simp] theorem query_coordinates (ctx : Context) (site : String) (request : Request)
    (coordinates : List Nat) :
    (Domain.atCoordinates (ctx.query site request) coordinates).withoutCoordinates =
      ctx.query site request :=
  Origin.withoutCoordinates_atCoordinates _ _ rfl

/-- The dynamic coordinates remain part of the nominal key at the public draw. -/
theorem output_draw (handle index : Nat) (mode : Domain.Mode) :
    (routing handle mode).draw [⟨"s37", index⟩] "label_6f7574707574" "bls12-381.fr" handle =
      some (Domain.atCoordinates (context.query "label_6f7574707574" (.draw "bls12-381.fr")) [index]) := by
  have ground : (routing handle mode).draw ([⟨"s37", 0⟩]) "label_6f7574707574" "bls12-381.fr" handle =
      some (Domain.atCoordinates (context.query "label_6f7574707574" (.draw "bls12-381.fr")) [0]) := by
    unfold Original.Routing.draw
    rw [ite_eq_left ⟨rfl, rfl⟩]
    change OccurrenceResolution.resolve snapshot context _ _ templates = _
    unfold OccurrenceResolution.resolve
    rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
    cbv
  have equation := Original.Routing.draw_reindex (routing handle mode) ([⟨"s37", 0⟩]) ([⟨"s37", index⟩])
    (by rfl) "label_6f7574707574" "bls12-381.fr" handle
  rw [ground] at equation
  simpa only [Option.map_some, query_coordinates, roundFrames, List.map_cons, List.map_nil] using equation

theorem output_message (handle index : Nat) (mode : Domain.Mode) :
    (routing handle mode).message [⟨"s37", index⟩]
      "label_6f75747075745f64656c6976657279_0" 1 0 =
      some (Domain.atCoordinates (context.message "label_6f75747075745f64656c6976657279_0" 1 0) [index]) := by
  have ground := output_message_ground
  have equation := Original.Routing.message_reindex (routing 0) ([⟨"s37", 0⟩]) ([⟨"s37", index⟩]) (by rfl) "label_6f75747075745f64656c6976657279_0" 1 0
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    List.map_cons, List.map_nil] using equation

theorem output_delivery (handle index : Nat) (mode : Domain.Mode) :
    (routing handle mode).delivery [⟨"s37", index⟩]
      "label_6f75747075745f64656c6976657279_0" "bls12-381.fr" 1 =
      some (Domain.atCoordinates (context.query "label_6f7574707574" (.draw "bls12-381.fr")) [index],
        Domain.atCoordinates (context.message "label_6f75747075745f64656c6976657279_0" 1 0) [index]) := by
  have ground := output_delivery_ground
  have equation := Original.Routing.delivery_reindex (routing 0) ([⟨"s37", 0⟩]) ([⟨"s37", index⟩]) (by rfl) "label_6f75747075745f64656c6976657279_0" "bls12-381.fr" 1
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    List.map_cons, List.map_nil] using equation

theorem round_draw (side : Side) (handle layer index : Nat) (mode : Domain.Mode) :
    (routing handle mode).draw (roundFrames side layer index)
      (ZkcExamples.Structured.GkrVerifier.challengeSite (roundContext side)) "bls12-381.fr" handle =
      some (Domain.atCoordinates
        (context.query (ZkcExamples.Structured.GkrVerifier.challengeSite (roundContext side)) (.draw "bls12-381.fr"))
        [layer, index]) := by
  have ground : (routing handle mode).draw (roundFrames side 0 0) (ZkcExamples.Structured.GkrVerifier.challengeSite (roundContext side)) "bls12-381.fr" handle =
      some (Domain.atCoordinates (context.query (ZkcExamples.Structured.GkrVerifier.challengeSite (roundContext side)) (.draw "bls12-381.fr")) [0, 0]) := by
    unfold Original.Routing.draw
    rw [ite_eq_left ⟨rfl, rfl⟩]
    change OccurrenceResolution.resolve snapshot context _ _ templates = _
    unfold OccurrenceResolution.resolve
    rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
    cases side <;> cbv
  have equation := Original.Routing.draw_reindex (routing handle mode) (roundFrames side 0 0) (roundFrames side layer index)
    (by rfl) (ZkcExamples.Structured.GkrVerifier.challengeSite (roundContext side)) "bls12-381.fr" handle
  rw [ground] at equation
  simpa only [Option.map_some, query_coordinates, roundFrames, List.map_cons, List.map_nil] using equation

theorem round_message (side : Side) (which : Fin 3) (handle layer index : Nat) (mode : Domain.Mode) :
    (routing handle mode).message (roundFrames side layer index)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext side) (toString which.val)) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext side) (toString which.val)) 0 1)
        [layer, index]) := by
  have ground := round_message_ground side which
  have equation := Original.Routing.message_reindex (routing 0) (roundFrames side 0 0) (roundFrames side layer index) (by rfl)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext side) (toString which.val)) 0 1
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    roundFrames, List.map_cons, List.map_nil] using equation

theorem round_delivery_message (side : Side) (handle layer index : Nat) (mode : Domain.Mode) :
    (routing handle mode).message (roundFrames side layer index)
      (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) 1 0 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) 1 0)
        [layer, index]) := by
  have ground := round_delivery_message_ground side
  have equation := Original.Routing.message_reindex (routing 0) (roundFrames side 0 0) (roundFrames side layer index) (by rfl)
      (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) 1 0
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    roundFrames, List.map_cons, List.map_nil] using equation

theorem round_delivery (side : Side) (handle layer index : Nat) (mode : Domain.Mode) :
    (routing handle mode).delivery (roundFrames side layer index)
      (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) "bls12-381.fr" 1 =
      some (Domain.atCoordinates
          (context.query (ZkcExamples.Structured.GkrVerifier.challengeSite (roundContext side)) (.draw "bls12-381.fr"))
          [layer, index],
        Domain.atCoordinates
          (context.message (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) 1 0)
          [layer, index]) := by
  have ground := round_delivery_ground side
  have equation := Original.Routing.delivery_reindex (routing 0) (roundFrames side 0 0) (roundFrames side layer index) (by rfl)
      (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) "bls12-381.fr" 1
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    roundFrames, List.map_cons, List.map_nil] using equation

theorem constant_message (handle layer : Nat) (mode : Domain.Mode) :
    (routing handle mode).message [⟨"s57", layer⟩] "label_6c696e655f636f6e7374616e74_0" 0 1 =
      some (Domain.atCoordinates (context.message "label_6c696e655f636f6e7374616e74_0" 0 1) [layer]) := by
  have ground := constant_message_ground
  have equation := Original.Routing.message_reindex (routing 0) ([⟨"s57", 0⟩]) ([⟨"s57", layer⟩]) (by rfl) "label_6c696e655f636f6e7374616e74_0" 0 1
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    roundFrames, List.map_cons, List.map_nil] using equation

theorem coefficient_message (handle layer index : Nat) (mode : Domain.Mode) :
    (routing handle mode).message [⟨"s57", layer⟩, ⟨"s91", index⟩]
      "label_6c696e655f636f656666696369656e74_0" 0 1 =
      some (Domain.atCoordinates (context.message "label_6c696e655f636f656666696369656e74_0" 0 1) [layer, index]) := by
  have ground := coefficient_message_ground
  have equation := Original.Routing.message_reindex (routing 0) ([⟨"s57", 0⟩, ⟨"s91", 0⟩]) ([⟨"s57", layer⟩, ⟨"s91", index⟩]) (by rfl) "label_6c696e655f636f656666696369656e74_0" 0 1
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    roundFrames, List.map_cons, List.map_nil] using equation

theorem line_draw (handle layer : Nat) (mode : Domain.Mode) :
    (routing handle mode).draw [⟨"s57", layer⟩] "label_6c696e655f6368616c6c656e6765" "bls12-381.fr" handle =
      some (Domain.atCoordinates (context.query "label_6c696e655f6368616c6c656e6765" (.draw "bls12-381.fr")) [layer]) := by
  have ground : (routing handle mode).draw ([⟨"s57", 0⟩]) "label_6c696e655f6368616c6c656e6765" "bls12-381.fr" handle =
      some (Domain.atCoordinates (context.query "label_6c696e655f6368616c6c656e6765" (.draw "bls12-381.fr")) [0]) := by
    unfold Original.Routing.draw
    rw [ite_eq_left ⟨rfl, rfl⟩]
    change OccurrenceResolution.resolve snapshot context _ _ templates = _
    unfold OccurrenceResolution.resolve
    rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
    cbv
  have equation := Original.Routing.draw_reindex (routing handle mode) ([⟨"s57", 0⟩]) ([⟨"s57", layer⟩])
    (by rfl) "label_6c696e655f6368616c6c656e6765" "bls12-381.fr" handle
  rw [ground] at equation
  simpa only [Option.map_some, query_coordinates, roundFrames, List.map_cons, List.map_nil] using equation

theorem line_message (handle layer : Nat) (mode : Domain.Mode) :
    (routing handle mode).message [⟨"s57", layer⟩] "label_6c696e655f64656c6976657279_0" 1 0 =
      some (Domain.atCoordinates (context.message "label_6c696e655f64656c6976657279_0" 1 0) [layer]) := by
  have ground := line_message_ground
  have equation := Original.Routing.message_reindex (routing 0) ([⟨"s57", 0⟩]) ([⟨"s57", layer⟩]) (by rfl) "label_6c696e655f64656c6976657279_0" 1 0
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    roundFrames, List.map_cons, List.map_nil] using equation

theorem line_delivery (handle layer : Nat) (mode : Domain.Mode) :
    (routing handle mode).delivery [⟨"s57", layer⟩] "label_6c696e655f64656c6976657279_0" "bls12-381.fr" 1 =
      some (Domain.atCoordinates (context.query "label_6c696e655f6368616c6c656e6765" (.draw "bls12-381.fr")) [layer],
        Domain.atCoordinates (context.message "label_6c696e655f64656c6976657279_0" 1 0) [layer]) := by
  have ground := line_delivery_ground
  have equation := Original.Routing.delivery_reindex (routing 0) ([⟨"s57", 0⟩]) ([⟨"s57", layer⟩]) (by rfl) "label_6c696e655f64656c6976657279_0" "bls12-381.fr" 1
  rw [ground] at equation
  simpa only [routing, Original.Routing.message, Original.Routing.delivery,
    Option.map_some, message_coordinates, query_coordinates,
    roundFrames, List.map_cons, List.map_nil] using equation

end ZkcExamples.Construction.GkrSourceRouting
