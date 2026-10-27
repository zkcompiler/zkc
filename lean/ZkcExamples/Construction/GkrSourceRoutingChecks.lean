module

public import ZkcExamples.Construction.GkrSourceRoutingValidity

@[expose] public section

/-! Closed source checks used by universal dynamic route certificates.
Every path is checked against the current snapshot, including def-use delivery.
The arbitrary dynamic-coordinate theorem lives in GkrSourceRouting. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace ZkcExamples.Construction.GkrSourceRouting
open Zkc.Source Zkc.Source.Structured Zkc.Construction

theorem output_message_ground :
    (routing 0).message [⟨"s37", 0⟩]
      "label_6f75747075745f64656c6976657279_0" 1 0 =
      some (Domain.atCoordinates (context.message "label_6f75747075745f64656c6976657279_0" 1 0) [0]) := by
    simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
    rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
    cbv

theorem output_delivery_ground :
    (routing 0).delivery [⟨"s37", 0⟩]
      "label_6f75747075745f64656c6976657279_0" "bls12-381.fr" 1 =
      some (Domain.atCoordinates (context.query "label_6f7574707574" (.draw "bls12-381.fr")) [0],
        Domain.atCoordinates (context.message "label_6f75747075745f64656c6976657279_0" 1 0) [0]) := by
    simp only [routing, Original.Routing.delivery, delivery_candidates,
      output_delivery_candidates, round_delivery_candidates, line_delivery_candidates]
    simp only [pure, Pure.pure, Bind.bind, Option.bind,
      OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
      OccurrenceResolution.matchesOccurrence, template0_valid, template1_valid,
      template5_valid, template6_valid, template10_valid, template11_valid,
      template14_valid, template15_valid]
    cbv

private theorem round_message_left_0 :
    (routing 0).message (roundFrames .left 0 0)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .left) (toString (0 : Nat))) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .left) (toString (0 : Nat))) 0 1)
        [0, 0]) := by
  have index : toString (0 : Nat) = "0" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  simp only [index]
  simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
  rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
  cbv

private theorem round_message_left_1 :
    (routing 0).message (roundFrames .left 0 0)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .left) (toString (1 : Nat))) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .left) (toString (1 : Nat))) 0 1)
        [0, 0]) := by
  have index : toString (1 : Nat) = "1" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  simp only [index]
  simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
  rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
  cbv

private theorem round_message_left_2 :
    (routing 0).message (roundFrames .left 0 0)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .left) (toString (2 : Nat))) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .left) (toString (2 : Nat))) 0 1)
        [0, 0]) := by
  have index : toString (2 : Nat) = "2" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  simp only [index]
  simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
  rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
  cbv

private theorem round_message_right_0 :
    (routing 0).message (roundFrames .right 0 0)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .right) (toString (0 : Nat))) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .right) (toString (0 : Nat))) 0 1)
        [0, 0]) := by
  have index : toString (0 : Nat) = "0" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  simp only [index]
  simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
  rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
  cbv

private theorem round_message_right_1 :
    (routing 0).message (roundFrames .right 0 0)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .right) (toString (1 : Nat))) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .right) (toString (1 : Nat))) 0 1)
        [0, 0]) := by
  have index : toString (1 : Nat) = "1" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  simp only [index]
  simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
  rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
  cbv

private theorem round_message_right_2 :
    (routing 0).message (roundFrames .right 0 0)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .right) (toString (2 : Nat))) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext .right) (toString (2 : Nat))) 0 1)
        [0, 0]) := by
  have index : toString (2 : Nat) = "2" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  simp only [index]
  simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
  rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
  cbv

theorem round_message_ground (side : Side) (which : Fin 3) :
    (routing 0).message (roundFrames side 0 0)
      (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext side) (toString which.val)) 0 1 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.roundSite (roundContext side) (toString which.val)) 0 1)
        [0, 0]) := by
  cases side <;> fin_cases which
  · exact round_message_left_0
  · exact round_message_left_1
  · exact round_message_left_2
  · exact round_message_right_0
  · exact round_message_right_1
  · exact round_message_right_2

theorem round_delivery_message_ground (side : Side) :
    (routing 0).message (roundFrames side 0 0)
      (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) 1 0 =
      some (Domain.atCoordinates
        (context.message (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) 1 0)
        [0, 0]) := by
    cases side
    all_goals
      simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
      rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
      cbv

theorem round_delivery_ground (side : Side) :
    (routing 0).delivery (roundFrames side 0 0)
      (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) "bls12-381.fr" 1 =
      some (Domain.atCoordinates
          (context.query (ZkcExamples.Structured.GkrVerifier.challengeSite (roundContext side)) (.draw "bls12-381.fr"))
          [0, 0],
        Domain.atCoordinates
          (context.message (ZkcExamples.Structured.GkrVerifier.deliverySite (roundContext side)) 1 0)
          [0, 0]) := by
    simp only [routing, Original.Routing.delivery, delivery_candidates,
      output_delivery_candidates, round_delivery_candidates, line_delivery_candidates]
    cases side
    all_goals
      simp only [pure, Pure.pure, Bind.bind, Option.bind,
        OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence, template0_valid, template1_valid,
        template5_valid, template6_valid, template10_valid, template11_valid,
        template14_valid, template15_valid]
      cbv

theorem constant_message_ground :
    (routing 0).message [⟨"s57", 0⟩] "label_6c696e655f636f6e7374616e74_0" 0 1 =
      some (Domain.atCoordinates (context.message "label_6c696e655f636f6e7374616e74_0" 0 1) [0]) := by
    simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
    rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
    cbv

theorem coefficient_message_ground :
    (routing 0).message [⟨"s57", 0⟩, ⟨"s91", 0⟩]
      "label_6c696e655f636f656666696369656e74_0" 0 1 =
      some (Domain.atCoordinates (context.message "label_6c696e655f636f656666696369656e74_0" 0 1) [0, 0]) := by
    simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
    rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
    cbv

theorem line_message_ground :
    (routing 0).message [⟨"s57", 0⟩] "label_6c696e655f64656c6976657279_0" 1 0 =
      some (Domain.atCoordinates (context.message "label_6c696e655f64656c6976657279_0" 1 0) [0]) := by
    simp only [routing, Original.Routing.message, OccurrenceResolution.resolve]
    rw [OccurrenceResolution.filter_validated snapshot context _ _ templates templates_valid]
    cbv

theorem line_delivery_ground :
    (routing 0).delivery [⟨"s57", 0⟩] "label_6c696e655f64656c6976657279_0" "bls12-381.fr" 1 =
      some (Domain.atCoordinates (context.query "label_6c696e655f6368616c6c656e6765" (.draw "bls12-381.fr")) [0],
        Domain.atCoordinates (context.message "label_6c696e655f64656c6976657279_0" 1 0) [0]) := by
    simp only [routing, Original.Routing.delivery, delivery_candidates,
      output_delivery_candidates, round_delivery_candidates, line_delivery_candidates]
    simp only [pure, Pure.pure, Bind.bind, Option.bind,
      OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
      OccurrenceResolution.matchesOccurrence, template0_valid, template1_valid,
      template5_valid, template6_valid, template10_valid, template11_valid,
      template14_valid, template15_valid]
    cbv

end ZkcExamples.Construction.GkrSourceRouting
