module

public import ZkcExamples.Construction.GkrSourceRouting
public import ZkcSecurity.Realizations.Gkr.HonestProducerCurrent

@[expose] public section

/-! Exact current-source route records for the computed honest producer.
Every route is discharged from the same source-selected templates used by the
full validator correspondence. Coefficients retain their own inner index. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalRoutes
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Construction.GkrSourceRouting
open HonestProducerSource

def output (handle index : Nat) :
    HonestProducer.OutputRoutes (routing handle) {} [⟨"s37", index⟩] handle where
  producer := rfl
  validator := rfl
  drawOrigin := Domain.atCoordinates (context.query (GkrSourceCallbacks.outputSite {})
    (.draw "bls12-381.fr")) [index]
  deliveryOrigin := Domain.atCoordinates (context.message (GkrSourceCallbacks.outputDeliverySite {}) 1 0) [index]
  queryRoute := output_draw handle index .validator
  deliveryRoute := output_delivery handle index .validator
  sentRoute := output_message handle index .validator
  request := OccurrenceResolution.atCoordinates_request _ _

def round (side : Side) (handle layer index : Nat) :
    HonestProducerPair.RoundRoutes (routing handle) (roundContext side)
      (roundFrames side layer index) handle where
  producer := by cases side <;> rfl
  validator := by cases side <;> rfl
  zeroOrigin := Domain.atCoordinates (context.message (GkrVerifier.roundSite (roundContext side) "0") 0 1)
    [layer, index]
  oneOrigin := Domain.atCoordinates (context.message (GkrVerifier.roundSite (roundContext side) "1") 0 1)
    [layer, index]
  twoOrigin := Domain.atCoordinates (context.message (GkrVerifier.roundSite (roundContext side) "2") 0 1)
    [layer, index]
  drawOrigin := Domain.atCoordinates (context.query (GkrVerifier.challengeSite (roundContext side))
    (.draw "bls12-381.fr")) [layer, index]
  deliveryOrigin := Domain.atCoordinates (context.message (GkrVerifier.deliverySite (roundContext side)) 1 0)
    [layer, index]
  zeroRoute := by
    have label : toString (0 : Nat) = "0" := by rw [← protocolSiteDecimal_eq_toString]; cbv
    change (routing handle).message (roundFrames side layer index)
      (GkrVerifier.roundSite (roundContext side) "0") 0 1 = _
    simpa only [label] using round_message side ⟨0, by decide⟩ handle layer index .validator
  oneRoute := by
    have label : toString (1 : Nat) = "1" := by rw [← protocolSiteDecimal_eq_toString]; cbv
    change (routing handle).message (roundFrames side layer index)
      (GkrVerifier.roundSite (roundContext side) "1") 0 1 = _
    simpa only [label] using round_message side ⟨1, by decide⟩ handle layer index .validator
  twoRoute := by
    have label : toString (2 : Nat) = "2" := by rw [← protocolSiteDecimal_eq_toString]; cbv
    change (routing handle).message (roundFrames side layer index)
      (GkrVerifier.roundSite (roundContext side) "2") 0 1 = _
    simpa only [label] using round_message side ⟨2, by decide⟩ handle layer index .validator
  queryRoute := round_draw side handle layer index .validator
  deliveryRoute := round_delivery side handle layer index .validator
  sentRoute := round_delivery_message side handle layer index .validator
  request := OccurrenceResolution.atCoordinates_request _ _

def layer (handle index : Nat) :
    HonestProducerObservedLayers.Routes (routing handle) {} [⟨"s57", index⟩] handle currentLayerSites where
  producer := rfl
  validator := rfl
  constantOrigin := Domain.atCoordinates (context.message (GkrSourceCallbacks.lineConstantSite {}) 0 1) [index]
  drawOrigin := Domain.atCoordinates (context.query (GkrSourceCallbacks.lineChallengeSite {})
    (.draw "bls12-381.fr")) [index]
  deliveryOrigin := Domain.atCoordinates (context.message (GkrSourceCallbacks.lineDeliverySite {}) 1 0) [index]
  constantRoute := constant_message handle index .validator
  queryRoute := line_draw handle index .validator
  deliveryRoute := line_delivery handle index .validator
  sentRoute := line_message handle index .validator
  request := OccurrenceResolution.atCoordinates_request _ _
  left := fun roundIndex => round .left handle index roundIndex
  right := fun roundIndex => round .right handle index roundIndex
  packetOrigin := fun coefficientIndex =>
    Domain.atCoordinates (context.message (GkrSourceCallbacks.lineCoefficientSite {}) 0 1) [index, coefficientIndex]
  coefficient := fun coefficientIndex => coefficient_message handle index coefficientIndex .validator

end ZkcSecurity.Realizations.Gkr.CanonicalRoutes
