module

public import ZkcExamples.Construction.GkrOriginalRounds
public import ZkcExamples.Construction.GkrSourceRouting

@[expose] public section
/-! Instantiation of the structural primitive obligations using the source
owner's universal occurrence-resolution proofs. No route is an endpoint premise. -/
set_option autoImplicit false
namespace ZkcExamples.Construction.GkrOriginalRoutes
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Construction GkrSourceRouting

theorem output (mode : Domain.Mode) (handle index : Nat) :
    GkrOriginalOutput.Routes mode handle index :=
  ⟨output_draw handle index mode, output_message handle index mode,
    output_delivery handle index mode⟩

theorem coefficient (mode : Domain.Mode) (handle layer index : Nat) :
    GkrOriginalCoefficient.Routes mode handle layer index :=
  ⟨coefficient_message handle layer index mode⟩

theorem round_site (side : Side) (packet : Fin 3) :
    GkrVerifier.roundSite (roundContext side) (toString packet.val) =
      GkrOriginalRounds.messageSite side packet := by
  simp only [← protocolSiteDecimal_eq_toString]
  fin_cases packet <;> cases side <;> decide +kernel

theorem round (mode : Domain.Mode) (side : Side) (handle layer index : Nat) :
    GkrOriginalRounds.Routes mode side handle layer index where
  message packet := by
    simpa only [round_site] using round_message side packet handle layer index mode
  draw := round_draw side handle layer index mode
  delivered := round_delivery_message side handle layer index mode
  delivery := round_delivery side handle layer index mode

end ZkcExamples.Construction.GkrOriginalRoutes
