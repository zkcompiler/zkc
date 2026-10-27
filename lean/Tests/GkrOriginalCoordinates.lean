module

public import ZkcExamples.Construction.GkrOriginalRoutes

@[expose] public section
set_option autoImplicit false
namespace Tests.GkrOriginalCoordinates
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction GkrSourceRouting

/-- An inner round frame cannot stand in for the coefficient frame. -/
theorem wrong_coefficient_frame (layer coefficient : Nat) :
    OccurrenceResolution.matchesOccurrence snapshot context
      (context.message GkrOriginalCoefficient.site 0 1)
      [⟨"s57", layer⟩, ⟨"s9", coefficient⟩] GkrOriginalCoefficient.template = false := by
  have sites : SourceOccurrences.repeatSites GkrOriginalCoefficient.template = ["s57", "s91"] := rfl
  have different : (["s57", "s91"] == ["s57", "s9"]) = false := rfl
  simp only [OccurrenceResolution.matchesOccurrence, sites, List.map_cons, List.map_nil,
    different, Bool.and_false, Bool.false_and]

/-- An extra coordinate cannot silently alter a layer-only challenge. -/
theorem extra_line_coordinate (layer extra : Nat) :
    Domain.queryOrigin context context.suite "bls12-381.fr" (templates[14]'(by decide +kernel))
      [layer, extra] = none := by kernel_rfl

/-- The fully indexed coefficient resolver rejects both missing coordinates. -/
theorem missing_coefficient_coordinates :
    Domain.templateOrigin context GkrOriginalCoefficient.template [] = none := by kernel_rfl

end Tests.GkrOriginalCoordinates
