module

public import ZkcExamples.Construction.GkrOriginalOutput

@[expose] public section
/-! Refusal controls for the actual nominal output and nested GKR templates.
These check the existing resolvers, without running a second evaluator. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace Tests.GkrOriginalOutput
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction GkrSourceRouting GkrOriginalOutput

theorem missing_output_coordinate :
    Domain.queryOrigin context context.suite "bls12-381.fr" drawTemplate [] = none := by
  kernel_rfl

theorem extra_output_coordinate (index extra : Nat) :
    Domain.queryOrigin context context.suite "bls12-381.fr" drawTemplate [index, extra] = none := by
  kernel_rfl

theorem missing_layer_coordinate (round : Nat) :
    Domain.templateOrigin context (templates[2]'(by decide +kernel)) [round] = none := by
  kernel_rfl

theorem missing_coefficient_coordinate (layer : Nat) :
    Domain.templateOrigin context (templates[13]'(by decide +kernel)) [layer] = none := by
  kernel_rfl

theorem coefficient_coordinates (layer coefficient : Nat) :
    Domain.templateOrigin context (templates[13]'(by decide +kernel)) [layer, coefficient] =
      some (Domain.atCoordinates
        (context.message "label_6c696e655f636f656666696369656e74_0" 0 1) [layer, coefficient]) := by
  kernel_rfl

/-- Equal nesting depth cannot substitute a layer frame for an output frame. -/
theorem wrong_output_site (index : Nat) :
    OccurrenceResolution.matchesOccurrence snapshot context
      (context.query "label_6f7574707574" (.draw "bls12-381.fr")) [⟨"s57", index⟩]
      drawTemplate = false := by
  have sites : SourceOccurrences.repeatSites drawTemplate = ["s37"] := rfl
  have different : (["s37"] == ["s57"]) = false := rfl
  simp only [OccurrenceResolution.matchesOccurrence, sites, List.map_cons, List.map_nil,
    different, Bool.and_false, Bool.false_and]

/-- Both applications retain their qualified static s9 frame beneath s57. -/
theorem left_round_sites :
    SourceOccurrences.repeatSites (templates[2]'(by decide +kernel)) =
      ["s57", qualifyProtocolSite (roundContext .left).applicationPrefix "s9"] := rfl

theorem right_round_sites :
    SourceOccurrences.repeatSites (templates[9]'(by decide +kernel)) =
      ["s57", qualifyProtocolSite (roundContext .right).applicationPrefix "s9"] := rfl

theorem sides_distinct (layer round : Nat) :
    roundFrames .left layer round ≠ roundFrames .right layer round := by
  have different : qualifyProtocolSite (roundContext .left).applicationPrefix "s9" ≠
      qualifyProtocolSite (roundContext .right).applicationPrefix "s9" := by decide +kernel
  intro equal
  have sites := congrArg (fun frames => (frames[1]?).map (·.site)) equal
  simp only [roundFrames, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.some.injEq] at sites
  exact different sites

/-- Even coordinate zero adds a nominal suffix; it is not the root key. -/
theorem zero_is_not_erased (origin : Origin) : Domain.atCoordinates origin [0] ≠ origin := by
  intro equal
  have length := congrArg (fun key => key.event.length) equal
  simp only [Domain.atCoordinates, List.isEmpty_cons, Bool.false_eq_true, ite_false,
    List.length_append, List.length_cons, List.length_nil, List.map_cons,
    List.map_nil] at length
  omega

end Tests.GkrOriginalOutput
