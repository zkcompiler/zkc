import Zkc.Construction.SourceDelivery
import Zkc.Construction.OccurrenceResolution
import ZkcExamples.Construction.SumcheckProofParticipant
import ZkcExamples.Structured.SumcheckSourceData

set_option autoImplicit false
set_option maxRecDepth 20000
namespace Tests.SourceDelivery
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private abbrev snapshot := ZkcExamples.Structured.SumcheckSourceData.snapshot
private abbrev exported := ZkcExamples.Construction.SumcheckProofParticipant.participant
private def context : Context :=
  ⟨exported.policy.entry, ["role00000000", "role00000001"], 0, 1, 3,
    "random.bls12-381.fr/0", some (.draw "bls12-381.fr"), exported.policy.suite,
    exported.policy.draws⟩

private def pair : Option (Template × Template) :=
  let edge := context.draws[0]!
  Zkc.Construction.SourceDelivery.resolve snapshot context edge.1 edge.2
private def query : Template := pair.getD (⟨"missing", [], []⟩, ⟨"missing", [], []⟩) |>.1
private def delivery : Template := pair.getD (⟨"missing", [], []⟩, ⟨"missing", [], []⟩) |>.2
private def origin : Origin := (query.origin context).getD ⟨"missing", [], none⟩
private def frames (index : Nat) : OccurrenceResolution.Frames :=
  (SourceOccurrences.repeatSites query).map (fun site => ⟨site, index⟩)

-- The real source has a call followed by a repeat; no artifact offsets select
-- the original draw or the SSA value delivered to the producer.
example : pair.isSome = true := by decide +kernel
example : Zkc.Construction.SourceDelivery.checked snapshot context query delivery = true := by
  decide +kernel
example : SourceOccurrences.valid snapshot context query = true := by decide +kernel
example : query.repeats = 1 := by decide +kernel
example : OccurrenceResolution.resolve snapshot context origin (frames 0) [query] =
    some (Domain.atCoordinates origin [0]) := by decide +kernel
example : OccurrenceResolution.resolve snapshot context origin (frames 4) [query] =
    some (Domain.atCoordinates origin [4]) := by decide +kernel
example : OccurrenceResolution.resolve snapshot context origin [] [query] = none := by decide +kernel
example : OccurrenceResolution.resolve snapshot context origin [⟨"other-loop", 0⟩] [query] = none := by
  decide +kernel
example : OccurrenceResolution.resolve snapshot context origin (frames 0) [query, query] = none := by
  decide +kernel
example : OccurrenceResolution.resolve snapshot context origin (frames 0) [] = none := by decide +kernel
example : OccurrenceResolution.resolve snapshot { context with service := 0 }
    origin (frames 0) [query] = none := by decide +kernel

-- Def-use identity permits visibility restriction but not arithmetic on the
-- sampled field element, even if that arithmetic would preserve its value.
private def direct : List Structured.Instruction := [
  .instruction (.draw "V" "F") [0] [.field "F"] [] "q",
  .instruction (.exchange "V" "P") [0] [.field "F"] [] "delivery"]
private def restricted : List Structured.Instruction := [
  .instruction (.draw "V" "F") [0] [.field "F"] [] "q",
  .instruction (.restrict ["V"]) [0] [.field "F"] [] "visible",
  .instruction (.exchange "V" "P") [0] [.field "F"] [] "delivery"]
private def changed : List Structured.Instruction := [
  .instruction (.draw "V" "F") [0] [.field "F"] [] "q",
  .instruction (.fieldConstant "F" "0") [] [.field "F"] [] "zero",
  .instruction (.fieldAdd "F") [0, 1] [.field "F"] [] "sum",
  .instruction (.exchange "V" "P") [0] [.field "F"] [] "delivery"]
example : Zkc.Construction.SourceDelivery.atDelivery "delivery" direct [none] = some "q" := rfl
example : Zkc.Construction.SourceDelivery.atDelivery "delivery" restricted [none] = some "q" := rfl
example : Zkc.Construction.SourceDelivery.atDelivery "delivery" changed [none] = none := rfl
example : Zkc.Construction.SourceDelivery.atDelivery "delivery"
    [.instruction (.exchange "V" "P") [0] [.field "F"] [] "delivery"] [none] = none := rfl

#print axioms OccurrenceResolution.resolved_source
#print axioms Zkc.Construction.SourceDelivery.templates_valid
end Tests.SourceDelivery
