import Tests.StructuredOccurrenceNormalForm
import ZkcTools.StructuredSource.Discovery.Search

/-! Executable controls for untrusted discovery metadata. These are not
independence or security theorems. The source itself is already admitted by the
occurrence-normalization fixture; this query goes through admission again. -/
namespace Tests.ReferenceDiscoveryDependencies
open Zkc.Source.Structured ZkcTools.StructuredSource.Discovery

def view : Except String View := do
  let program ← check Tests.StructuredOccurrenceNormalForm.snapshot
  buildView program .joint 0

/- The source has nested repeats and multiple applications returning draws. -/
#guard (view.toOption.map fun view =>
  let compounds := view.nodes.filter fun node => node.tag == "call" || node.tag == "repeat"
  compounds.length >= 4 && compounds.all fun node =>
    !node.results.isEmpty && node.results.all (·.unknownDependencies)) == some true

/- The source/context identity of each application remains available. -/
#guard (view.toOption.map fun view =>
  let calls := view.nodes.filter (·.tag == "call")
  calls.length == 2 && calls.all (fun node => !node.address.region.isEmpty)) == some true

/- Seeing the honest producer is not a conditional randomness theorem. -/
#guard commonObligations.contains "challenge-prefix-fixation"
#guard commonObligations.contains "conditional-challenge-distribution"
#guard commonObligations.contains "reference-dependency-summary"

end Tests.ReferenceDiscoveryDependencies
