import Tools.Crypto.Keccak
import Tools.Artifact.Codec
import Tools.Interactive.Sampling
import Tools.Artifact.Runtime
import Tests.Checks

/-! Executable known-answer and boundary checks. These do not claim that
transcript bytes are uniform or that the resulting protocol is secure. -/
set_option autoImplicit false

namespace Tests.OracleSampling
open Tools.Artifact Tools.Interactive
open Lean (Json)
open Tests.Checks

#eval show IO Unit from do
  let checks ← start
  let cases : List (String × String) := [
    ("", "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
    ("abc", "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")]
  for (input, expected) in cases do
    checks.holds (hex (Tools.Crypto.Keccak.hash input.toUTF8) == expected) "Keccak known-answer mismatch"
  let rejected := ByteArray.mk (Array.replicate 64 255)
  checks.holds ((Sampling.coordinates rejected).isEmpty) "rejected words reduced modulo the field"
  let zero := ByteArray.mk (Array.replicate 64 0)
  checks.holds ((Sampling.coordinates zero).length == 16 && (Sampling.extension (Sampling.coordinates zero)).isSome) "accepted extension coordinates lost"
  for bits in [:64] do
    let bound := 2^bits
    checks.holds (Sampling.index rejected bound == .ok (bound-1)) "bounded index mask mismatch"
  for bound in [0,3,5,2^64] do
    checks.holds (Sampling.index zero bound == .error "query-bound") "invalid query bound accepted"
  checks.holds (Sampling.index (zero.extract 0 63) 8 == .error "transcript-challenge-width") "short random block accepted"
  checks.finish "Keccak known answers and sampling boundaries"

private def retryFixture (exhaust : Bool) : Result State := do
  let location : Tools.Artifact.Location := {
    entry := "main", binding := "root", path := [], protocol := "Example", role := "V"
    sourceRole := "V", function := "Draw", operation := "draw" }
  let origin ← treeBytes location.challenge
  let mut history := #[Json.arr #[.str "challenge", .str (hex origin)]]
  let mut answers := #[]
  for i in [:if exhaust then 16 else 2] do
    if i > 0 then history := history.push (.arr #[.str "challenge-continuation"])
    let bytes := ByteArray.mk (Array.replicate 64 (if exhaust || i == 0 then 255 else 0))
    answers := answers.push ⟨← transcriptRequest .empty history Bindings.extensionTranscript,
      .arr #[.str "ok", .str (hex bytes)]⟩
  return {
    cursor := ⟨.empty, 0⟩, root := .empty, configuration := .null
    answers := answers, transcriptBudget := 2 }

#eval show IO Unit from do
  let checks ← start
  let source : Source := ⟨.explicit [], [], [], [], []⟩
  let descriptor : Descriptor := {
    entry := "main", producer := "P", validator := "V", publicBindings := []
    rng := "coins", draws := [("Draw", "draw")], acceptance := 0
    json := .arr #[.null,.null,.null,.null,.null,.null,.null,.str Bindings.extensionTranscript,.str "normalized"] }
  let location : Tools.Artifact.Location := {
    entry := "main", binding := "root", path := [], protocol := "Example", role := "V"
    sourceRole := "V", function := "Draw", operation := "draw" }
  for exhaust in [false, true] do
    let .ok initial := retryFixture exhaust | throw (IO.userError "retry fixture")
    let program : RunM Unit := do
      let _ ← challenge source descriptor location 0
      transcriptMessage (.str "after") (.boolean true)
    let (result, state) := program.run initial
    if exhaust then
      let .error failure := result | throw (IO.userError "rejection limit accepted")
      checks.holds (failure.reason == "exhausted" && failure.detail == "challenge-rejection-limit" && state.draws == 1 && state.transcriptActions == 1 && state.history.size == 16) "rejection exhaustion accounting"
    else
      let .ok () := result | throw (IO.userError "retry charged a second logical action")
      checks.holds (state.draws == 1 && state.transcriptActions == 2 && state.history.size == 3 && state.events.size == 2) "retry event or transition lost"
  checks.finish "challenge retry and rejection accounting"

end Tests.OracleSampling
