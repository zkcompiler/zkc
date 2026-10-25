module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.SumcheckArtifact
public import ZkcExamples.Construction.SumcheckProof
public import ZkcExamples.Executable.SumcheckProofProgramData

@[expose] public section

/-! Generated artifacts of the subject `sumcheck` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes
and the executable validator of the deployed program. Every fact below is a
generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.SumcheckProof.snapshot
  participant := ZkcExamples.Construction.SumcheckProof.participant
  publics := [.vector "bls12-381.fr", .field "bls12-381.fr", .index]
  program := some ZkcExamples.Executable.SumcheckProofProgramData.validator

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.SumcheckProof.imported
  compiled := ZkcExamples.Construction.SumcheckProof.compiled
  selection := ZkcExamples.Construction.SumcheckProof.selection
  selected := ZkcExamples.Construction.SumcheckProof.selected
  checked := ZkcExamples.Construction.SumcheckProof.selection_checked
  publics := by decide +kernel
  occurrences := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 .nil)) => exact ZkcExamples.Construction.SumcheckProof.compiled_transform challenge value0 value1 value2 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:649933cf9561b62b081e958442c1479024ed6fae925bdf88c58c1ecf5a51076a", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:ef7dd8da96b1da7abf94876491bf525a639ee4a4662030e141b25299f48abe7a"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:ef7dd8da96b1da7abf94876491bf525a639ee4a4662030e141b25299f48abe7a"⟩, ⟨"verifier-program", "sha256:16a63417a62f65de160d326542dd881df74e2b805ec73dee945f0e95dc0640d0"⟩]⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  [{ label := "reduce.challenge", native := "apply_18_label_726564756365_label_6368616c6c656e6765",
      delivery := "apply_18_label_726564756365_label_64656c6976657279_0", selected := by decide +kernel,
      request := compiled.context.request.getD (.draw ""), requestSelected := by decide +kernel }]

end ZkcSecurity.Examples.Subjects.Sumcheck
