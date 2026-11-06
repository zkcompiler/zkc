module

public import ZkcSecurity.Claims.Subject
public import ZkcTools.ConstructionBindings.Admission
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

-- Generated connection types traverse nested occurrence certificates.
set_option maxRecDepth 4096
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
  sourceConnection := some ⟨ZkcExamples.Construction.SumcheckProof.sourceConnected⟩

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 .nil)) => exact ZkcExamples.Construction.SumcheckProof.compiled_transform challenge value0 value1 value2 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:76491dbfe0d0d4ce888fe45e0b7bfe329ae6446201a1bca31ad864304035c97f", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:2443672f4de15c8fbc2cde0400ef343ff08637c40b14fded6d6d716ee8cad54b"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:2443672f4de15c8fbc2cde0400ef343ff08637c40b14fded6d6d716ee8cad54b"⟩, ⟨"verifier-program", "sha256:0eac8edf476a57ed06ef1ce4f3ed6fa18e90a85e4aac3c83ef7e3e5f5a275762"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:76491dbfe0d0d4ce888fe45e0b7bfe329ae6446201a1bca31ad864304035c97f",
    "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  [{ label := "reduce.challenge", native := "apply_18_label_726564756365_label_6368616c6c656e6765",
      delivery := "apply_18_label_726564756365_label_64656c6976657279_0", selected := by decide +kernel,
      request := compiled.context.request.getD (.draw ""), requestSelected := by decide +kernel }]

end ZkcSecurity.Examples.Subjects.Sumcheck
