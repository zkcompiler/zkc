module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.OkamotoProof

@[expose] public section

/-! Generated artifacts of the subject `okamoto-proof` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes.
Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Okamoto
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.OkamotoProof.snapshot
  participant := ZkcExamples.Construction.OkamotoProof.participant
  publics := [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1"]
  program := none

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.OkamotoProof.imported
  compiled := ZkcExamples.Construction.OkamotoProof.compiled
  selection := ZkcExamples.Construction.OkamotoProof.selection
  selected := ZkcExamples.Construction.OkamotoProof.selected
  checked := ZkcExamples.Construction.OkamotoProof.selection_checked
  publics := by decide +kernel

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:440eb60d922d4c53048d7ff1b38ba4e90dfd040306892f4cf1b638b77ca73eaf", "example::Proof", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:8ad7d8de5dcc0a232582cecb67fba8dd472b07b7eafa770c2e90823b130457b0"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:8ad7d8de5dcc0a232582cecb67fba8dd472b07b7eafa770c2e90823b130457b0"⟩]⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.Okamoto
