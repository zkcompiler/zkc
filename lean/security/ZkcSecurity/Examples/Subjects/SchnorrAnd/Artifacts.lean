module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.SchnorrAndProof

@[expose] public section

/-! Generated artifacts of the subject `schnorr-and` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::AndProof` Entry, the types of the inputs its policy
publishes. Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::AndProof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.SchnorrAndProof.snapshot
  participant := ZkcExamples.Construction.SchnorrAndProof.participant
  publics := [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1"]
  program := none

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.SchnorrAndProof.imported
  compiled := ZkcExamples.Construction.SchnorrAndProof.compiled
  selection := ZkcExamples.Construction.SchnorrAndProof.selection
  selected := ZkcExamples.Construction.SchnorrAndProof.selected
  checked := ZkcExamples.Construction.SchnorrAndProof.selection_checked
  publics := by decide +kernel

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:38886e48c95e08ed0368765f6c4e3b6b8a8927007ad5a3781ecf11d436abf420", "example::AndProof", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:c357922a3b0180891fe68a86398f065f243ec5a9247f0fef075b3a0dcaaeb548"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:c357922a3b0180891fe68a86398f065f243ec5a9247f0fef075b3a0dcaaeb548"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive Entry. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:4e27a0515ffb7205b4e9c2a96114c00b1f4c9328a61707a7462e5a2beb78545e",
    "example::AndInteractive", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.SchnorrAnd
