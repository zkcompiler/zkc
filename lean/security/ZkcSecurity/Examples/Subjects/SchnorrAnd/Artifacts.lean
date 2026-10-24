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
  ⟨"sha256:38886e48c95e08ed0368765f6c4e3b6b8a8927007ad5a3781ecf11d436abf420", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:20c88621b68939166296bc2930e1bea4e09639256324390f09af8c4e4e8a983a"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:20c88621b68939166296bc2930e1bea4e09639256324390f09af8c4e4e8a983a"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:4e27a0515ffb7205b4e9c2a96114c00b1f4c9328a61707a7462e5a2beb78545e",
    "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.SchnorrAnd
