module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.ChaumPedersenProof

@[expose] public section

/-! Generated artifacts of the subject `chaum-pedersen` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::EqualityProof` Entry, the types of the inputs its policy
publishes. Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.ChaumPedersen
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::EqualityProof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.ChaumPedersenProof.snapshot
  participant := ZkcExamples.Construction.ChaumPedersenProof.participant
  publics := [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1"]
  program := none

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.ChaumPedersenProof.imported
  compiled := ZkcExamples.Construction.ChaumPedersenProof.compiled
  selection := ZkcExamples.Construction.ChaumPedersenProof.selection
  selected := ZkcExamples.Construction.ChaumPedersenProof.selected
  checked := ZkcExamples.Construction.ChaumPedersenProof.selection_checked
  publics := by decide +kernel

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:ef66cde675242086d335705bc59d7a70c4ae41771627cc6e4575a7134651aa6a", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:d879047e4d385d5b4ab40c20173504580352826f5a2f0dadf807ab8d56be5eb8"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:d879047e4d385d5b4ab40c20173504580352826f5a2f0dadf807ab8d56be5eb8"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:f5d3a2647306748758c9bf9a9cf75fe5e77cba97188707886b781c66b78a827d",
    "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.ChaumPedersen
