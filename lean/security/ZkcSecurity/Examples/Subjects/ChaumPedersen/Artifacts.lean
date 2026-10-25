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
  ⟨"sha256:6365ec039c6a69c630fec6a233b7f0e19519d12c8bf2766daddf1ffbc20b429b", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:9a304847881b4459693e6e4a3e0789a9ec306f2ae729e4310c4efcacedf58f22"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:9a304847881b4459693e6e4a3e0789a9ec306f2ae729e4310c4efcacedf58f22"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:13e370c27590e35d2d3a799aed2592a39b8594596a402bda35115c7823ef7218",
    "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.ChaumPedersen
