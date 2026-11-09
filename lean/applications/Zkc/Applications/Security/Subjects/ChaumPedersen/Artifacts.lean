module

public import Zkc.Verification.Claims.Subject
public import Zkc.Tools.IR.ConstructionBindings.Admission
public import Zkc.Applications.IR.Construction.ChaumPedersenArtifact
public import Zkc.Applications.IR.Construction.ChaumPedersenProof

@[expose] public section

/-! Generated artifacts of the subject `chaum-pedersen` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::EqualityProof` Entry, the types of the inputs its policy
publishes. Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.ChaumPedersen
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

-- Generated connection types traverse nested occurrence certificates.
set_option maxRecDepth 4096
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
  occurrences := by decide +kernel
  sourceConnection := some ⟨ZkcExamples.Construction.ChaumPedersenProof.sourceConnected⟩

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 (.cons value3 .nil))) => exact ZkcExamples.Construction.ChaumPedersenProof.compiled_transform challenge value0 value1 value2 value3 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:04fa943660b53d1276a75e5b8edc930e7220d07e1e712c18d9d98d618bd650f8", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:265da5ae51020bba046641fa030b30443223d881e0add0e0337ea71510c21a1d"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:265da5ae51020bba046641fa030b30443223d881e0add0e0337ea71510c21a1d"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:fb34e76be3a2fea3c20e66abf3e77072fdaa5f718e9586ced8b3dbb911d47980",
    "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.ChaumPedersen
