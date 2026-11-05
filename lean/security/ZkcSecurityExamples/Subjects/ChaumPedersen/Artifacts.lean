module

public import ZkcSecurity.Claims.Subject
public import ZkcTools.ConstructionBindings.Admission
public import ZkcExamples.Construction.ChaumPedersenArtifact
public import ZkcExamples.Construction.ChaumPedersenProof

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
  ⟨"sha256:a6ba24d4b3ea2c887413d37a63697ca964b3c1e71fef2a11aea56db3bade0878", "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:3951d4c414f71d25772c3fd9ff8f118d1c079bda00da5f7f964fc980cdc8e968"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:3951d4c414f71d25772c3fd9ff8f118d1c079bda00da5f7f964fc980cdc8e968"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:ab84f0a2dd82a54c96ebd681499907b131a24b18a9a71578b03c5b831082ff3f",
    "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.ChaumPedersen
