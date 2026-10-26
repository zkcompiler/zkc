module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.SchnorrArtifact
public import ZkcExamples.Construction.SchnorrProof
public import ZkcExamples.Executable.SchnorrProofProgramData

@[expose] public section

/-! Generated artifacts of the subject `schnorr` and their checked facts. Regenerate
with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes
and the executable validator of the deployed program. Every fact below is a
generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.SchnorrProof.snapshot
  participant := ZkcExamples.Construction.SchnorrProof.participant
  publics := [.group "bls12-381.g1", .group "bls12-381.g1"]
  program := some ZkcExamples.Executable.SchnorrProofProgramData.validator

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.SchnorrProof.imported
  compiled := ZkcExamples.Construction.SchnorrProof.compiled
  selection := ZkcExamples.Construction.SchnorrProof.selection
  selected := ZkcExamples.Construction.SchnorrProof.selected
  checked := ZkcExamples.Construction.SchnorrProof.selection_checked
  publics := by decide +kernel
  occurrences := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 .nil) => exact ZkcExamples.Construction.SchnorrProof.compiled_transform challenge value0 value1 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:96e7911cc0127e0d751223fec8d3d4fb6f2b6f518f1fd884290251e35893be4a", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:19a0425a0933930417ecc530361d3d11775e88f52ae110229976dbce4eb236d6"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:19a0425a0933930417ecc530361d3d11775e88f52ae110229976dbce4eb236d6"⟩, ⟨"verifier-program", "sha256:e4e3ceccb896909a93fbf4711b60481a2f89ccea7a5c26ecc244e10c1f59efd5"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:21d6dd8665904f0b0b0faf43f057f61c2fae5b5b12f0191e40fd88bda8b72c2e",
    "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.Schnorr
