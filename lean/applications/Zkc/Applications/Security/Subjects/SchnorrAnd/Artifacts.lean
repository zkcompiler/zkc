module

public import Zkc.Verification.Claims.Subject
public import Zkc.Tools.IR.ConstructionBindings.Admission
public import Zkc.Applications.IR.Construction.SchnorrAndArtifact
public import Zkc.Applications.IR.Construction.SchnorrAndProof

@[expose] public section

/-! Generated artifacts of the subject `schnorr-and` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::AndProof` Entry, the types of the inputs its policy
publishes. Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

-- Generated connection types traverse nested occurrence certificates.
set_option maxRecDepth 4096
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
  occurrences := by decide +kernel
  sourceConnection := some ⟨ZkcExamples.Construction.SchnorrAndProof.sourceConnected⟩

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 (.cons value3 .nil))) => exact ZkcExamples.Construction.SchnorrAndProof.compiled_transform challenge value0 value1 value2 value3 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:6fa64559b149ca006d14362f258e232bdbe56d57993ce9be0839276b6244710b", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:a5676b3562f6f08066f639cae7f2ad8b5a6ff2249914ac42f7865aa5d7894682"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:a5676b3562f6f08066f639cae7f2ad8b5a6ff2249914ac42f7865aa5d7894682"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:28e843170d633d0b682301cfb5b3811e470fd2d4df8f9e2aac739883fd999ac2",
    "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.SchnorrAnd
