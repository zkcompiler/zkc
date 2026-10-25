module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.SchnorrAndArtifact
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
  occurrences := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 (.cons value3 .nil))) => exact ZkcExamples.Construction.SchnorrAndProof.compiled_transform challenge value0 value1 value2 value3 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:caa1f6f2253041b1592fe89382e19e68e6da204292e0fbe054e00c110dcb41b8", "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:b729a1578eb23887e0ad9f21588336bf68891c7ea413669aa99e8481b3033dc3"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:b729a1578eb23887e0ad9f21588336bf68891c7ea413669aa99e8481b3033dc3"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:8cadb7843dcf604e9f735471d9344dfab28566f21253ed09dbe616170a474966",
    "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.SchnorrAnd
