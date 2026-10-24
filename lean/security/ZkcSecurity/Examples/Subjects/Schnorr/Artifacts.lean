module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.SchnorrProof
public import ZkcExamples.Executable.SchnorrProof

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
  program := some ZkcExamples.Executable.SchnorrProof.validator

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.SchnorrProof.imported
  compiled := ZkcExamples.Construction.SchnorrProof.compiled
  selection := ZkcExamples.Construction.SchnorrProof.selection
  selected := ZkcExamples.Construction.SchnorrProof.selected
  checked := ZkcExamples.Construction.SchnorrProof.selection_checked
  publics := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The executable validator, accepted by the lowering rule. -/
def lowering : LoweringEvidence artifacts compiled F G where
  validator := ZkcExamples.Executable.SchnorrProof.validator
  program := rfl
  lowered := ZkcExamples.Executable.SchnorrProof.lowered
  accepted := ZkcExamples.Executable.SchnorrProof.accepted
  prepared := ZkcExamples.Executable.SchnorrProof.prepared
  sorted := ZkcExamples.Executable.SchnorrProof.helpersSorted
  admits statement := by
    match statement with
    | .cons value0 (.cons value1 .nil) => exact ZkcExamples.Executable.SchnorrProof.admitted value0 value1

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:7c4214ba8b6291c17f70289eda113d07b9d5a25c95aa1e3e9e1986189559364e", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:06815be04bad322a8148c076445cbf9d981b16c9cde0996b3af7ccb8e47c1ca4"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:06815be04bad322a8148c076445cbf9d981b16c9cde0996b3af7ccb8e47c1ca4"⟩, ⟨"verifier-program", "sha256:d44ad7e97f8d8ff5f80b6a18a546477181119c5aecef841cc9324683f8cb8b51"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:f2c94c4ba120d711b25be07006417f56ca1f933eac20612b1551162a98c3d0bc",
    "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.Schnorr
