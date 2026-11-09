module

public import Zkc.Verification.Claims.Subject
public import Zkc.Tools.IR.ConstructionBindings.Admission
public import Zkc.Applications.IR.Construction.SchnorrArtifact
public import Zkc.Applications.IR.Construction.SchnorrProof
public import Zkc.Applications.IR.Executable.SchnorrProofProgramData

@[expose] public section

/-! Generated artifacts of the subject `schnorr` and their checked facts. Regenerate
with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes
and the executable validator of the deployed program. Every fact below is a
generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

-- Generated connection types traverse nested occurrence certificates.
set_option maxRecDepth 4096
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
  sourceConnection := some ⟨ZkcExamples.Construction.SchnorrProof.sourceConnected⟩

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 .nil) => exact ZkcExamples.Construction.SchnorrProof.compiled_transform challenge value0 value1 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:b1d9b0d6d172578cf23ab89ace9c0188e11d937ef8c332257abc922fefd828e1", "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:34e9fc6980bda7ed3ee198856f30e2ecbcfb3bd5b5c9863ab2c1b9997cec0c35"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:34e9fc6980bda7ed3ee198856f30e2ecbcfb3bd5b5c9863ab2c1b9997cec0c35"⟩, ⟨"verifier-program", "sha256:e0db02fa6103cc3968350491b21e1c65097c91eb942dce990d08fdc993d5e4e5"⟩]⟩

/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨"sha256:ae6c35def0409f34ade665f321012a99de6bb0c95dc939137eacc3ab768cf2cc",
    "zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", .interactive, []⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.Schnorr
