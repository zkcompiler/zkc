module

public import ZkcSecurity.Endpoint.Evidence
public import ZkcExamples.Construction.SchnorrProof
public import ZkcExamples.Executable.SchnorrProof

@[expose] public section

/-! Generated artifacts of the subject `schnorr` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

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

end ZkcSecurity.Examples.Subjects.Schnorr
