module

public import ZkcSecurity.Endpoint.Evidence
public import ZkcExamples.Construction.SumcheckProof
public import ZkcExamples.Executable.SumcheckProof

@[expose] public section

/-! Generated artifacts of the subject `sumcheck` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes
and the executable validator of the deployed program. Every fact below is a
generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.SumcheckProof.snapshot
  participant := ZkcExamples.Construction.SumcheckProof.participant
  publics := [.vector "bls12-381.fr", .field "bls12-381.fr", .index]
  program := some ZkcExamples.Executable.SumcheckProof.validator

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.SumcheckProof.imported
  compiled := ZkcExamples.Construction.SumcheckProof.compiled
  selection := ZkcExamples.Construction.SumcheckProof.selection
  selected := ZkcExamples.Construction.SumcheckProof.selected
  checked := ZkcExamples.Construction.SumcheckProof.selection_checked
  publics := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The executable validator, accepted by the lowering rule. -/
def lowering : LoweringEvidence artifacts compiled F G where
  validator := ZkcExamples.Executable.SumcheckProof.validator
  program := rfl
  lowered := ZkcExamples.Executable.SumcheckProof.lowered
  accepted := ZkcExamples.Executable.SumcheckProof.accepted
  prepared := ZkcExamples.Executable.SumcheckProof.prepared
  sorted := ZkcExamples.Executable.SumcheckProof.helpersSorted
  admits statement := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 .nil)) => exact ZkcExamples.Executable.SumcheckProof.admitted value0 value1 value2

end ZkcSecurity.Examples.Subjects.Sumcheck
