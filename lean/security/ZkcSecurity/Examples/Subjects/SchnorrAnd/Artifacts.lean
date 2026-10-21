module

public import ZkcSecurity.Endpoint.Evidence
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

end ZkcSecurity.Examples.Subjects.SchnorrAnd
