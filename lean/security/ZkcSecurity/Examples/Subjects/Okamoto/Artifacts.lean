module

public import ZkcSecurity.Endpoint.Evidence
public import ZkcExamples.Construction.OkamotoProof

@[expose] public section

/-! Generated artifacts of the subject `okamoto-proof` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes.
Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Okamoto
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.OkamotoProof.snapshot
  participant := ZkcExamples.Construction.OkamotoProof.participant
  publics := [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1"]
  program := none

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.OkamotoProof.imported
  compiled := ZkcExamples.Construction.OkamotoProof.compiled
  selection := ZkcExamples.Construction.OkamotoProof.selection
  selected := ZkcExamples.Construction.OkamotoProof.selected
  checked := ZkcExamples.Construction.OkamotoProof.selection_checked
  publics := by decide +kernel

end ZkcSecurity.Examples.Subjects.Okamoto
