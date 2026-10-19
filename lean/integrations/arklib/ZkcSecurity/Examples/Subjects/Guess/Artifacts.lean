module

public import ZkcSecurity.Endpoint.Evidence
public import ZkcExamples.Construction.GuessProof

@[expose] public section

/-! Generated artifacts of the subject `guess` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry and the types of the inputs its policy
publishes. Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Guess
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.GuessProof.snapshot
  participant := ZkcExamples.Construction.GuessProof.participant
  publics := [.field "bls12-381.fr"]
  program := none

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.GuessProof.imported
  compiled := ZkcExamples.Construction.GuessProof.compiled
  selection := ZkcExamples.Construction.GuessProof.selection
  selected := ZkcExamples.Construction.GuessProof.selected
  checked := ZkcExamples.Construction.GuessProof.selection_checked
  publics := by decide +kernel

end ZkcSecurity.Examples.Subjects.Guess
