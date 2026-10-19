module

public import ZkcExamples.Construction.DeferredRoundsData
public import ZkcExamples.Construction.DeferredRoundsParticipant
public import Zkc.Construction.Structured

@[expose] public section

/-! Generated construction facts of the compiled `example::Proof` Entry of the subject
`deferred-rounds`. Regenerate with `lean/bridges/subject.py --write`.

`DeferredRoundsData` is the Entry's original export and
`DeferredRoundsParticipant` its constructed validator. The per-compile
transcript-construction check accepts the pair (`accepted`); the participant
projection rule is not applied to this Entry. -/

namespace ZkcExamples.Construction.DeferredRounds
open Zkc.Construction

abbrev participant := ZkcExamples.Construction.DeferredRoundsParticipant.participant

set_option smartUnfolding true in
/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport ZkcExamples.Construction.DeferredRoundsData.snapshot participant = .ok () := by decide +kernel

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := (exportContext ZkcExamples.Construction.DeferredRoundsData.snapshot participant).get (by decide +kernel)

theorem context_admitted : exportContext ZkcExamples.Construction.DeferredRoundsData.snapshot participant = some context := by
  rfl

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance ZkcExamples.Construction.DeferredRoundsData.snapshot participant).get (by decide +kernel)

theorem acceptance_admitted :
    exportAcceptance ZkcExamples.Construction.DeferredRoundsData.snapshot participant = some acceptancePosition := by
  rfl

set_option smartUnfolding true in
theorem acceptancePosition_eq : acceptancePosition = 0 := by decide +kernel

/-- Data inputs of the constructed validator: the policy's public inputs, in
policy order. -/
def inputs {F G : Type} (x : F) : List (Value F G) := [.data (.field "bls12-381.fr" x)]

end ZkcExamples.Construction.DeferredRounds
