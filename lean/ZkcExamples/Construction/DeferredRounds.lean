module

public import ZkcExamples.Construction.DeferredRoundsData
public import ZkcExamples.Construction.DeferredRoundsParticipant
public import Zkc.Construction.Structured

@[expose] public section

/-! The constructed validator of the deferred-rounds fixture's `example::Proof`.

`DeferredRoundsData` is the original-stage export of the Proof Entry of
`common/tests/fixtures/projects/deferred-rounds`, and
`DeferredRoundsParticipant` is the compiler's constructed validator for it. The
per-compile transcript-construction check accepts the pair (`accepted`). This
module derives the occurrence context and the acceptance position the way that
check does; the participant projection rule is not applied to this Entry.
-/

namespace ZkcExamples.Construction.DeferredRounds
open Zkc.Construction

abbrev participant := DeferredRoundsParticipant.participant

set_option smartUnfolding true in
/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport DeferredRoundsData.snapshot participant = .ok () := by decide +kernel

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := (exportContext DeferredRoundsData.snapshot participant).get (by decide +kernel)

theorem context_admitted : exportContext DeferredRoundsData.snapshot participant = some context := by
  rfl

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance DeferredRoundsData.snapshot participant).get (by decide +kernel)

theorem acceptance_admitted :
    exportAcceptance DeferredRoundsData.snapshot participant = some acceptancePosition := by
  rfl

set_option smartUnfolding true in
theorem acceptancePosition_eq : acceptancePosition = 0 := by decide +kernel

/-- Data inputs of the constructed validator: the public value `x`. -/
def inputs {F G : Type} (x : F) : List (Value F G) := [.data (.field "bls12-381.fr" x)]

end ZkcExamples.Construction.DeferredRounds
