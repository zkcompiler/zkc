module

public import ZkcExamples.Executable.SumcheckSourceHonest
public import ZkcExamples.Executable.SumcheckCharges

@[expose] public section

/-! Honest source success transported through the retained artifact's full
checked connection. Output, transcript readback and cost use that same artifact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Executable.SumcheckDomainHonest
open Zkc Zkc.Construction Zkc.Executable Zkc.Source Zkc.Source.Structured
open Uniform Uniform.DomainAdapter
open ZkcExamples.Construction.SumcheckSourceConnection
attribute [local implicit_reducible] CheckedProtocol.signature
attribute [local irreducible] DomainVM.Passes

abbrev transcript : SumcheckMessages.Transcript := SumcheckProof.transcript
abbrev messages {F G : Type} [Field F] (oracle : History F G → F) :=
  SumcheckMessages.honestRounds transcript oracle

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def Success (returned : DomainVM.Environment F G) (unread : Proof F G) : Prop :=
  returned[0]? = some (.data (.boolean true)) ∧ unread = [] ∧
    ∃ history, returned = [.data (.boolean true), .transcript context.suite history] ∧
      ∃ suffix, readbackHistory Origin.withoutCoordinates history = some suffix

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Complete output ABI and the artifact-fixed history projection preserve
both the actual selected Boolean and readable transcript suffix. -/
theorem returned (scalar : Values (Component (assignment F G)) program.payload.entry.outputs ×
    Domain.History (uniformCarriers F G))
    (actual : Values (Component (assignment F G)) program.payload.entry.outputs × Original.State (uniformCarriers F G))
    (target : Domain.Result (uniformCarriers F G)) (unread : Proof F G)
    (result : scalar.1 = actual.1)
    (history : scalar.2 = ScalarProjection.history (ScalarProjection.iterations artifact) actual.2.history)
    (related : Original.CompleteReturns program.payload.entry.signature routing.context 1 artifact actual target)
    (good : SumcheckSourceHonest.SourceSuccess scalar unread) : Success target.values unread := by
  obtain ⟨data, encoding, targetValues⟩ := related.values
  have outputs : actual.1 = .cons (some true) .nil := result.symm.trans good.1
  rw [outputs] at encoding
  change some [.data (.boolean true)] = some data at encoding
  cases encoding
  rw [targetValues]
  refine ⟨rfl, good.2.1, actual.2.history, rfl, ?_⟩
  rw [← LoopedSourceProcess.readback_history]
  change ∃ suffix, readbackHistory SourceProcess.legacyOrigin
    (ScalarProjection.history (ScalarProjection.iterations artifact) actual.2.history) = some suffix
  rw [← history]
  exact good.2.2

/-- Exact retained observation success, with the original postcondition and
exact unread suffix. Shape and admission enter only the honest-source premise. -/
theorem observation_passes (oracle : History F G → F) (initial : History F G)
    (values : List F) (rounds : Nat) (admitted : rounds ≤ SumcheckProof.maximum)
    (shaped : values.length = 2 ^ rounds) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (DomainVM.observation program context (Code.instructions SumcheckProof.lowered.code) SumcheckProof.lowered.returned
        (SumcheckProof.physicalInputs values values.sum rounds []))
      ((messages oracle initial values rounds).map (.field "bls12-381.fr")) Success := by
  have source := SumcheckSourceHonest.source_passes (G := G) oracle initial values rounds routing.selectedHandle admitted shaped
  rw [SumcheckSourceHonest.transcript_identity] at source
  have passes := ScalarCheckedBytes.connected (F := F) (G := G) checkedConnection rfl _ rfl (by decide +kernel)
    (SumcheckProof.physicalInputs values values.sum rounds [])
    (ZkcExamples.Construction.SumcheckProof.verifierInputs values values.sum rounds routing.selectedHandle)
    (by kernel_rfl) (by kernel_rfl) (by derive_scalar_support) initial oracle
    ((messages oracle initial values rounds).map (.field "bls12-381.fr"))
    SumcheckSourceHonest.SourceSuccess (fun result rest => Success result.values rest)
    source returned
  rw [SumcheckProof.normalized]
  apply DomainVM.Passes.participant_observation
  rw [DomainVM.Passes.forgetCheckpoints, DomainVM.Passes.bind]
  have key : ScalarVerifier.origin artifact = Origin.withoutCoordinates := by kernel_rfl
  rw [key] at passes
  apply DomainVM.Passes.mono _ _ _ _ _ _ _ ?_ passes
  intro value unread good
  simpa only [DomainVM.Passes] using good

end ZkcExamples.Executable.SumcheckDomainHonest
