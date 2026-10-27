module

public import ZkcExamples.Construction.SumcheckSourceConnection
public import Zkc.Construction.ScalarVerifier

@[expose] public section

/-! Maintained actual Domain endpoint. Historical Instruction comparisons are
outside this module's dependencies. All raw typed public inputs are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckProof
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Construction.SumcheckDomainConnection
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def compiledVerifier (challenge : History F G → m F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (proof : Proof F G) : m (PIR.Outcome (Option Bool) × Proof F G) :=
  ScalarVerifier.verify program context participant acceptancePosition challenge
    (inputs values claim rounds) initial proof

/-- Whole-return readback and direct Boolean selection agree at every actual
return. The proof uses the all-reply mapped-history invariant, including stops. -/
theorem compiled_retained (challenge : History F G → m F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge values claim rounds initial proof =
      (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        retained challenge values claim rounds initial proof := by
  rw [compiledVerifier, ScalarVerifier.verify_eq_runK program context participant acceptancePosition
    challenge (inputs values claim rounds) (SumcheckDomainConnection.inputs values claim rounds)
    rfl initial proof, retained_root]
  have key : ScalarVerifier.origin participant = Origin.withoutCoordinates := by funext origin; rfl
  rw [key]
  let finish : Domain.Environment (uniformCarriers F G) → Proof F G →
      m (PIR.Outcome (Option Bool) × Proof F G) := fun values unread => pure
    (.returned ((ScalarVerifier.acceptance acceptancePosition) ⟨values, []⟩), unread)
  have projection := congrArg (fun process => runK Origin.withoutCoordinates initial challenge process proof finish)
    (root_projection values claim rounds ([] : Domain.History (uniformCarriers F G)))
  simp only [rootProjection, runK_forgetCheckpoints, runK_bind, runK] at projection
  change runK Origin.withoutCoordinates initial challenge
    (Domain.participant (ringModel F G) program context participant (frame values claim rounds []))
    proof (fun result unread => finish result.values unread) = _
  rw [projection]
  rw [runK_mapOutcome]
  unfold rootProcess
  split
  · rw [runK_bind, runK_bind]
    apply runK_congr_yields _ _ _ _ _ (reduce_mapped (List.range rounds) [] claim [] [] rfl)
    intro state unread hasMapping
    obtain ⟨suffix, mapped⟩ := Option.isSome_iff_exists.mp hasMapping
    simp only [terminal]
    split_ifs <;> simp [runK, nominalFinish, finish, readbackOutcome, readbackValues,
      readbackValue, readbackData, mapped, ScalarVerifier.acceptance, mapOutcome,
      acceptance, acceptancePosition_eq]
  · simp [runK]

/-- Actual Domain/source transport for every public vector, claim and round
count, every initial history and every typed proof and challenge function. -/
theorem compiled_transform (challenge : History F G → m F) (values : List F) (claim : F)
    (rounds handle : Nat) (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge values claim rounds initial proof =
      transform context challenge (verifier values claim rounds handle) initial proof := by
  rw [compiled_retained]
  exact retained_transform challenge values claim rounds handle initial proof

end ZkcExamples.Construction.SumcheckProof
