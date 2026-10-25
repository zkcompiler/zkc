import ZkcSecurity.VCVio.SigmaAndSchnorr
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the shared-challenge composition, over `ZMod 5` as scalar field
and additive group, with no hardness claim.

* The composition's premises are satisfiable: two Schnorr instances are
  complete, specially sound and specially HVZK, so their composition is too.
* An unshared challenge fails: when each component receives its own challenge,
  two accepting transcripts can differ only in the second component's
  challenge. For a first statement without any witness (base zero, key one)
  such a pair is accepted, so no extractor makes that composition specially
  sound.
* A shared witness cannot be claimed: two accepting transcripts of the
  composition with distinct challenges exist for keys zero and one at base one,
  where no single witness exists, so no extractor makes the composition
  specially sound for the shared-witness relation. -/

namespace TestsSecurity.SigmaComposition
open OracleComp ZkcSecurity.VCVio ZkcSecurity.VCVio.SigmaAnd

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5

/-! ### Satisfiable premises -/

theorem premises (firstBase secondBase : Scalar) :
    (_root_.Schnorr.sigma Scalar Scalar firstBase).PerfectlyComplete ∧
      (_root_.Schnorr.sigma Scalar Scalar firstBase).SpeciallySound ∧
      SpecialHVZK (_root_.Schnorr.sigma Scalar Scalar firstBase).toChallengeVerifyProtocol
        (SigmaAndSchnorr.simulate Scalar Scalar firstBase) ∧
      (SigmaAndSchnorr.sigma Scalar Scalar firstBase secondBase).PerfectlyComplete ∧
      (SigmaAndSchnorr.sigma Scalar Scalar firstBase secondBase).SpeciallySound :=
  ⟨_root_.Schnorr.sigma_complete Scalar Scalar firstBase,
    _root_.Schnorr.sigma_speciallySound Scalar Scalar firstBase,
    SigmaAndSchnorr.specialHVZK Scalar Scalar firstBase,
    SigmaAndSchnorr.complete Scalar Scalar firstBase secondBase,
    SigmaAndSchnorr.speciallySound Scalar Scalar firstBase secondBase⟩

theorem zero_knowledge (firstBase secondBase : Scalar) :
    (SigmaAndSchnorr.sigma Scalar Scalar firstBase secondBase).PerfectHVZK
      (challengeFirst (simulateAnd (SigmaAndSchnorr.simulate Scalar Scalar firstBase)
        (SigmaAndSchnorr.simulate Scalar Scalar secondBase))) :=
  SigmaAndSchnorr.hvzk Scalar Scalar firstBase secondBase

/-! ### An unshared challenge -/

variable {Stmt₁ Wit₁ Commit₁ State₁ Resp₁ Stmt₂ Wit₂ Commit₂ State₂ Resp₂ Chal : Type}
  {rel₁ : Stmt₁ → Wit₁ → Bool} {rel₂ : Stmt₂ → Wit₂ → Bool}

/-- Parallel composition in which each component receives its own challenge,
with an arbitrary extractor. -/
def unshared (first : SigmaProtocol Stmt₁ Wit₁ Commit₁ State₁ Chal Resp₁ rel₁)
    (second : SigmaProtocol Stmt₂ Wit₂ Commit₂ State₂ Chal Resp₂ rel₂)
    (extract : Chal × Chal → Resp₁ × Resp₂ → Chal × Chal → Resp₁ × Resp₂ → ProbComp (Wit₁ × Wit₂)) :
    SigmaProtocol (Stmt₁ × Stmt₂) (Wit₁ × Wit₂) (Commit₁ × Commit₂) (State₁ × State₂) (Chal × Chal)
      (Resp₁ × Resp₂) (andRelation rel₁ rel₂) where
  commit := (and first second).commit
  respond statement witness state challenge := do
    let response₁ ← first.respond statement.1 witness.1 state.1 challenge.1
    let response₂ ← second.respond statement.2 witness.2 state.2 challenge.2
    pure (response₁, response₂)
  verify statement commitment challenge response :=
    first.verify statement.1 commitment.1 challenge.1 response.1 &&
      second.verify statement.2 commitment.2 challenge.2 response.2
  sim := (and first second).sim
  extract := extract

/-- The first statement, base zero and key one, has no witness, yet two
transcripts that differ only in the second challenge are accepted. Whatever
extractor is chosen, the unshared composition is not specially sound. -/
theorem unshared_not_speciallySound
    (extract : Scalar × Scalar → Scalar × Scalar → Scalar × Scalar → Scalar × Scalar →
      ProbComp (Scalar × Scalar)) :
    ¬ (unshared (_root_.Schnorr.sigma Scalar Scalar 0) (_root_.Schnorr.sigma Scalar Scalar 1)
      extract).SpeciallySound := by
  intro sound
  obtain ⟨witness, extracted⟩ := support_nonempty (extract (0, 0) (0, 0) (0, 1) (0, 0))
  have holds := sound (1, 0) (0, 0) (0, 0) (0, 1) (0, 0) (0, 0) (by decide) rfl rfl witness extracted
  clear extracted sound
  revert holds
  rcases witness with ⟨first, second⟩
  revert first second
  decide

/-! ### A shared witness claimed for the composition -/

/-- One witness for both keys. -/
def sharedRelation (firstBase secondBase : Scalar) (keys : Scalar × Scalar) (witness : Scalar) : Bool :=
  decide (witness • firstBase = keys.1) && decide (witness • secondBase = keys.2)

/-- The composition's verifier accepts transcripts with challenges zero and one
for keys zero and one at base one, and no witness is shared by these keys. -/
theorem accepted_without_shared_witness :
    (SigmaAndSchnorr.sigma Scalar Scalar 1 1).verify (0, 1) (0, 0) 0 (0, 0) = true ∧
      (SigmaAndSchnorr.sigma Scalar Scalar 1 1).verify (0, 1) (0, 0) 1 (0, 1) = true ∧
      ∀ witness, sharedRelation 1 1 (0, 1) witness = false := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- Whatever extractor is chosen, the composition's verifier is not specially
sound for one shared witness: the shared challenge does not share witnesses. -/
theorem shared_witness_not_speciallySound
    (extract : Scalar → Scalar × Scalar → Scalar → Scalar × Scalar → ProbComp Scalar) :
    ¬ (⟨⟨fun keys witness => (SigmaAndSchnorr.sigma Scalar Scalar 1 1).commit keys (witness, witness),
        fun keys witness => (SigmaAndSchnorr.sigma Scalar Scalar 1 1).respond keys (witness, witness),
        (SigmaAndSchnorr.sigma Scalar Scalar 1 1).verify⟩,
        (SigmaAndSchnorr.sigma Scalar Scalar 1 1).sim, extract⟩ :
      SigmaProtocol (Scalar × Scalar) Scalar (Scalar × Scalar) (Scalar × Scalar) Scalar (Scalar × Scalar)
        (sharedRelation 1 1)).SpeciallySound := by
  intro sound
  obtain ⟨first, second, none⟩ := accepted_without_shared_witness
  obtain ⟨witness, extracted⟩ := support_nonempty (extract 0 (0, 0) 1 (0, 1))
  have holds := sound (0, 1) (0, 0) 0 1 (0, 0) (0, 1) (by decide) first second witness extracted
  rw [none witness] at holds
  cases holds

end TestsSecurity.SigmaComposition
