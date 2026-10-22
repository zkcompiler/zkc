import ZkcSecurity.VCVio.UniformChallenge
import ZkcSecurity.Examples.SchnorrAndSigma
import ZkcSecurity.Examples.ChaumPedersenSigma
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the Fiat–Shamir theorems over the imported Schnorr AND and
Chaum–Pedersen verifiers. A finite instance uses `ZMod 5` as scalar field and
additive group, with no hardness claim: each query-bound premise is
satisfiable, each honest prover is accepted with probability one, and each
conclusion is a strictly positive extraction bound. The imported decisions
accept honest responses and reject a changed one. -/

open scoped ZkcSecurity.VCVio.UniformChallenge

namespace TestsSecurity.SigmaCompositionFiatShamir
open OracleComp OracleSpec

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5

def message : String := "example-context"

/-! ### Schnorr AND: keys `2` and `3` at base `1` -/

section Pair
open ZkcSecurity.Examples.SchnorrAndSigma

def keys : Scalar × Scalar := (2, 3)

/-- The honest prover with nonces `3` and `4` asks the oracle for its challenge. -/
def honest : _root_.FiatShamir.KnowledgeProver (Scalar × Scalar) (Scalar × Scalar) Scalar
    (Scalar × Scalar) String :=
  fun _ message => do
    let challenge ← HasQuery.query (spec := String × (Scalar × Scalar) →ₒ Scalar) (message, (3, 4))
    pure ((3, 4), (3 + challenge * 2, 4 + challenge * 3))

theorem honest_bound : _root_.FiatShamir.nmaHashQueryBound (M := String) (honest keys message) 1 := by
  change IsQueryBoundP
    ((liftM ((unifSpec + (String × (Scalar × Scalar) →ₒ Scalar)).query (.inr (message, (3, 4)))) :
        OracleComp (unifSpec + (String × (Scalar × Scalar) →ₒ Scalar)) Scalar) >>= fun challenge =>
      pure ((3, 4), (3 + challenge * 2, 4 + challenge * 3))) _ 1
  simp

theorem decision_controls :
    decision (1 : Scalar) 1 0 keys (3, 4) (4 : Scalar) (3 + 4 * 2, 4 + 4 * 3) = true ∧
      decision (1 : Scalar) 1 0 keys (3, 4) (4 : Scalar) (3 + 4 * 2, 2) = false := by
  simp only [decision_eq]
  decide

theorem honest_run : _root_.FiatShamir.knowledgeVerifyRun
    (sigma (F := Scalar) (1 : Scalar) 1 0) (generable 1 1) String honest keys message = (do
      let _ ← _root_.FiatShamir.Fork.wrappedChallengeQuery Scalar
      pure true) := by
  rw [sigma_eq]
  unfold _root_.FiatShamir.knowledgeVerifyRun
  simp [honest, _root_.FiatShamir, ZkcSecurity.VCVio.SigmaAnd.and, _root_.Schnorr.sigma, HasQuery.query,
    QueryImpl.simulateQ_add_liftM_query_right, _root_.FiatShamir.Fork.roImpl,
    StateT.run'_eq, monad_norm, keys]

theorem honest_acceptance : _root_.FiatShamir.knowledgeAcceptance
    (sigma (F := Scalar) (1 : Scalar) 1 0) (generable 1 1) String honest keys message = 1 := by
  unfold _root_.FiatShamir.knowledgeAcceptance
  rw [honest_run]
  simp

/-- A strictly positive extraction bound for the retained `DLogPair` formula. -/
theorem positive_extraction : (2⁻¹ - 5⁻¹ : ENNReal) ≤
    Pr{let witnesses ← _root_.FiatShamir.knowledgeExtractor
        (sigma (F := Scalar) (1 : Scalar) 1 0) (generable 1 1) String honest message 1 keys}[
      ZkcExamples.Structured.SchnorrAndBinding.Relation (1 : Scalar) keys.1 1 keys.2
        witnesses.1 witnesses.2] := by
  have bound := knowledge_soundness String (1 : Scalar) 1 0 honest keys message 1 honest_bound
  dsimp only at bound
  rw [honest_acceptance] at bound
  simpa only [_root_.FiatShamir.challengeSpaceInv, Scalar, ZMod.card,
    Nat.cast_ofNat, one_mul, one_div, Nat.cast_one, one_add_one_eq_two] using bound

end Pair

/-! ### Chaum–Pedersen: witness `2` at bases `1` and `3` -/

section Equality
open ZkcSecurity.Examples.ChaumPedersenSigma

def equalityKeys : Scalar × Scalar := (2, 1)

/-- The honest prover with nonce `3` commits at both bases. -/
def equalityHonest : _root_.FiatShamir.KnowledgeProver (Scalar × Scalar) (Scalar × Scalar) Scalar Scalar
    String :=
  fun _ message => do
    let challenge ← HasQuery.query (spec := String × (Scalar × Scalar) →ₒ Scalar) (message, (3, 4))
    pure ((3, 4), 3 + challenge * 2)

theorem equality_bound :
    _root_.FiatShamir.nmaHashQueryBound (M := String) (equalityHonest equalityKeys message) 1 := by
  change IsQueryBoundP
    ((liftM ((unifSpec + (String × (Scalar × Scalar) →ₒ Scalar)).query (.inr (message, (3, 4)))) :
        OracleComp (unifSpec + (String × (Scalar × Scalar) →ₒ Scalar)) Scalar) >>= fun challenge =>
      pure ((3, 4), 3 + challenge * 2)) _ 1
  simp

/-- One response must satisfy both bases: commitments and a response that
satisfy the first base's equation but not the second's are rejected. -/
theorem equality_decision_controls :
    decision (1 : Scalar) 3 0 equalityKeys (3, 4) (4 : Scalar) (3 + 4 * 2) = true ∧
      decision (1 : Scalar) 3 0 equalityKeys (3, 0) (4 : Scalar) 1 = false ∧
      (1 : Scalar) • (1 : Scalar) = 3 + (4 : Scalar) • equalityKeys.1 := by
  simp only [decision_eq]
  decide

theorem equality_run : _root_.FiatShamir.knowledgeVerifyRun
    (sigma (F := Scalar) (1 : Scalar) 3 0) (generable 1 3) String equalityHonest equalityKeys message = (do
      let _ ← _root_.FiatShamir.Fork.wrappedChallengeQuery Scalar
      pure true) := by
  have second : ∀ challenge : Scalar, (3 + challenge * 2) * 3 = 4 + challenge := by decide
  rw [sigma_eq]
  unfold _root_.FiatShamir.knowledgeVerifyRun
  simp [equalityHonest, _root_.FiatShamir, _root_.Schnorr.sigma, HasQuery.query,
    QueryImpl.simulateQ_add_liftM_query_right, _root_.FiatShamir.Fork.roImpl,
    StateT.run'_eq, monad_norm, equalityKeys, second]

theorem equality_acceptance : _root_.FiatShamir.knowledgeAcceptance
    (sigma (F := Scalar) (1 : Scalar) 3 0) (generable 1 3) String equalityHonest equalityKeys message = 1 := by
  unfold _root_.FiatShamir.knowledgeAcceptance
  rw [equality_run]
  simp

/-- A strictly positive extraction bound for the retained `DLogEquality` formula. -/
theorem equality_positive_extraction : (2⁻¹ - 5⁻¹ : ENNReal) ≤
    Pr{let witness ← _root_.FiatShamir.knowledgeExtractor
        (sigma (F := Scalar) (1 : Scalar) 3 0) (generable 1 3) String equalityHonest message 1
          equalityKeys}[
      ZkcExamples.Structured.ChaumPedersenBinding.Relation (1 : Scalar) equalityKeys.1 3 equalityKeys.2
        witness] := by
  have bound := knowledge_soundness String (1 : Scalar) 3 0 equalityHonest equalityKeys message 1
    equality_bound
  dsimp only at bound
  rw [equality_acceptance] at bound
  simpa only [_root_.FiatShamir.challengeSpaceInv, Scalar, ZMod.card,
    Nat.cast_ofNat, one_mul, one_div, Nat.cast_one, one_add_one_eq_two] using bound

end Equality

end TestsSecurity.SigmaCompositionFiatShamir
