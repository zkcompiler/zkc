import ZkcSecurity.Mathematics.Oracle.UniformChallenge
import ZkcSecurityExamples.StructuredSchnorrFiatShamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the Fiat–Shamir theorem over the imported interactive Schnorr
verifier. A finite instance uses `ZMod 5` as scalar field and additive group,
with no hardness claim: the query-bound premise is satisfiable, the honest
prover is accepted with probability one, and the conclusion is a strictly
positive extraction bound. -/

open scoped ZkcSecurity.VCVio.UniformChallenge

namespace TestsSecurity.StructuredSchnorrFiatShamir
open OracleComp OracleSpec
open ZkcSecurity.Examples.StructuredSchnorrFiatShamir

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5

def base : Scalar := 1
/-- The statement `2 • base`, with witness `2`. -/
def key : Scalar := 2
def message : String := "example-context"

/-- The honest prover with nonce `3` asks the oracle for its own challenge. -/
def honest : _root_.FiatShamir.KnowledgeProver Scalar Scalar Scalar Scalar String :=
  fun _ message => do
    let challenge ← HasQuery.query (spec := String × Scalar →ₒ Scalar) (message, 3)
    pure (3, 3 + challenge * 2)

theorem honest_bound : _root_.FiatShamir.nmaHashQueryBound (M := String) (honest key message) 1 := by
  change IsQueryBoundP
    ((liftM ((unifSpec + (String × Scalar →ₒ Scalar)).query (.inr (message, 3))) :
        OracleComp (unifSpec + (String × Scalar →ₒ Scalar)) Scalar) >>= fun challenge =>
      pure (3, 3 + challenge * 2)) _ 1
  simp

/-- The imported verifier's decision accepts the honest proof for challenge `4`
and rejects a wrong response. -/
theorem decision_controls :
    ZkcSecurity.Examples.StructuredSchnorrSigma.decision base key (3 : Scalar) (4 : Scalar)
        (3 + 4 * 2) 0 = true ∧
      ZkcSecurity.Examples.StructuredSchnorrSigma.decision base key (3 : Scalar) (4 : Scalar)
        2 0 = false := by
  simp only [ZkcSecurity.Examples.StructuredSchnorrSigma.decision_eq]
  decide

/-- One fresh challenge request, reused by final verification. -/
theorem honest_run : _root_.FiatShamir.knowledgeVerifyRun
    (ZkcSecurity.Examples.StructuredSchnorrSigma.sigma (F := Scalar) base base 0 0)
    (generable base) String honest key message = (do
      let _ ← _root_.FiatShamir.Fork.wrappedChallengeQuery Scalar
      pure true) := by
  rw [ZkcSecurity.Examples.StructuredSchnorrSigma.sigma_eq]
  unfold _root_.FiatShamir.knowledgeVerifyRun
  simp [honest, _root_.FiatShamir, _root_.Schnorr.sigma, HasQuery.query,
    QueryImpl.simulateQ_add_liftM_query_right, _root_.FiatShamir.Fork.roImpl,
    StateT.run'_eq, monad_norm, key, base]

theorem honest_acceptance : _root_.FiatShamir.knowledgeAcceptance
    (ZkcSecurity.Examples.StructuredSchnorrSigma.sigma (F := Scalar) base base 0 0)
    (generable base) String honest key message = 1 := by
  unfold _root_.FiatShamir.knowledgeAcceptance
  rw [honest_run]
  simp

/-- The conclusion is not vacuous: a strictly positive extraction bound. -/
theorem positive_extraction : (2⁻¹ - 5⁻¹ : ENNReal) ≤
    Pr{let witness ← _root_.FiatShamir.knowledgeExtractor
        (ZkcSecurity.Examples.StructuredSchnorrSigma.sigma (F := Scalar) base base 0 0)
        (generable base) String honest message 1 key}[
      ZkcExamples.Structured.SchnorrBinding.Relation base key witness] := by
  have bound := knowledge_soundness String base base 0 0 honest key message 1 honest_bound
  dsimp only at bound
  rw [honest_acceptance] at bound
  simpa only [_root_.FiatShamir.challengeSpaceInv, Scalar, ZMod.card,
    Nat.cast_ofNat, one_mul, one_div, Nat.cast_one, one_add_one_eq_two] using bound

end TestsSecurity.StructuredSchnorrFiatShamir
