import ZkcSecurity.Examples.CompiledSchnorrFiatShamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the compiled Schnorr Fiat–Shamir theorem. A finite instance uses
`ZMod 5` as both scalar field and additive group, with no hardness claim. The
compiled program, run directly, accepts the honest proof, rejects a wrong
response and a trailing message, and asks for its challenge at a history that
binds the statement and the application context. The query-bound premise is
satisfiable, the honest prover is accepted with probability one, and the
conclusion gives a strictly positive extraction bound. -/

namespace TestsSecurity.CompiledSchnorrFiatShamir
open OracleComp OracleSpec
open Zkc.Construction
open ZkcSecurity.Examples.CompiledSchnorrFiatShamir

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5
abbrev Message := History Scalar Scalar

def application : String := "example-application"
def base : Scalar := 1
/-- The statement `2 • base`, with witness `2`. -/
def key : Scalar := 2

/-- The history at which the compiled verifier asks for the challenge of a
proof with commitment `3`. -/
def challengeHistory (message : Message) : Message :=
  message ++ [.message commitmentOrigin (.group groupDomain 3), .challenge challengeOrigin]

/-- The honest prover with nonce `3` asks the oracle for its own challenge. -/
def honest : Prover Scalar Scalar := fun _ message => do
  let challenge ← historyChallenge (challengeHistory message)
  pure (3, 3 + challenge * 2)

theorem honest_bound :
    IsQueryBoundP (honest key (initial application base key)) (· matches .inr _) 1 := by
  change IsQueryBoundP
    ((liftM ((HistorySpec Scalar Scalar).query
      (.inr (challengeHistory (initial application base key)))) :
        OracleComp (HistorySpec Scalar Scalar) Scalar) >>= fun challenge =>
      pure (3, 3 + challenge * 2)) _ 1
  simp

/-- Fixed oracle answers, for running the compiled program directly. -/
def fixed (challenge : Scalar) : QueryImpl (HistorySpec Scalar Scalar) Id :=
  QueryImpl.ofFn (fun n : Nat => (0 : Fin (n + 1))) + QueryImpl.ofFn (fun _ : Message => challenge)

/-- Answers `4` at one history and `0` elsewhere. -/
def pointed (history : Message) : QueryImpl (HistorySpec Scalar Scalar) Id :=
  QueryImpl.ofFn (fun n : Nat => (0 : Fin (n + 1))) +
    QueryImpl.ofFn (fun asked : Message => if asked = history then 4 else 0)

theorem compiled_accepts : evalWithAnswerFn (fixed 4)
    (verify application base key (3, 3 + 4 * 2)) = true := by
  decide +kernel

theorem compiled_rejects_wrong_response : evalWithAnswerFn (fixed 4)
    (verify application base key (3, 2)) = false := by
  decide +kernel

/-- The compiled program requires the whole proof to be read. -/
theorem compiled_rejects_trailing_message : evalWithAnswerFn (fixed 4)
    ((fun result => accepted (mapOutcome ZkcExamples.Construction.SchnorrProof.acceptance result.1,
      result.2)) <$>
      ideal historyChallenge ZkcExamples.Construction.SchnorrProof.participant.returned
        ZkcExamples.Construction.SchnorrProof.participant.instructions
        ((ZkcExamples.Construction.SchnorrProof.inputs base key).map .data ++
          [.transcript (initial application base key)])
        [.group groupDomain 3, .field fieldDomain (3 + 4 * 2), .field fieldDomain 0]) = false := by
  decide +kernel

/-- The challenge history binds the statement: the honest proof for `key` is
accepted when only its own history answers `4`, while the same proof against the
statement `3` asks elsewhere and is rejected. -/
theorem statement_bound :
    evalWithAnswerFn (pointed (challengeHistory (initial application base key)))
        (verify application base key (3, 3 + 4 * 2)) = true ∧
      evalWithAnswerFn (pointed (challengeHistory (initial application base key)))
        (verify application base 3 (3, 3 + 4 * 2)) = false := by
  decide +kernel

/-- The challenge history binds the application context. -/
theorem context_bound :
    evalWithAnswerFn (pointed (challengeHistory (initial application base key)))
      (verify "other-application" base key (3, 3 + 4 * 2)) = false := by
  decide +kernel

theorem honest_reduced : reduce honest key (.inl (initial application base key)) = (do
    let challenge ← HasQuery.query (spec := Key Scalar Scalar →ₒ Scalar)
      (.inl (initial application base key), (3 : Scalar))
    pure (3, 3 + challenge * 2)) := by
  have routed : route (challengeHistory (initial application base key)) =
      ((.inl (initial application base key), 3) : Key Scalar Scalar) := by
    simp [route, challengeHistory, challengeKey_append]
  simp only [reduce, honest, Sum.elim_inl, id, simulateQ_bind, simulateQ_pure,
    route_challenge routed]
  rfl

def answers (challenge : Scalar) : QueryImpl (_root_.FiatShamir.Fork.wrappedSpec Scalar) Id :=
  QueryImpl.ofFn (fun n : Nat => (0 : Fin (n + 1))) + QueryImpl.ofFn (fun _ : Unit => challenge)

theorem honest_accepts : evalWithAnswerFn (answers 4)
    (run honest application base key) = true := by
  rw [run_eq]
  decide +kernel

/-- One fresh challenge request, reused by final verification. -/
theorem honest_run : run honest application base key = (do
    let _ ← _root_.FiatShamir.Fork.wrappedChallengeQuery Scalar
    pure true) := by
  rw [run_eq]
  unfold _root_.FiatShamir.knowledgeVerifyRun
  rw [honest_reduced]
  simp [_root_.FiatShamir, _root_.Schnorr.sigma, HasQuery.query,
    QueryImpl.simulateQ_add_liftM_query_right, _root_.FiatShamir.Fork.roImpl,
    StateT.run'_eq, monad_norm, key, base]

local instance : ∀ t, MeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec Scalar).Range t) :=
  fun _ => ⊤
local instance : ∀ t, DiscreteMeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec Scalar).Range t) :=
  fun _ => inferInstance
noncomputable local instance : IsUniformMeasureSpec (_root_.FiatShamir.Fork.wrappedSpec Scalar) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

theorem honest_acceptance : acceptance honest application base key = 1 := by
  unfold acceptance
  rw [honest_run]
  simp

/-- The conclusion is not vacuous: a strictly positive extraction bound. -/
theorem positive_extraction : (2⁻¹ - 5⁻¹ : ENNReal) ≤
    Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (_root_.Schnorr.sigma Scalar Scalar base)
        (ZkcSecurity.Examples.StructuredSchnorrFiatShamir.generable base) (Message ⊕ Message)
        (reduce honest) (.inl (initial application base key)) 1 key}[
      ZkcExamples.Structured.SchnorrBinding.Relation base key witness] := by
  have bound := knowledge_soundness honest application base key 1 honest_bound
  dsimp only at bound
  rw [honest_acceptance] at bound
  simpa only [_root_.FiatShamir.challengeSpaceInv, Scalar, ZMod.card,
    Nat.cast_ofNat, one_mul, one_div, Nat.cast_one, one_add_one_eq_two] using bound

theorem extraction_bound_positive : (0 : ENNReal) < 2⁻¹ - 5⁻¹ := by
  apply tsub_pos_iff_lt.mpr
  exact ENNReal.inv_lt_inv.mpr (by norm_num)

end TestsSecurity.CompiledSchnorrFiatShamir
