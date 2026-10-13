module

public import Zkc.Protocols.Sumcheck.Common.Program
public import Zkc.Protocols.Sumcheck.Security

@[expose] public section

/-! Reusable security consumers of the common-source two-round verifier contract.
Fresh uniform coins are supplied by the experiment, not inferred from service handles. -/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 500000

namespace Zkc.Protocols.Sumcheck.Common

open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Polynomial Zkc.Probability

variable {F : Type} [Field F] [DecidableEq F]

/-- Any fixed private randomness/state can be incorporated into these choices.
The second coefficients can depend on the first coin, never the second coin. -/
structure Strategy (F : Type) where
  first : Message F
  second : F → Message F

def strategy (prover : Strategy F) : Zkc.Protocols.Sumcheck.Strategy F 2 :=
  .send prover.first (fun first => .send (prover.second first) (fun _ => .done))

omit [Field F] [DecidableEq F] in
/-- The callback presentation covers every adaptive two-round strategy of the
independent game, including any fixed private prover state. -/
theorem strategy_surjective (source : Zkc.Protocols.Sumcheck.Strategy F 2) :
    ∃ prover : Strategy F, strategy prover = source := by
  cases source with
  | send first next =>
      refine ⟨⟨first, fun r => match next r with | .send message _ => message⟩, ?_⟩
      dsimp only [strategy]
      congr 1
      funext r
      cases next r with
      | send message finish =>
          congr 1
          funext last
          cases finish last
          rfl

def received (prover : Strategy F) (first : F) : Nat → F
  | 0 => prover.first.constant
  | 1 => prover.first.linear
  | 2 => prover.first.quadratic
  | 5 => (prover.second first).constant
  | 6 => (prover.second first).linear
  | _ => (prover.second first).quadratic

/-- Position counts reached actions. Coins are exposed only at positions three
and eight of the proved verifier, after each full coefficient message. -/
def transcriptHandler (prover : Strategy F) (first second : F) :
    PIR.Handler (actions (F := F)) Nat (Action Nat language services (ScalarValue F F))
  | action@(.send ..), position => ⟨.returned (), position + 1, [action]⟩
  | action@(.query ..), position =>
      ⟨.returned (if position = 3 then first else second), position + 1, [action]⟩
  | action@(.receive ty ..), position =>
      ⟨.returned (match ty with
        | .boolean => false
        | .field _ => received prover first position
        | .group _ => 0
        | .service _ => 0), position + 1, [action]⟩

def run (program : Verifier F) (coefficients : Coefficients F) (claim : F) (service : Nat)
    (prover : Strategy F) (first second : F) :
    PIR.Execution Nat (Action Nat language services (ScalarValue F F)) (Option Bool) :=
  (program coefficients claim service).run (transcriptHandler prover first second) 0

omit [DecidableEq F] in
theorem handler_receive_field (prover : Strategy F) (first second : F) (domain site : String)
    (sender position : Nat) :
    transcriptHandler prover first second (.receive (.field domain) site sender) position =
      ⟨.returned (received prover first position), position + 1, [.receive (.field domain) site sender]⟩ := by rfl

omit [DecidableEq F] in
theorem handler_query (prover : Strategy F) (first second : F) (site domain : String)
    (args : Values (ScalarValue F F) (services.arguments domain)) (position : Nat) :
    transcriptHandler prover first second (.query site domain args) position =
      ⟨.returned (if position = 3 then first else second), position + 1, [.query site domain args]⟩ := by rfl

omit [DecidableEq F] in
theorem handler_send (prover : Strategy F) (first second : F) (site : String)
    (receiver : Nat) {ty : Ty} (value : ScalarValue F F ty) (position : Nat) :
    transcriptHandler prover first second (.send site receiver value) position =
      ⟨.returned (), position + 1, [.send site receiver value]⟩ := by rfl

theorem experiment_outcome (wiring : Wiring) (coefficients : Coefficients F) (claim : F) (service : Nat)
    (prover : Strategy F) (first second : F) :
    ((experiment wiring coefficients claim service).run (transcriptHandler prover first second) 0).outcome =
      if wireBoundary prover.first = claim then
        if wireBoundary (prover.second first) = wireEvaluate prover.first first then
          .returned (some (decide (wireEvaluate (prover.second first) second =
            evaluate coefficients first second)))
        else .stopped .reject
      else .stopped .reject := by
  by_cases hfirst : wireBoundary prover.first = claim
  all_goals by_cases hsecond : wireBoundary (prover.second first) = wireEvaluate prover.first first
  all_goals simp only [experiment, experimentWith, standardArithmetic, PIR.Proc.run, PIR.Execution.follow, handler_receive_field,
    handler_query, handler_send, received, hfirst, hsecond, decide_true, decide_false,
    Bool.false_eq_true, ite_true, ite_false, Nat.reduceAdd, Nat.reduceEqDiff]
  all_goals rfl

variable {wiring : Wiring} {program : Verifier F}

theorem VerifierContract.run_outcome (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (claim : F) (service : Nat)
    (prover : Strategy F) (first second : F) :
    (run program coefficients claim service prover first second).outcome =
      if wireBoundary prover.first = claim then
        if wireBoundary (prover.second first) = wireEvaluate prover.first first then
          .returned (some (decide (wireEvaluate (prover.second first) second =
            evaluate coefficients first second)))
        else .stopped .reject
      else .stopped .reject := by
  exact (congrArg (fun process => (process.run (transcriptHandler prover first second) 0).outcome)
    (certificate.realizes coefficients claim service).process_eq).trans
      (experiment_outcome wiring coefficients claim service prover first second)

/-- The accepting event comes from the actual imported execution, including
both early rejection branches and the final false result. -/
theorem VerifierContract.accepted_iff (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (claim : F) (service : Nat)
    (prover : Strategy F) (first second : F) :
    (run program coefficients claim service prover first second).outcome = .returned (some true) ↔
      Zkc.Protocols.Sumcheck.verify (polynomial coefficients) claim (strategy prover)
        (first, second, ()) = true := by
  have terminal := Zkc.Protocols.Sumcheck.verify_iff_final
    (polynomial coefficients) claim (strategy prover) (first, second, ())
  refine Iff.trans ?_ terminal.symm
  rw [certificate.run_outcome]
  simp only [wireBoundary_eq, wireEvaluate_eq, evaluate_eq]
  change (if prover.first.boundary = claim then
      if (prover.second first).boundary = prover.first.evaluate first then
        PIR.Outcome.returned (some (decide ((prover.second first).evaluate second =
          (polynomial coefficients).eval (Zkc.Protocols.Sumcheck.tapePoint 2 (first, second, ())))))
      else .stopped .reject
    else .stopped .reject) = .returned (some true) ↔
    (if prover.first.boundary = claim then
      if (prover.second first).boundary = prover.first.evaluate first then
        some ((prover.second first).evaluate second)
      else none
    else none) = some ((polynomial coefficients).eval (Zkc.Protocols.Sumcheck.tapePoint 2 (first, second, ())))
  by_cases hfirst : prover.first.boundary = claim
  all_goals by_cases hsecond : (prover.second first).boundary = prover.first.evaluate first
  all_goals simp [hfirst, hsecond]

def honestStrategy (coefficients : Coefficients F) : Strategy F :=
  ⟨Zkc.Protocols.Sumcheck.roundPolynomial (polynomial coefficients),
    fun first => Zkc.Protocols.Sumcheck.roundPolynomial ((polynomial coefficients).restrict first)⟩

omit [DecidableEq F] in
theorem honest_strategy (coefficients : Coefficients F) :
    strategy (honestStrategy coefficients) = Zkc.Protocols.Sumcheck.honest (polynomial coefficients) := by
  rfl

theorem VerifierContract.completeness (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (service : Nat) (first second : F) :
    (run program coefficients (polynomial coefficients).booleanSum service
      (honestStrategy coefficients) first second).outcome = .returned (some true) := by
  rw [certificate.accepted_iff, honest_strategy]
  exact Zkc.Protocols.Sumcheck.completeness _ _

variable [Fintype F]

/-- Exactly two independent uniform field challenges. The fixed prover cannot
inspect the unconsumed tape; no sampler claim is attached to a native handle. -/
def acceptance (program : Verifier F) (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F) : ℚ :=
  UniformTape.average 2 (fun coins =>
    if (run program coefficients claim service prover coins.1 coins.2.1).outcome = .returned (some true)
    then 1 else 0)

theorem VerifierContract.acceptance_eq (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F) :
    acceptance program coefficients claim service prover =
      Zkc.Protocols.Sumcheck.acceptance (polynomial coefficients) claim (strategy prover) := by
  unfold acceptance Zkc.Protocols.Sumcheck.acceptance
  congr 1
  funext coins
  rcases coins with ⟨first, second, terminal⟩
  cases terminal
  simp only [certificate.accepted_iff]

/-- Ordinary interactive soundness for arbitrary causal coefficient messages.
This is not knowledge soundness, Fiat–Shamir, or a committed oracle claim. -/
theorem VerifierContract.soundness (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    acceptance program coefficients claim service prover ≤ 4 / (Fintype.card F : ℚ) := by
  rw [certificate.acceptance_eq]
  convert Zkc.Protocols.Sumcheck.soundness (polynomial coefficients) claim (strategy prover) falseClaim using 1
  norm_num

theorem VerifierContract.perfect_completeness (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (service : Nat) :
    acceptance program coefficients (polynomial coefficients).booleanSum service (honestStrategy coefficients) = 1 := by
  rw [certificate.acceptance_eq, honest_strategy]
  exact Zkc.Protocols.Sumcheck.perfect_completeness _

/-- A uniformly sampled private seed is independent of the verifier tape.
Arbitrary fixed private state is already covered by `soundness`. -/
theorem VerifierContract.randomized_soundness (certificate : VerifierContract wiring program) {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Seed → Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    UniformTape.average (F := Seed) 1 (fun seed => acceptance program coefficients claim service (prover seed.1)) ≤
      4 / (Fintype.card F : ℚ) := by
  rw [← UniformTape.constant (F := Seed) 1 (4 / (Fintype.card F : ℚ))]
  exact UniformTape.monotone 1 _ _ (fun _ => certificate.soundness coefficients claim service _ falseClaim)

end Zkc.Protocols.Sumcheck.Common
