module

public import Zkc.Protocols.Sumcheck.FactorOpening.Program
public import Zkc.Protocols.Sumcheck.Common

@[expose] public section

/-! Security of sequential factor checks at the actual Sumcheck residual.
The opening loss concerns reached checks in this same experiment. No independence
between openings is assumed, and arbitrary checks do not imply PCS security.
-/
set_option autoImplicit false
namespace Zkc.Protocols.Sumcheck.FactorOpening
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.Sumcheck.Common
open Zkc.Probability

variable {F : Type} [Field F] [DecidableEq F]

/-- Callbacks are fixed before the coins. The right reply may depend on the
actual left reply; both may depend on both already exposed challenges. -/
structure Strategy (F : Type) where
  rounds : Common.Strategy F
  left : F → F → F
  right : F → F → F → F

def residual (prover : Strategy F) (first second : F) : Residual F :=
  ⟨first, second, wireEvaluate (prover.rounds.second first) second⟩

def received (prover : Strategy F) (first second : F) (position : Nat) : F :=
  if position = 10 then prover.left first second
  else if position = 11 then prover.right first second (prover.left first second)
  else Common.received prover.rounds first position

def transcriptHandler (prover : Strategy F) (first second : F) :
    PIR.Handler (actions (F := F)) Nat (Participant.Action Nat Ty services (ScalarValue F F))
  | action@(.send ..), position => ⟨.returned (), position + 1, [action]⟩
  | action@(.query ..), position =>
      ⟨.returned (if position = 3 then first else second), position + 1, [action]⟩
  | action@(.receive ty ..), position =>
      ⟨.returned (match ty with
        | .boolean => false
        | .field _ => received prover first second position
        | .group _ => 0
        | .service _ => 0), position + 1, [action]⟩

omit [DecidableEq F] in
theorem handler_receive_field (prover : Strategy F) (first second : F) (domain site : String)
    (sender position : Nat) :
    transcriptHandler prover first second (.receive (.field domain) site sender) position =
      ⟨.returned (received prover first second position), position + 1, [.receive (.field domain) site sender]⟩ := rfl

omit [DecidableEq F] in
theorem handler_query (prover : Strategy F) (first second : F) (site domain : String)
    (args : Values (ScalarValue F F) (services.arguments domain)) (position : Nat) :
    transcriptHandler prover first second (.query site domain args) position =
      ⟨.returned (if position = 3 then first else second), position + 1, [.query site domain args]⟩ := rfl

omit [DecidableEq F] in
theorem handler_send (prover : Strategy F) (first second : F) (site : String)
    (receiver : Nat) {ty : Ty} (value : ScalarValue F F ty) (position : Nat) :
    transcriptHandler prover first second (.send site receiver value) position =
      ⟨.returned (), position + 1, [.send site receiver value]⟩ := rfl


def run (program : Verifier F) (statement : Statement F) (claim : F) (service : Nat)
    (prover : Strategy F) (first second : F) :=
  (program statement claim service).run (transcriptHandler prover first second) 0

/-- Reaching an opening includes both successful round guards. -/
def Reached (prover : Strategy F) (claim first : F) : Prop :=
  wireBoundary prover.rounds.first = claim ∧
    wireBoundary (prover.rounds.second first) = wireEvaluate prover.rounds.first first

def Accepted (checks : Checks F) (statement : Statement F) (prover : Strategy F)
    (claim first second : F) : Prop :=
  Reached prover claim first ∧
  checks.left statement (residual prover first second) (prover.left first second) = true ∧
  checks.right statement (residual prover first second)
    (prover.right first second (prover.left first second)) = true ∧
  (residual prover first second).claim =
    prover.left first second * prover.right first second (prover.left first second)

/-- The left check precedes the right check; a failed left check cannot expose
or charge a right opening. Terminal equality is not required for this event. -/
def BadOpening (checks : Checks F) (statement : Statement F) (prover : Strategy F)
    (claim first second : F) : Prop :=
  Reached prover claim first ∧
  checks.left statement (residual prover first second) (prover.left first second) = true ∧
  (prover.left first second ≠ value statement.left first second ∨
    (checks.right statement (residual prover first second)
      (prover.right first second (prover.left first second)) = true ∧
    prover.right first second (prover.left first second) ≠ value statement.right first second))

theorem experiment_accepted (wiring : Wiring) (checks : Checks F) (statement : Statement F)
    (claim : F) (service : Nat) (prover : Strategy F) (first second : F) :
    (run (experimentWith wiring checks) statement claim service prover first second).outcome =
      .returned (some true) ↔ Accepted checks statement prover claim first second := by
  by_cases hfirst : wireBoundary prover.rounds.first = claim
  all_goals by_cases hsecond : wireBoundary (prover.rounds.second first) = wireEvaluate prover.rounds.first first
  all_goals by_cases hleft : checks.left statement (residual prover first second) (prover.left first second) = true
  all_goals simp only [residual] at hleft
  all_goals simp only [run, experimentWith, rounds, roundsWith, standardArithmetic, terminal,
    PIR.Proc.bind, PIR.Proc.run, PIR.Execution.follow, handler_receive_field,
    handler_query, handler_send, received, Common.received, residual, Accepted, Reached,
    hfirst, hsecond, hleft, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceEqDiff]
  all_goals simp only [Bool.and_eq_true, decide_eq_true_eq,
    PIR.Outcome.returned.injEq, Option.some.injEq, true_and, false_and, reduceCtorEq]

theorem VerifierContract.accepted_iff {wiring : Wiring} {checks : Checks F} {program : Verifier F}
    (certificate : VerifierContract wiring checks program) (statement : Statement F)
    (claim : F) (service : Nat) (prover : Strategy F) (first second : F) :
    (run program statement claim service prover first second).outcome = .returned (some true) ↔
      Accepted checks statement prover claim first second := by
  unfold run
  rw [(certificate.realizes statement claim service).process_eq]
  exact experiment_accepted wiring checks statement claim service prover first second

theorem accepted_source_or_bad (checks : Checks F) (statement : Statement F) (prover : Strategy F)
    (claim first second : F) (accepted : Accepted checks statement prover claim first second) :
    Zkc.Protocols.Sumcheck.verify (polynomial (coefficients statement)) claim
      (Common.strategy prover.rounds) (first, second, ()) = true ∨
    BadOpening checks statement prover claim first second := by
  by_cases hl : prover.left first second = value statement.left first second
  · by_cases hr : prover.right first second (prover.left first second) = value statement.right first second
    · left
      have cert : Common.VerifierContract defaultWiring (Common.experiment defaultWiring (F := F)) :=
        ⟨fun _ _ _ => .refl _⟩
      rw [← cert.accepted_iff (coefficients statement) claim 0 prover.rounds first second,
        cert.run_outcome]
      rw [ite_eq_left accepted.1.1, ite_eq_left accepted.1.2]
      have terminalEq := accepted.2.2.2
      simp only [residual] at terminalEq
      rw [hr, hl, ← evaluate_product] at terminalEq
      simp only [terminalEq, decide_true]
    · exact Or.inr ⟨accepted.1, accepted.2.1, Or.inr ⟨accepted.2.2.1, hr⟩⟩
  · exact Or.inr ⟨accepted.1, accepted.2.1, Or.inl hl⟩
where
  defaultWiring : Common.Wiring := ⟨0, "F", ("a", "b", "c"), ("d", "e", "f"), "r", "s", "x", "y"⟩

theorem public_no_bad (statement : Statement F) (prover : Strategy F) (claim first second : F) :
    ¬ BadOpening publicChecks statement prover claim first second := by
  simp [BadOpening, publicChecks, residual]

def honestStrategy (statement : Statement F) : Strategy F :=
  ⟨Common.honestStrategy (coefficients statement), value statement.left,
    fun first second _ => value statement.right first second⟩

theorem VerifierContract.completeness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring publicChecks program) (statement : Statement F)
    (service : Nat) (first second : F) :
    (run program statement (polynomial (coefficients statement)).booleanSum service
      (honestStrategy statement) first second).outcome = .returned (some true) := by
  have direct : Common.VerifierContract wiring.rounds (Common.experiment wiring.rounds (F := F)) :=
    ⟨fun _ _ _ => .refl _⟩
  have honest := direct.completeness (coefficients statement) service first second
  rw [direct.run_outcome] at honest
  split at honest
  next hfirst =>
    split at honest
    next hsecond =>
      have last : wireEvaluate ((Common.honestStrategy (coefficients statement)).second first) second =
          Common.evaluate (coefficients statement) first second := by simpa using honest
      rw [certificate.accepted_iff]
      refine ⟨⟨hfirst, hsecond⟩, ?_, ?_, ?_⟩
      · simp [publicChecks, honestStrategy, residual]
      · simp [publicChecks, honestStrategy, residual]
      · exact last.trans (evaluate_product statement first second)
    next => cases honest
  next => cases honest


end Zkc.Protocols.Sumcheck.FactorOpening
