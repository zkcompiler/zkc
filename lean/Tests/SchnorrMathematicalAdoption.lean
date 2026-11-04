import ZkcExamples.Structured.SchnorrContract
import ZkcExamples.Construction.SchnorrAndExecution
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Full-outcome and refusal controls for actual Schnorr and AND roots. -/
set_option autoImplicit false
set_option smartUnfolding false

namespace Tests.SchnorrMathematicalAdoption
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcExamples.Construction

/-- The handler records the request that stops, its post-state and all earlier
requests. No later request runs after that stop. -/
def countedHandler {F G : Type} (script : ReplyScript F G) (stopAt : Nat) (why : PIR.Stop) :
    PIR.Handler (participantInterface F G) Nat (participantInterface F G).Op :=
  fun action state ↦
    if state = stopAt then ⟨.stopped why, state + 1, [action]⟩
    else ⟨(script.handler action ()).outcome, state + 1, [action]⟩

/-- Every optional result is reflected. This quantifies over none, some false
and some true and over arbitrary residual state and event lists. -/
example (decision : Option Bool) (state : Nat) (events : List String) :
    ((⟨.returned decision, state, events⟩ : PIR.Execution Nat String (Option Bool)).follow
      (fun value current ↦ ⟨.returned (some value), current, []⟩)).outcome =
        .returned (some decision) := rfl

example (decision : Option Bool) (why : PIR.Stop) (state : Nat) (events : List String) :
    ((⟨.stopped why, state, events⟩ : PIR.Execution Nat String (Option Bool)).follow
      (fun value current ↦ ⟨.returned (some value), current, []⟩)).outcome ≠
        .returned (some decision) := by
  intro impossible
  cases impossible

/-- Dropping absence makes false and absent decisions indistinguishable. -/
example : (none : Option Bool).getD false = (some false).getD false ∧
    (none : Option Bool) ≠ some false := ⟨rfl, by decide⟩

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

example (base key : G) (secret challenge : F) (service : Nat) (why : PIR.Stop) :
    (SchnorrInteractive.program.participant F G 0
      (SchnorrInteractive.proverInputs base key secret service)).run
        (SchnorrHonestProver.replyHandler service (.stopped why) (.returned challenge)) () =
      ⟨.stopped why, (), [.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil)]⟩ := by
  rw [SchnorrHonestProver.full_execution_eq, SchnorrHonestProver.nonce_stopped]
  rfl

example (base key : G) (secret nonce : F) (service : Nat) (why : PIR.Stop) :
    (SchnorrInteractive.program.participant F G 0
      (SchnorrInteractive.proverInputs base key secret service)).run
        (SchnorrHonestProver.replyHandler service (.returned nonce) (.stopped why)) () =
      ⟨.stopped why, (),
        [.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil),
         .send (ty := .group groupDomain) SchnorrInteractive.wiring.commitmentSite 1 (nonce • base),
         .receive (.field scalarDomain) SchnorrInteractive.wiring.deliverySite 1]⟩ := by
  rw [SchnorrHonestProver.full_execution_eq, SchnorrHonestProver.challenge_stopped]
  rfl

/-- Actual missing public input retains an absent decision after the full
interaction; it does not become false or a stop. -/
example (base : G) (service : Nat) (commitment : G) (challenge response : F) :
    ((SchnorrInteractive.program.participant F G 1
      (.cons (some base) (.cons none (.cons none (.cons none (.cons (some service) .nil)))))).run
        (SchnorrInteractiveNormalForms.verifierReplies commitment challenge response).handler
        ()).outcome = .returned (.cons none .nil) := by
  rfl

/-- False is returned as false, with the ordinary verifier equation unchanged. -/
example (base key : G) (service : Nat) (prover : Zkc.Protocols.Schnorr.Common.Strategy F G)
    (challenge : F)
    (refuses : prover.response challenge • base ≠ prover.commitment + challenge • key) :
    (SchnorrExecution.execute base key service prover challenge).outcome =
      .returned (.cons (some false) .nil) := by
  apply (SchnorrExecution.returned_iff ..).mpr
  change ((SchnorrInteractive.verifier base key service).run
    (Zkc.Protocols.Schnorr.Common.transcriptHandler prover challenge) ()).outcome = _
  rw [SchnorrInteractive.verifier_correspondence]
  change PIR.Outcome.returned (some (decide _)) = .returned (some false)
  simp only [refuses, decide_false]

/-- All six AND verifier stopping positions and every stop reason retain the
exact post-state and reached prefix, including a stopped send. -/
theorem and_verifier_stops (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (responses : F × F) (challenge : F)
    (stopAt : Fin 6) (why : PIR.Stop) :
    let script := SchnorrAndExecution.verifierReplies commitments responses challenge
    let result := SchnorrAndExecution.execute firstBase firstKey secondBase secondKey service
      (countedHandler script stopAt.val why) 0
    (result.outcome, result.state, result.events) =
      (.stopped why, stopAt.val + 1,
        (SchnorrAndExecution.execute firstBase firstKey secondBase secondKey service
          script.handler ()).events.take (stopAt.val + 1)) := by
  dsimp only
  rw [SchnorrAndExecution.execute_eq, SchnorrAndProof.process_equation,
    SchnorrAndExecution.verifier_execution]
  fin_cases stopAt <;> rfl

/-- The actual producer's seven stopping positions cover both nonce queries,
both commitments, the shared receive and both responses. -/
theorem and_prover_stops (firstBase firstKey secondBase secondKey : G)
    (secrets nonces : F × F) (service : Nat) (challenge : F)
    (stopAt : Fin 7) (why : PIR.Stop) :
    let script := SchnorrAndExecution.proverReplies nonces challenge
    let root := SchnorrAndProof.program.participant F G 0
      (SchnorrAndExecution.proverInputs firstBase firstKey secondBase secondKey secrets service)
    let result := root.run (countedHandler script stopAt.val why) 0
    (result.outcome, result.state, result.events) =
      (.stopped why, stopAt.val + 1,
        (root.run script.handler ()).events.take (stopAt.val + 1)) := by
  dsimp only
  rw [SchnorrAndExecution.prover_full_execution, SchnorrAndExecution.prover_equation,
    SchnorrAndExecution.prover_execution]
  fin_cases stopAt <;> rfl

/-- A split-challenge transcript can satisfy each separate equation but is
refused by the real shared-challenge verifier. -/
example :
    (0 : Rat) = 0 + 0 * 1 ∧ (1 : Rat) = 0 + 1 * 1 ∧
    (SchnorrAndExecution.execute (F := Rat) (G := Rat) 1 1 1 1 0
      (SchnorrAndExecution.verifierReplies (0, 0) (0, 1) 0).handler ()).outcome =
        .returned (.cons (some false) .nil) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [SchnorrAndExecution.verifier_execution]
  norm_num

/-- Equal challenges permit acceptance but give no nonzero difference for
the registered recovery. The zero quotient fails on this nonzero key. -/
example :
    (SchnorrAndExecution.execute (F := Rat) (G := Rat) 1 1 1 1 0
      (SchnorrAndExecution.verifierReplies (0, 0) (0, 0) 0).handler ()).outcome =
        .returned (.cons (some true) .nil) ∧
      ((0 - 0 : Rat) / (0 - 0)) ≠ 1 := by
  constructor
  · apply (SchnorrAndExecution.accepted_iff ..).mpr
    norm_num
  · norm_num

/-- Changing the commitments between runs invalidates fixed recovery even
when both actual runs accept under distinct shared challenges. -/
example :
    (SchnorrAndExecution.execute (F := Rat) (G := Rat) 1 1 1 1 0
      (SchnorrAndExecution.verifierReplies (0, 0) (0, 0) 0).handler ()).outcome =
        .returned (.cons (some true) .nil) ∧
    (SchnorrAndExecution.execute (F := Rat) (G := Rat) 1 1 1 1 0
      (SchnorrAndExecution.verifierReplies (-1, -1) (0, 0) 1).handler ()).outcome =
        .returned (.cons (some true) .nil) ∧
      ((0 - 0 : Rat) / (0 - 1)) ≠ 1 := by
  refine ⟨?_, ?_, by norm_num⟩
  all_goals apply (SchnorrAndExecution.accepted_iff ..).mpr; norm_num

end Tests.SchnorrMathematicalAdoption
