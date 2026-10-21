module

public import ZkcArkLib.Sumcheck.Message
public import Zkc.Protocols.Sumcheck.Common
public import ZkcSecurity.Families.Sumcheck.Common
public import Zkc.Semantics.MonadExecution

@[expose] public section

/-! Close actual PIR execution with causal messages and fresh VCVio challenges.
The second message reads the first challenge from reached handler state. It has
no access to the second challenge. All operations retain their ordered events.
-/

namespace ZkcSecurity.ArkLib.Sumcheck
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.Sumcheck.Common
open OracleSpec OracleComp

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]

abbrev Event (F : Type) := Participant.Action Nat Ty services (ScalarValue F F)

def handler (prover : Strategy F) :
    PIR.MonadHandler ProbComp (actions (F := F)) (Nat × F) (Event F)
  | action@(.send ..), (position, first) =>
      pure ⟨.returned (), (position + 1, first), [action]⟩
  | action@(.query ..), (position, first) => do
      let challenge ← $ᵗ F
      pure ⟨.returned challenge, (position + 1, if position = 3 then challenge else first), [action]⟩
  | action@(.receive ty ..), (position, first) =>
      pure ⟨.returned (match ty with
        | .boolean => false
        | .field _ => received prover first position
        | .group _ => 0
        | .service _ => 0), (position + 1, first), [action]⟩

omit [DecidableEq F] in
theorem handler_receive_field (prover : Strategy F) (site domain : String)
    (sender position : Nat) (first : F) :
    handler prover (.receive (.field domain) site sender) (position, first) =
      pure ⟨.returned (received prover first position), (position + 1, first),
        [.receive (.field domain) site sender]⟩ := rfl

omit [DecidableEq F] in
theorem handler_send (prover : Strategy F) (site : String) (receiver position : Nat)
    (first : F) {ty : Ty} (value : ScalarValue F F ty) :
    handler prover (.send site receiver value) (position, first) =
      pure ⟨.returned (), (position + 1, first), [.send site receiver value]⟩ := rfl

omit [DecidableEq F] in
theorem handler_query (prover : Strategy F) (site domain : String)
    (args : Values (ScalarValue F F) (services.arguments domain)) (position : Nat) (first : F) :
    handler prover (.query site domain args) (position, first) =
      (do let challenge ← $ᵗ F
          return ⟨.returned challenge, (position + 1, if position = 3 then challenge else first),
            [.query site domain args]⟩) := rfl

def execution (program : Verifier F) (coefficients : Coefficients F)
    (claim : F) (service : Nat) (prover : Strategy F) :
    ProbComp (PIR.Execution (Nat × F) (Event F) (Option Bool)) :=
  (program coefficients claim service).runM (handler prover) (0, 0)

/-- Only acceptance is observed by this security game. Rejection branches in
`execution` retain their precise state and event prefixes. -/
def game (coefficients : Coefficients F) (claim : F) (prover : Strategy F) : ProbComp Prop := do
  if wireBoundary prover.first = claim then
    let first ← $ᵗ F
    if wireBoundary (prover.second first) = wireEvaluate prover.first first then
      let second ← $ᵗ F
      return wireEvaluate (prover.second first) second = evaluate coefficients first second
    else return False
  else return False

theorem execution_game {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (coefficients : Coefficients F)
    (claim : F) (service : Nat) (prover : Strategy F) :
    (do let result ← execution program coefficients claim service prover
        return result.outcome = .returned (some true)) = game coefficients claim prover := by
  rw [execution, (certificate.realizes coefficients claim service).process_eq]
  by_cases firstCheck : wireBoundary prover.first = claim
  · simp only [experiment, experimentWith, standardArithmetic, PIR.Proc.runM,
      PIR.Execution.followM, handler_receive_field, handler_send, handler_query, received,
      pure_bind, bind_assoc, Nat.reduceAdd, firstCheck, decide_true, ite_true, game]
    apply bind_congr
    intro first
    by_cases secondCheck : wireBoundary (prover.second first) = wireEvaluate prover.first first
    · simp only [PIR.Proc.runM, PIR.Execution.followM, handler_send,
        handler_query, pure_bind, bind_assoc, Nat.reduceAdd, Nat.reduceEqDiff,
        secondCheck, decide_true, ite_true, ite_false]
      apply bind_congr
      intro second
      simp
      exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩
    · simp [PIR.Proc.runM, secondCheck]
  · simp [experiment, experimentWith, standardArithmetic, PIR.Proc.runM,
      PIR.Execution.followM, handler_receive_field, received, firstCheck, game]

end ZkcSecurity.ArkLib.Sumcheck
