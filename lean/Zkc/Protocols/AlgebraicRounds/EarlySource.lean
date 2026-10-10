import Zkc.Semantics.ExecutionPath
import Zkc.Protocols.AlgebraicRounds.Early

set_option autoImplicit false
namespace Zkc.Protocols.AlgebraicRounds.EarlySource
open PIR
open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.AlgebraicRounds.Early Zkc.Protocols.AlgebraicRounds.BlockEvaluation

inductive Role where | prover | verifier
  deriving DecidableEq, Repr
inductive Op where | message | challenge | reject
  deriving DecidableEq, Repr
def sig (F : Type) : Signature := ⟨Op, fun
  | .message => Message F
  | .challenge => F
  | .reject => Unit⟩

/-- The phase is specification state, not an input given to every endpoint. -/
inductive Phase (F : Type) where
  | message : Nat → F → Phase F
  | challenge : Nat → Message F → Phase F
  | reject | finished

variable {F S Q : Type} [CommRing F] [DecidableEq F]

def start : Nat → F → Phase F
  | 0, _ => .finished
  | n+1, claim => .message n claim

def interaction (evaluate : Round F → F) : Interaction (sig F) where
  Role := Role
  Phase := Phase F
  owner := fun | .message => .prover | _ => .verifier
  enabled := fun phase op => match phase, op with
    | .message _ _, .message | .challenge _ _, .challenge | .reject, .reject => True
    | _, _ => False
  advance := fun phase op reply => match phase, op with
    | .message n claim, .message =>
        if boundary (roundOf reply 0) = claim then .challenge n reply else .reject
    | .challenge n msg, .challenge => start n (evaluate (roundOf msg reply))
    | _, _ => .finished

/-- Uniform finite source. No honest-message predicate filters received values. -/
def source (evaluate : Round F → F) : Nat → F → Proc (sig F) F
  | 0, claim => .done claim
  | n+1, claim => .call .message fun msg =>
      if boundary (roundOf msg 0) = claim then
        .call .challenge fun r => source evaluate n (evaluate (roundOf msg r))
      else .call .reject fun _ => .halt .reject

theorem formed (evaluate : Round F → F) (n : Nat) (claim : F) :
    Conforms (interaction evaluate) (source evaluate n claim) (start n claim) := by
  induction n generalizing claim with
  | zero => trivial
  | succ n ih =>
    refine ⟨trivial, ?_⟩
    intro msg
    by_cases h : boundary (roundOf msg 0) = claim
    · simp only [Conforms, interaction, start, if_pos h]
      exact ⟨trivial, fun r => ih _⟩
    · simp only [Conforms, interaction, start, if_neg h]
      exact ⟨trivial, fun _ => trivial⟩

theorem bounded (evaluate : Round F → F) (n : Nat) (claim : F) :
    Within (2*n) (source evaluate n claim) := by
  induction n generalizing claim with
  | zero => trivial
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    intro msg
    by_cases h : boundary (roundOf msg 0) = claim
    · simp only [if_pos h, Within]
      exact fun r => ih _
    · simp [if_neg h, Within]

/-- Actual supplied endpoints: send sees only prover memory; react additionally
    receives the delivered challenge. Only draw receives provider state Q. -/
def handler (send : S → Message F × S) (react : S → F → S)
    (draw : Q → F × Q) : Handler (sig F) (S × Q) (Zkc.Protocols.AlgebraicRounds.Early.Event F)
  | .message, (ps, qs) =>
      let (msg, ps') := send ps
      ⟨.returned msg, (ps', qs), [.message msg]⟩
  | .challenge, (ps, qs) =>
      let (r, qs') := draw qs
      ⟨.returned r, (react ps r, qs'), [.challenge r]⟩
  | .reject, st => ⟨.returned (), st, [.reject]⟩

def embed (out : Zkc.Protocols.AlgebraicRounds.Early.Execution F S Q) : PIR.Execution (S × Q) (Zkc.Protocols.AlgebraicRounds.Early.Event F) F :=
  ⟨match out.result with | none => .stopped .reject | some a => .returned a,
    (out.proverState, out.oracleState), out.trace⟩

/-- Exact connection to the existing early-stop interpreter, for every endpoint
    implementation and public finite round count, including hostile senders. -/
theorem execution_exact (evaluate : Round F → F) (send : S → Message F × S)
    (react : S → F → S) (draw : Q → F × Q) (n : Nat) (claim : F) (ps : S) (qs : Q) :
    (source evaluate n claim).run (handler send react draw) (ps, qs) =
      embed (Zkc.Protocols.AlgebraicRounds.Early.early evaluate send react draw n claim ps qs) := by
  induction n generalizing claim ps qs with
  | zero => rfl
  | succ n ih =>
    simp only [source, Proc.run, handler, Execution.follow, Zkc.Protocols.AlgebraicRounds.Early.early]
    split
    · simp only [Proc.run, handler, Execution.follow]
      rw [ih]
      rfl
    · rfl

omit [CommRing F] [DecidableEq F] in
/-- The next message and post-send local memory cannot use hidden provider state. -/
theorem send_hidden_independent (send : S → Message F × S) (react : S → F → S)
    (draw : Q → F × Q) (ps : S) (q t : Q) :
    (handler send react draw .message (ps,q)).outcome =
      (handler send react draw .message (ps,t)).outcome ∧
    (handler send react draw .message (ps,q)).state.1 =
      (handler send react draw .message (ps,t)).state.1 := ⟨rfl,rfl⟩

theorem actual_calls_permitted (evaluate : Round F → F) (n : Nat) (claim : F)
    (server : Handler (sig F) (S × Q) (Zkc.Protocols.AlgebraicRounds.Early.Event F)) (state : S × Q) :
    ∀ phase op, Sum.inl (phase,op) ∈
      ((source evaluate n claim).run (ExecutionPath.handler (interaction evaluate) server)
        (start n claim,state)).events → (interaction evaluate).enabled phase op :=
  ExecutionPath.calls_permitted (interaction evaluate) server _ _ _ (formed evaluate n claim)

/-- Supplied mathematical endpoint state is retained, not silently projected
    away on reject. This instance does not add source extraction for send/react. -/
theorem rejected_prefix :
    (source Zkc.Protocols.AlgebraicRounds.Scalar.value 1 (1 : Int)).run
      (handler Zkc.Protocols.AlgebraicRounds.Early.badSend Zkc.Protocols.AlgebraicRounds.Early.ignoreChallenge Zkc.Protocols.AlgebraicRounds.Early.counterDraw) ((),0) =
      ⟨.stopped .reject,((),0),[.message (0,0,0),.reject]⟩ := rfl

end Zkc.Protocols.AlgebraicRounds.EarlySource
