import Zkc.Protocols.AlgebraicRounds.Construction

/-! Interactive execution with an explicit fresh-challenge provider.

The operational provider may return or stop. Independence and distribution
premises belong to its probabilistic instantiation, not to this function type.
-/

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.Fresh

open PIR Construction

variable {F S Q : Type}

def handler (send : S → Message F × S) (react : S → F → S) (draw : Draw F Q) :
    Handler (Construction.interface F) (S × Q) (Event F)
  | .receive, (prover, provider) =>
      let (message, next) := send prover
      ⟨.returned message, (next, provider), [.message message]⟩
  | .sample, (prover, provider) =>
      let (outcome, next) := draw provider
      match outcome with
      | .stopped why => ⟨.stopped why, (prover, next), []⟩
      | .returned challenge =>
          ⟨.returned challenge, (react prover challenge, next), [.challenge challenge]⟩
  | .reject, state => ⟨.returned (), state, [.reject]⟩
  | .absorb _, state => ⟨.stopped .refused, state, []⟩
  | .squeeze, state => ⟨.stopped .refused, state, []⟩

variable [Semiring F] [DecidableEq F]

/-- Direct operational reference: it neither lowers nor calls the constructed
handler. Prover and provider residuals survive a failed challenge request. -/
def reference (send : S → Message F × S) (react : S → F → S) (draw : Draw F Q) :
    Nat → F → S → Q → Execution (S × Q) (Event F) F
  | 0, claim, prover, provider => ⟨.returned claim, (prover, provider), []⟩
  | count + 1, claim, prover, provider =>
      let (message, nextProver) := send prover
      if message.boundary = claim then
        let (outcome, nextProvider) := draw provider
        match outcome with
        | .stopped why => ⟨.stopped why, (nextProver, nextProvider), [.message message]⟩
        | .returned challenge =>
            let tail := reference send react draw count (message.evaluate challenge)
              (react nextProver challenge) nextProvider
            ⟨tail.outcome, tail.state, .message message :: .challenge challenge :: tail.events⟩
      else ⟨.stopped .reject, (nextProver, provider), [.message message, .reject]⟩

theorem execution_exact (send : S → Message F × S) (react : S → F → S) (draw : Draw F Q)
    (count : Nat) (claim : F) (prover : S) (provider : Q) :
    ((rounds count claim).interpret fresh).run (handler send react draw) (prover, provider) =
      reference send react draw count claim prover provider := by
  induction count generalizing claim prover provider with
  | zero => rfl
  | succ count ih =>
    cases sent : send prover with
    | mk message nextProver =>
      by_cases accepted : message.boundary = claim
      · cases drawn : draw provider with
        | mk outcome nextProvider =>
          cases outcome <;>
            simp [rounds, Proc.interpret, fresh, Proc.bind, Proc.run,
              handler, reference, Execution.follow, sent, accepted, drawn, ih]
      · simp [rounds, Proc.interpret, fresh, Proc.bind, Proc.run,
          handler, reference, Execution.follow, sent, accepted]

theorem source_exact (send : S → Message F × S) (react : S → F → S) (draw : Draw F Q)
    (count : Nat) (env : Source.Environment (Value F) [.scalar]) (prover : S) (provider : Q) :
    ((program count).denote (meaning.translate fresh) env).run
      (handler send react draw) (prover, provider) =
      reference send react draw count (env .here) prover provider := by
  rw [structured_source, execution_exact]

def run (send : S → Message F × S) (react : S → F → S) (draw : Draw F Q)
    (count : Nat) (claim : F) (prover : S) (provider : Q) :=
  ((program count).denote (meaning.translate fresh)
    (Source.Values.cons (ty := Ty.scalar) claim .nil).get).run
      (handler send react draw) (prover, provider)

theorem run_exact (send : S → Message F × S) (react : S → F → S) (draw : Draw F Q)
    (count : Nat) (claim : F) (prover : S) (provider : Q) :
    run send react draw count claim prover provider =
      reference send react draw count claim prover provider :=
  source_exact send react draw count _ _ _

end Zkc.Protocols.AlgebraicRounds.Fresh
