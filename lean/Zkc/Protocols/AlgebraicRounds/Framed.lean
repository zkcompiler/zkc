import Zkc.Protocols.AlgebraicRounds.Construction

/-! Canonically framed logical Fiat-Shamir construction.

Each query binds the domain, initial claim, public round count, prior challenges,
current message and request position. Query state and the attempted request
are retained on failure. Frames are typed values, not a verified byte encoding.
The query implementation and its cryptographic assumptions are separate inputs.
An enclosing protocol must additionally bind its polynomial/relation statement;
that object is not represented by this round component's scalar initial claim.
-/

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.Framed

open PIR Construction

structure State (F S Q : Type) where
  prover : S
  provider : Q
  frames : List (Frame F)
  position : Nat
  deriving Repr

variable {F S Q : Type}

def initial (domain : String) (count : Nat) (claim : F) (prover : S) (provider : Q) :
    State F S Q := ⟨prover, provider, [.context domain count claim], 0⟩

def handler (send : S → Message F × S) (react : S → F → S) (query : Query F Q) :
    Handler (Construction.interface F) (State F S Q) (Event F)
  | .receive, state =>
      let (message, next) := send state.prover
      ⟨.returned message, { state with prover := next }, [.message message]⟩
  | .absorb message, state =>
      ⟨.returned (), { state with frames := state.frames ++ [.message state.position message] }, []⟩
  | .squeeze, state =>
      let request := state.frames ++ [.request state.position]
      let (outcome, next) := query request state.provider
      match outcome with
      | .stopped why =>
          ⟨.stopped why, { state with provider := next, frames := request }, [.query request]⟩
      | .returned challenge =>
          ⟨.returned challenge,
            ⟨react state.prover challenge, next,
              request ++ [.challenge state.position challenge], state.position + 1⟩,
            [.query request, .challenge challenge]⟩
  | .reject, state => ⟨.returned (), state, [.reject]⟩
  | .sample, state => ⟨.stopped .refused, state, []⟩

variable [Semiring F] [DecidableEq F]

/-- A direct recursive reference with explicit message absorption and query
ordering. It shares data definitions, but does not execute the constructed handler. -/
def reference (send : S → Message F × S) (react : S → F → S) (query : Query F Q) :
    Nat → F → State F S Q → Execution (State F S Q) (Event F) F
  | 0, claim, state => ⟨.returned claim, state, []⟩
  | count + 1, claim, state =>
      let (message, nextProver) := send state.prover
      let absorbed := state.frames ++ [.message state.position message]
      if message.boundary = claim then
        let request := absorbed ++ [.request state.position]
        let (outcome, nextProvider) := query request state.provider
        match outcome with
        | .stopped why =>
            ⟨.stopped why, ⟨nextProver, nextProvider, request, state.position⟩,
              [.message message, .query request]⟩
        | .returned challenge =>
            let nextState := ⟨react nextProver challenge, nextProvider,
              request ++ [.challenge state.position challenge], state.position + 1⟩
            let tail := reference send react query count (message.evaluate challenge) nextState
            ⟨tail.outcome, tail.state,
              .message message :: .query request :: .challenge challenge :: tail.events⟩
      else ⟨.stopped .reject,
        ⟨nextProver, state.provider, absorbed, state.position⟩, [.message message, .reject]⟩

theorem execution_exact (send : S → Message F × S) (react : S → F → S) (query : Query F Q)
    (count : Nat) (claim : F) (state : State F S Q) :
    ((rounds count claim).interpret framed).run (handler send react query) state =
      reference send react query count claim state := by
  induction count generalizing claim state with
  | zero => rfl
  | succ count ih =>
    cases sent : send state.prover with
    | mk message nextProver =>
      by_cases accepted : message.boundary = claim
      · cases queried : query
          (state.frames ++ [.message state.position message, .request state.position])
          state.provider with
        | mk outcome nextProvider =>
          cases outcome <;>
            simp [rounds, Proc.interpret, framed, Proc.bind, Proc.run,
              handler, reference, Execution.follow, sent, accepted, queried, ih]
      · simp [rounds, Proc.interpret, framed, Proc.bind, Proc.run,
          handler, reference, Execution.follow, sent, accepted]

theorem source_exact (send : S → Message F × S) (react : S → F → S) (query : Query F Q)
    (count : Nat) (env : Source.Environment (Value F) [.scalar]) (state : State F S Q) :
    ((program count).denote (meaning.translate framed) env).run (handler send react query) state =
      reference send react query count (env .here) state := by
  rw [structured_source, execution_exact]

/-- The entry point binds transcript initialization to the actual source's
public round count and claim; callers cannot substitute a different root frame. -/
def run (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (count : Nat) (claim : F) (prover : S) (provider : Q) :=
  ((program count).denote (meaning.translate framed)
    (Source.Values.cons (ty := Ty.scalar) claim .nil).get).run
      (handler send react query) (initial domain count claim prover provider)

theorem run_exact (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (count : Nat) (claim : F) (prover : S) (provider : Q) :
    run domain send react query count claim prover provider =
      reference send react query count claim (initial domain count claim prover provider) :=
  source_exact send react query count _ _

end Zkc.Protocols.AlgebraicRounds.Framed
