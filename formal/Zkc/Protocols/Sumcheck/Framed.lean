import Zkc.Protocols.Sumcheck.Source
import Zkc.Protocols.Sumcheck.Optimization
import Zkc.Polynomial.Encoding
import Zkc.Protocols.AlgebraicRounds.Framed
import Zkc.Semantics.EventInvariant

/-! Canonical framing of the complete Sumcheck statement and actual source.

The typed root binds the domain, dimension, initial claim and injectively encoded
ordered coefficient object. This is logical statement binding and execution
correspondence. Byte encoding, random-oracle interpretation and FS security are
separate obligations; ordinary interactive soundness does not prove them.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Framed

open PIR Zkc.Source Zkc.Polynomial
open AlgebraicRounds (Message)
open AlgebraicRounds.Construction (Frame Event Query)

variable {F S Q : Type} {n : Nat}

def root (domain : String) (p : Quadratic F n) (claim : F) : List (Frame F) :=
  [.context domain n claim, .statement "sumcheck.quadratic.v1" p.coefficients]

def initial (domain : String) (p : Quadratic F n) (claim : F) (prover : S) (provider : Q) :
    AlgebraicRounds.Framed.State F S Q := ⟨prover, provider, root domain p claim, 0⟩

theorem root_injective (domain otherDomain : String) (p q : Quadratic F n) (claim otherClaim : F)
    (same : root domain p claim = root otherDomain q otherClaim) :
    domain = otherDomain ∧ claim = otherClaim ∧ p = q := by
  have first := List.cons.inj same |>.1
  have second := List.cons.inj (List.cons.inj same |>.2) |>.1
  cases first
  exact ⟨rfl, rfl, Quadratic.coefficients_injective (Frame.statement.inj second).2⟩

def HasRoot (frames : List (Frame F)) (state : AlgebraicRounds.Framed.State F S Q) : Prop :=
  ∃ suffix, state.frames = frames ++ suffix

def BoundQuery (frames : List (Frame F)) : Event F → Prop
  | .query request => ∃ suffix, request = frames ++ suffix
  | _ => True

theorem handler_preserves (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (frames : List (Frame F)) :
    (AlgebraicRounds.Framed.handler send react query).Preserves (HasRoot frames) := by
  intro op state initial
  rcases initial with ⟨suffix, same⟩
  cases op with
  | receive =>
      cases sent : send state.prover
      exact ⟨suffix, by simpa [AlgebraicRounds.Framed.handler, sent] using same⟩
  | absorb message =>
      exact ⟨suffix ++ [.message state.position message], by
        simp [AlgebraicRounds.Framed.handler, same, List.append_assoc]⟩
  | sample | reject => exact ⟨suffix, same⟩
  | squeeze =>
      cases queried : query (state.frames ++ [.request state.position]) state.provider with
      | mk outcome next =>
          cases outcome with
          | stopped why =>
              exact ⟨suffix ++ [.request state.position], by
                simp only [AlgebraicRounds.Framed.handler, queried]
                simp [same, List.append_assoc]⟩
          | returned r =>
              exact ⟨suffix ++ [.request state.position, .challenge state.position r], by
                simp only [AlgebraicRounds.Framed.handler, queried]
                simp [same, List.append_assoc]⟩

theorem handler_emits (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (frames : List (Frame F)) :
    (AlgebraicRounds.Framed.handler send react query).Emits (HasRoot frames) (BoundQuery frames) := by
  intro op state initial event member
  rcases initial with ⟨suffix, same⟩
  cases op with
  | receive =>
      cases sent : send state.prover
      simp [AlgebraicRounds.Framed.handler, sent] at member
      subst event
      trivial
  | absorb message | sample => simp [AlgebraicRounds.Framed.handler] at member
  | reject =>
      simp [AlgebraicRounds.Framed.handler] at member
      subst event
      trivial
  | squeeze =>
      have bound : BoundQuery frames (.query (state.frames ++ [.request state.position])) :=
        ⟨suffix ++ [.request state.position], by simp [same, List.append_assoc]⟩
      cases queried : query (state.frames ++ [.request state.position]) state.provider with
      | mk outcome next =>
          cases outcome with
          | stopped why =>
              simp [AlgebraicRounds.Framed.handler, queried] at member
              subst event
              exact bound
          | returned r =>
              simp [AlgebraicRounds.Framed.handler, queried] at member
              rcases member with rfl | rfl
              · exact bound
              · trivial

variable [CommSemiring F] [DecidableEq F]

/-- Independent recursive framed-round execution, retaining the delivered point. -/
def reference (send : S → Message F × S) (react : S → F → S) (query : Query F Q) :
    Nat → Source.Accumulator F → AlgebraicRounds.Framed.State F S Q →
      PIR.Execution (AlgebraicRounds.Framed.State F S Q) (Event F) (Source.Accumulator F)
  | 0, accumulator, state => ⟨.returned accumulator, state, []⟩
  | count + 1, accumulator, state =>
      let (message, nextProver) := send state.prover
      let absorbed := state.frames ++ [.message state.position message]
      if message.boundary = accumulator.claim then
        let request := absorbed ++ [.request state.position]
        let (outcome, nextProvider) := query request state.provider
        match outcome with
        | .stopped why =>
            ⟨.stopped why, ⟨nextProver, nextProvider, request, state.position⟩,
              [.message message, .query request]⟩
        | .returned challenge =>
            let nextState := ⟨react nextProver challenge, nextProvider,
              request ++ [.challenge state.position challenge], state.position + 1⟩
            let tail := reference send react query count (Source.advance message challenge accumulator) nextState
            ⟨tail.outcome, tail.state,
              .message message :: .query request :: .challenge challenge :: tail.events⟩
      else ⟨.stopped .reject,
        ⟨nextProver, state.provider, absorbed, state.position⟩, [.message message, .reject]⟩

theorem execution_exact (send : S → Message F × S) (react : S → F → S) (query : Query F Q)
    (count : Nat) (accumulator : Source.Accumulator F) (state : AlgebraicRounds.Framed.State F S Q) :
    ((Source.rounds count accumulator).interpret AlgebraicRounds.Construction.framed).run
      (AlgebraicRounds.Framed.handler send react query) state =
        reference send react query count accumulator state := by
  induction count generalizing accumulator state with
  | zero => rfl
  | succ count ih =>
      cases sent : send state.prover with
      | mk message nextProver =>
          by_cases accepted : message.boundary = accumulator.claim
          · cases queried : query
              (state.frames ++ [.message state.position message, .request state.position])
              state.provider with
            | mk outcome nextProvider =>
                cases outcome <;>
                  simp [Source.rounds, Proc.interpret, AlgebraicRounds.Construction.framed,
                    Proc.bind, Proc.run, AlgebraicRounds.Framed.handler, reference,
                    PIR.Execution.follow, sent, accepted, queried, ih]
          · simp [Source.rounds, Proc.interpret, AlgebraicRounds.Construction.framed,
              Proc.bind, Proc.run, AlgebraicRounds.Framed.handler, reference,
              PIR.Execution.follow, sent, accepted]

def run (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (p : Quadratic F n) (claim : F) (prover : S) (provider : Q) :
    PIR.Execution (AlgebraicRounds.Framed.State F S Q) (Event F) Bool :=
  ((Source.program n).denote (Source.meaning.translate AlgebraicRounds.Construction.framed)
    (Values.cons (ty := Source.Ty.accumulator) ⟨claim, []⟩
      (Values.cons (ty := Source.Ty.polynomial) p .nil)).get).run
    (AlgebraicRounds.Framed.handler send react query) (initial domain p claim prover provider)

theorem run_exact (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (p : Quadratic F n) (claim : F) (prover : S) (provider : Q) :
    run domain send react query p claim prover provider =
      (reference send react query n ⟨claim, []⟩ (initial domain p claim prover provider)).follow
        (fun accumulator state => ⟨.returned (Source.terminal p accumulator), state, []⟩) := by
  rw [run, Program.denote_translate, Source.program_denote, Proc.interpret_bind, PIR.run_bind,
    execution_exact]
  rfl

/-- The checked arithmetic interpretation remains valid under this different
construction. This is execution preservation, not a security reduction. -/
theorem optimized_exact (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (p : Quadratic F n) (claim : F) (prover : S) (provider : Q) :
    ((Source.program n).denote (Optimization.meaning.translate AlgebraicRounds.Construction.framed)
      (Values.cons (ty := Source.Ty.accumulator) ⟨claim, []⟩
        (Values.cons (ty := Source.Ty.polynomial) p .nil)).get).run
      (AlgebraicRounds.Framed.handler send react query) (initial domain p claim prover provider) =
        run domain send react query p claim prover provider := by
  simp only [run, Program.denote_translate, Optimization.denotation_exact (n := n)]

theorem root_retained (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (p : Quadratic F n) (claim : F) (prover : S) (provider : Q) :
    HasRoot (root domain p claim) (run domain send react query p claim prover provider).state := by
  apply Proc.run_invariant _ _ (handler_preserves send react query (root domain p claim))
  exact ⟨[], by simp [initial]⟩

/-- Every actual query event retains the same complete public statement root,
including an attempted query whose provider stops. -/
theorem queries_bound (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : Query F Q) (p : Quadratic F n) (claim : F) (prover : S) (provider : Q) :
    ∀ event ∈ (run domain send react query p claim prover provider).events,
      BoundQuery (root domain p claim) event := by
  apply Proc.run_events _ _ _ (handler_preserves send react query (root domain p claim))
    (handler_emits send react query (root domain p claim))
  exact ⟨[], by simp [initial]⟩

end Zkc.Protocols.Sumcheck.Framed
