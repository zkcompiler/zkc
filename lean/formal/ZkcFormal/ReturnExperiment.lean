module

public import ZkcFormal.OracleProcess
public import ZkcFormal.Samplers

@[expose] public section

/-!
The experiment of a bound on what a process returns.

A statement of soundness bounds the probability that a role returns. What that probability is
of, against which services, is said here once, as definitions of the library; a generated
statement applies them to the role, the inputs and the bound that it read from the source, and
says nothing of its own about services.

- `Service.Conforms`: the services that a statement is about. A conforming service is no more
  likely to answer an effect within a set of replies than the sampler of the effect is to draw
  one there, and it answers only what is allowed. It may also not answer, and it may keep a
  state.
- `ReturnsWithin p samplers allowed bad limit`: against every conforming service, from every
  state, the simulation of `p` by the service's handler returns a value of `bad` with
  probability at most `limit`. A protocol that decides has `bad` true of everything: the event
  is that the role returns. A reduction has `bad` true of the results on which the reduced
  statement holds.
- `Served samplers allowed`: there is a conforming service with a state, so that a statement
  with `ReturnsWithin` is not about nothing.

The bridge from a judgment with fees to the experiment is in `ZkcFormal.ChargedReturn`.
-/

namespace ZkcFormal.ProbabilisticProcess
open Zkc.Core OracleComp
open scoped NNRat ENNReal

variable {S : Sig} {H A σ : Type}

/-- A service that a statement of soundness is about: it draws within the samplers and answers
only what is allowed. -/
structure Service.Conforms (service : Service S σ) (samplers : Samplers S)
    (allowed : ∀ op, S.Reply op → Prop) : Prop where
  /-- At an effect with a sampler, in every state, a set of replies has at most the probability
  under the service that it has under the sampler. -/
  follows : service.Follows samplers
  /-- What the service answers is allowed. -/
  permitted : ∀ op s reply t, (some reply, t) ∈ support (service op s) → allowed op reply

/-- **The experiment of a bound on returns.** Against every conforming service, from every
state, the simulation of the process by the service's handler returns a value of `bad` with
probability at most `limit`. -/
def ReturnsWithin (p : Process S H A) (samplers : Samplers S)
    (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop) (limit : ℝ≥0∞) : Prop :=
  ∀ (σ : Type) (service : Service S σ), service.Conforms samplers allowed → ∀ s : σ,
    Pr{let out ← (simulateQ (handlerOf service) (embed p)).run.run s}[
      ∃ a, out.1 = some (.inl a) ∧ bad a] ≤ limit

/-- There is a conforming service with a state. -/
def Served (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) : Prop :=
  ∃ (σ : Type) (service : Service S σ), Nonempty σ ∧ service.Conforms samplers allowed

/-- A bound on returns holds with every larger limit. -/
theorem ReturnsWithin.mono {p : Process S H A} {samplers : Samplers S}
    {allowed : ∀ op, S.Reply op → Prop} {bad : A → Prop} {limit larger : ℝ≥0∞}
    (within : ReturnsWithin p samplers allowed bad limit) (le : limit ≤ larger) :
    ReturnsWithin p samplers allowed bad larger :=
  fun σ service conforms s => (within σ service conforms s).trans le

/-- A bound on the probability that the simulation returns, against every conforming service, is
the experiment with the event that the process returns. -/
theorem returnsWithin_of_returns (p : Process S H A) (samplers : Samplers S)
    (allowed : ∀ op, S.Reply op → Prop) (limit : ℝ≥0∞)
    (returns : ∀ {σ : Type} (service : Service S σ), service.Follows samplers →
      (∀ op s reply t, (some reply, t) ∈ support (service op s) → allowed op reply) → ∀ s : σ,
      Pr{let out ← (simulateQ (handlerOf service) (embed p)).run.run s}[
        ∃ a, out.1 = some (.inl a)] ≤ limit) :
    ReturnsWithin p samplers allowed (fun _ => True) limit := by
  intro σ service conforms s
  simpa using returns service conforms.follows conforms.permitted s

/-- What a bound on every return says of the simulation: the probability that it returns. -/
theorem ReturnsWithin.returns {p : Process S H A} {samplers : Samplers S}
    {allowed : ∀ op, S.Reply op → Prop} {limit : ℝ≥0∞}
    (within : ReturnsWithin p samplers allowed (fun _ => True) limit)
    (service : Service S σ) (conforms : service.Conforms samplers allowed) (s : σ) :
    Pr{let out ← (simulateQ (handlerOf service) (embed p)).run.run s}[
      ∃ a, out.1 = some (.inl a)] ≤ limit := by
  simpa using within σ service conforms s

end ZkcFormal.ProbabilisticProcess
