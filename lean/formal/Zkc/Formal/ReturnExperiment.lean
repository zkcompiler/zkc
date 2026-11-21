module

public import Zkc.Formal.OracleProcess
public import Zkc.Formal.ChargedProbability

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

`returnsWithin_of_charged` takes a judgment with fees within a budget to the experiment: a
process judged never to return a value of `bad`, with every fee within what the effect that
pays it is allowed, returns one with probability at most the budget.
-/

namespace Zkc.Formal.ProbabilisticProcess
open Core OracleComp
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

/-- **From the judgment with fees to the experiment.** A process that is judged, within a budget
and with every fee within what the effect that pays it is allowed, never to return a value of
`bad`, returns one with probability at most the budget. -/
theorem returnsWithin_of_charged (p : Process S H A) (samplers : Samplers S)
    (allowance : S.Op → ℚ≥0) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop) (budget : ℚ≥0)
    (judged : p.interpret (.charged allowed (paysWithin samplers allowance)) (fun a _ => ¬ bad a)
      (fun _ _ => True) budget) :
    ReturnsWithin p samplers allowed bad (toProbability budget) := by
  intro σ service conforms s
  have bound := allowed_bounds_probability service samplers allowance allowed bad conforms.permitted
    conforms.follows p budget s judged
  rw [prEvent_run service p s fun outcome => ∃ a, outcome = .returned a ∧ bad a] at bound
  refine le_trans (le_of_eq (prEvent_congr _ _ _ fun out => ?_)) bound
  exact exists_congr fun _ => and_congr_left fun _ => outcomeOf_eq_returned.symm

/-- A process that is judged never to return, within a budget and with every fee within what
the effect that pays it is allowed, returns with probability at most the budget. -/
theorem returnsWithin_of_never (p : Process S H A) (samplers : Samplers S)
    (allowance : S.Op → ℚ≥0) (allowed : ∀ op, S.Reply op → Prop) (budget : ℚ≥0)
    (judged : p.interpret (.charged allowed (paysWithin samplers allowance)) (fun _ _ => False)
      (fun _ _ => True) budget) :
    ReturnsWithin p samplers allowed (fun _ => True) (toProbability budget) :=
  returnsWithin_of_charged p samplers allowance allowed (fun _ => True) budget (by simpa using judged)

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

end Zkc.Formal.ProbabilisticProcess
