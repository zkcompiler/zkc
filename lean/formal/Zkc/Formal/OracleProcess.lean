module

public import Zkc.Formal.ProbabilisticProcess
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

/-!
A process as a computation with oracles, and its run as a simulation.

A signature of effects is a specification of oracles: an effect is a query and its replies are
the answers. A process is then a computation that asks those oracles (`embed`), and a service is
a handler of their queries in the monad of a state under a possible failure (`handlerOf`); every
handler of that monad is the handler of a service. The run of a process against a service is
VCVio's simulation of the embedded process by that handler (`run_eq_simulateQ`), so an event of
the run has the probability of the same event of the simulation (`prEvent_run`).

A result about a compiled program is stated about the simulation. `run` stays the form in which
proofs work, since it is defined by the process's own fold.
-/

namespace Zkc.Formal.ProbabilisticProcess
open Core OracleComp

variable {S : Sig} {H A σ : Type}

/-- A signature of effects as a specification of oracles. -/
def specOf (S : Sig) : OracleSpec S.Op := fun op => S.Reply op

/-- A process as a computation with oracles. A stop is a value of the computation, beside a
result. -/
def embed : Process S H A → OracleComp (specOf S) (A ⊕ H)
  | .done a => pure (.inl a)
  | .halt h => pure (.inr h)
  | .call op next => OracleComp.queryBind (spec := specOf S) op fun reply => embed (next reply)

/-- A service as a handler. No answer is the failure of `OptionT`, and the state is kept under
it: `OptionT (StateT σ ProbComp) α` is `σ → ProbComp (Option α × σ)`. -/
def handlerOf (service : Service S σ) : QueryImpl (specOf S) (OptionT (StateT σ ProbComp)) :=
  fun op => OptionT.mk fun s => service op s

/-- A handler as a service. -/
def serviceOf (handler : QueryImpl (specOf S) (OptionT (StateT σ ProbComp))) : Service S σ :=
  fun op s => (handler op).run.run s

/-- Every handler is the handler of a service: a statement for every service is a statement for
every handler. -/
theorem handlerOf_serviceOf (handler : QueryImpl (specOf S) (OptionT (StateT σ ProbComp))) :
    handlerOf (serviceOf handler) = handler := rfl

theorem serviceOf_handlerOf (service : Service S σ) : serviceOf (handlerOf service) = service :=
  rfl

/-- What the simulation gives, as an outcome of the run. -/
def outcomeOf : Option (A ⊕ H) → Outcome H A
  | none => .unavailable
  | some (.inl a) => .returned a
  | some (.inr h) => .halted h

theorem outcomeOf_eq_returned {o : Option (A ⊕ H)} {a : A} :
    outcomeOf o = .returned a ↔ o = some (.inl a) := by
  rcases o with _ | a' | h <;> simp [outcomeOf]

/-- The run of a process against a service is the simulation of the embedded process by the
service's handler. -/
theorem run_eq_simulateQ (service : Service S σ) (p : Process S H A) (s : σ) :
    run service p s =
      (fun out => (outcomeOf out.1, out.2)) <$>
        ((simulateQ (handlerOf service) (embed p)).run.run s) := by
  induction p generalizing s with
  | done a => simp [run, Process.interpret, embed, outcomeOf]
  | halt h => simp [run, Process.interpret, embed, outcomeOf]
  | call op next ih =>
    have step : simulateQ (handlerOf service)
        (OracleComp.queryBind (spec := specOf S) op fun reply => embed (next reply)) =
        handlerOf service op >>= fun reply => simulateQ (handlerOf service) (embed (next reply)) :=
      rfl
    have runs : run service (.call op next) s = (do
        let (reply, state) ← service op s
        match reply with
        | none => pure (.unavailable, state)
        | some v => run service (next v) state) := rfl
    rw [runs, embed, step]
    simp only [OptionT.run_bind, handlerOf, Option.elimM, StateT.run_bind, map_bind]
    refine bind_congr fun out => ?_
    obtain ⟨reply, state⟩ := out
    cases reply with
    | none => rfl
    | some v => exact ih v state

/-- An event of the run's outcome has the probability of the same event of the simulation. -/
theorem prEvent_run (service : Service S σ) (p : Process S H A) (s : σ)
    (event : Outcome H A → Prop) :
    Pr{let out ← run service p s}[event out.1] =
      Pr{let out ← (simulateQ (handlerOf service) (embed p)).run.run s}[
        event (outcomeOf out.1)] := by
  rw [run_eq_simulateQ, prEvent_map]

/-- The simulation returns with the probability with which the run does. -/
theorem prEvent_simulation_returns (service : Service S σ) (p : Process S H A) (s : σ) :
    Pr{let out ← (simulateQ (handlerOf service) (embed p)).run.run s}[
        ∃ a, out.1 = some (.inl a)] =
      Pr{let out ← run service p s}[∃ a, out.1 = .returned a] := by
  rw [prEvent_run service p s fun outcome => ∃ a, outcome = .returned a]
  exact prEvent_congr _ _ _ fun out =>
    exists_congr fun _ => outcomeOf_eq_returned.symm

end Zkc.Formal.ProbabilisticProcess
