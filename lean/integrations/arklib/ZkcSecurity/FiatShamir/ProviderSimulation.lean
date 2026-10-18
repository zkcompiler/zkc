module

public import ZkcSecurity.FiatShamir.Interface

@[expose] public section

/-! Provider simulations and their query-cost relation.

A provider realizes the ideal history oracle with primitive calls: compressions,
permutations or byte hashes, carrying chain or sponge states between calls. A
provider simulation relates the concrete experiment, in which the adversary
calls the primitive families directly and the verifier runs the provider, to the
ideal experiment over the history oracle of `ZkcSecurity.FiatShamir.Typed`. It
is stated for one property, one provider and one class of bounded executions.
This module fixes its type; it states no simulation of a particular provider.

- `Budget Family`: the primitive calls an adversary may make on every path, per
  primitive family. `FamilyQueryBound` is that bound on an oracle computation,
  and it implies a total bound of the summed budget
  (`FamilyQueryBound.isTotalQueryBound`).
- `Expansion.total`: the primitive calls of one verifier run within an
  execution bound, initialization included:
  `initialization + Σ_e n_e · v_e + Σ_r n_r · v_r`, with `v_e` and `v_r` the calls
  per absorbed event kind and per request kind and `n_e`, `n_r` their
  occurrence counts at the bound's maxima.
- `QueryCost`: the budget translation `cost : Budget Family → ℕ` (monotone), the
  verifier expansion `expansion : ExecBound → ℕ` and the loss
  `loss : Budget Family → ℕ → ENNReal`, applied to the adversary's budget and
  the verifier expansion. `QueryCost.ofCounts` aggregates an `Expansion` over
  the counts of each execution bound.
- On traces, an `Assignment` charges each primitive call, given the calls
  before it on its path, at most one TranscriptQuery, or none when a stated
  simulator answers it (`charged_length_le`). A grinding attempt is one
  TranscriptQuery whatever its primitive cost: in split-hash gate forms the two
  calls of one attempt are charged once (`ChargesAttemptsOnce`) and answered
  from one ideal answer.
- `Simulation`: the translation of adversaries, the query-cost relation, the
  transport of budgets to the translated adversary's total bound, and the
  inequality

  ```text
  concreteFailure A b ≤ idealFailure (translate A) b + loss q (expansion b)
  ```

  for every adversary `A` within the budget `q` and every execution bound `b`.
  The verifier's own TranscriptQueries are charged on the ideal side by the
  typed engine's validator cost, not by `cost`.

The transported total bound gives the pathwise weighted budget that the typed
engine consumes (`Simulation.weightedBudget`), and an ideal bound in the
translated adversary's query count transfers to the concrete experiment with
the loss added (`Simulation.concrete_le`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Provider
open OracleComp OracleSpec

/-- The primitive calls an adversary may make on every path, per primitive
family. -/
abbrev Budget (Family : Type) := Family → ℕ

section Bounds
variable {ι Family α : Type} {spec : OracleSpec ι} [DecidableEq Family]

/-- At most `budget f` calls of each primitive family `f` on every path, where
`family` sends a primitive query to its family. -/
def FamilyQueryBound (family : ι → Family) (computation : OracleComp spec α)
    (budget : Budget Family) : Prop :=
  IsQueryBound computation budget (fun query remaining => 0 < remaining (family query))
    (fun query remaining =>
      Function.update remaining (family query) (remaining (family query) - 1))

theorem familyQueryBound_query_bind_iff (family : ι → Family) {query : ι}
    {next : spec query → OracleComp spec α} {budget : Budget Family} :
    FamilyQueryBound family (liftM (spec.query query) >>= next) budget ↔
      0 < budget (family query) ∧ ∀ reply, FamilyQueryBound family (next reply)
        (Function.update budget (family query) (budget (family query) - 1)) :=
  Iff.rfl

/-- A bound per family bounds the total number of calls by the summed budget. -/
theorem FamilyQueryBound.isTotalQueryBound [Fintype Family] (family : ι → Family) :
    ∀ (computation : OracleComp spec α) (budget : Budget Family),
      FamilyQueryBound family computation budget →
        IsTotalQueryBound computation (∑ kind, budget kind) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind query next ih =>
      intro budget bounded
      obtain ⟨positive, rest⟩ := (familyQueryBound_query_bind_iff family).mp bounded
      have member : family query ∈ (Finset.univ : Finset Family) := Finset.mem_univ _
      have total : ∑ kind, budget kind = budget (family query) +
          ∑ kind ∈ Finset.univ.erase (family query), budget kind :=
        (Finset.add_sum_erase _ _ member).symm
      have updated : ∑ kind, Function.update budget (family query)
          (budget (family query) - 1) kind =
          (budget (family query) - 1) + ∑ kind ∈ Finset.univ.erase (family query), budget kind := by
        rw [Finset.sum_update_of_mem member, Finset.sdiff_singleton_eq_erase]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨?_, fun reply => ?_⟩
      · rw [total]
        omega
      · have bound := ih reply _ (rest reply)
        rw [updated] at bound
        refine bound.mono (le_of_eq ?_)
        rw [total]
        omega

end Bounds

section Expansion

/-- Occurrence counts of absorbed event kinds and request kinds in one verifier
run at an execution bound's maxima. -/
structure ExecutionCounts (EventKind RequestKind : Type) where
  events : EventKind → ℕ
  requests : RequestKind → ℕ

/-- A provider's primitive calls at initialization, per absorbed event kind and
per request kind. -/
structure Expansion (EventKind RequestKind : Type) where
  initialization : ℕ
  perEvent : EventKind → ℕ
  perRequest : RequestKind → ℕ

variable {EventKind RequestKind : Type} [Fintype EventKind] [Fintype RequestKind]

/-- The primitive calls of one verifier run within the counts, initialization
included. -/
def Expansion.total (expansion : Expansion EventKind RequestKind)
    (counts : ExecutionCounts EventKind RequestKind) : ℕ :=
  expansion.initialization + ∑ kind, counts.events kind * expansion.perEvent kind +
    ∑ kind, counts.requests kind * expansion.perRequest kind

/-- Initialization is part of every run's expansion. -/
theorem Expansion.initialization_le_total (expansion : Expansion EventKind RequestKind)
    (counts : ExecutionCounts EventKind RequestKind) :
    expansion.initialization ≤ expansion.total counts := by
  unfold Expansion.total
  omega

end Expansion

/-- The query-cost relation of a provider simulation, as consumed: the
TranscriptQuery budget `cost q` of the translated adversary for a primitive
budget `q` (monotone), the primitive calls `expansion b` of one verifier run
within the execution bound `b`, and the loss `loss q (expansion b)`. -/
structure QueryCost (Family ExecBound : Type) where
  cost : Budget Family → ℕ
  monotone : Monotone cost
  expansion : ExecBound → ℕ
  loss : Budget Family → ℕ → ENNReal

/-- A query-cost relation whose verifier expansion aggregates a provider's
per-step calls over the occurrence counts of each execution bound. -/
def QueryCost.ofCounts {Family ExecBound EventKind RequestKind : Type} [Fintype EventKind]
    [Fintype RequestKind] (cost : Budget Family → ℕ) (monotone : Monotone cost)
    (expansion : Expansion EventKind RequestKind)
    (counts : ExecBound → ExecutionCounts EventKind RequestKind)
    (loss : Budget Family → ℕ → ENNReal) : QueryCost Family ExecBound where
  cost := cost
  monotone := monotone
  expansion executions := expansion.total (counts executions)
  loss := loss

section Traces
variable {Call D : Type}

/-- On a trace, each primitive call, given the calls before it on its path, is
charged at most one TranscriptQuery, or none when a stated simulator answers
it. -/
abbrev Assignment (Call D : Type) := List Call → Call → Option D

/-- The TranscriptQueries charged along a trace, after the calls `earlier`. -/
def chargedAfter (assign : Assignment Call D) : List Call → List Call → List D
  | _, [] => []
  | earlier, call :: rest =>
      match assign earlier call with
      | some key => key :: chargedAfter assign (earlier ++ [call]) rest
      | none => chargedAfter assign (earlier ++ [call]) rest

/-- The TranscriptQueries charged along a trace of primitive calls. -/
def charged (assign : Assignment Call D) (trace : List Call) : List D :=
  chargedAfter assign [] trace

theorem chargedAfter_length_le (assign : Assignment Call D) :
    ∀ (trace earlier : List Call), (chargedAfter assign earlier trace).length ≤ trace.length
  | [], _ => by simp [chargedAfter]
  | call :: rest, earlier => by
      have tail := chargedAfter_length_le assign rest (earlier ++ [call])
      unfold chargedAfter
      cases assign earlier call <;> simp only [List.length_cons] <;> omega

/-- A trace is charged at most one TranscriptQuery per primitive call. -/
theorem charged_length_le (assign : Assignment Call D) (trace : List Call) :
    (charged assign trace).length ≤ trace.length :=
  chargedAfter_length_le assign trace []

/-- Split-hash grinding attempts are charged once: whenever `second` completes,
directly after `first`, the attempt `first` begins, `first` is charged the
attempt's TranscriptQuery and `second` is charged nothing, being answered from
the same ideal answer. -/
def ChargesAttemptsOnce (assign : Assignment Call D) (completes : Call → Call → Prop) : Prop :=
  ∀ earlier first second, completes first second →
    (assign earlier first).isSome ∧ assign (earlier ++ [first]) second = none

end Traces

/-- A provider simulation for one property, one provider and one class of
bounded executions. `concreteFailure A b` is the probability that the property
fails in the concrete experiment, with the adversary `A` calling the primitive
families and the verifier running the provider within the execution bound `b`;
`idealFailure A b` is the same in the ideal experiment over the history oracle
`OracleSpec.ofFn R`. -/
structure Simulation {ι D Family ExecBound α : Type} [DecidableEq Family]
    (primitive : OracleSpec ι) (family : ι → Family) (R : D → Type)
    (concreteFailure : OracleComp primitive α → ExecBound → ENNReal)
    (idealFailure : OracleComp (OracleSpec.ofFn R) α → ExecBound → ENNReal) where
  translate : OracleComp primitive α → OracleComp (OracleSpec.ofFn R) α
  queryCost : QueryCost Family ExecBound
  transport : ∀ adversary budget, FamilyQueryBound family adversary budget →
    IsTotalQueryBound (translate adversary) (queryCost.cost budget)
  bound : ∀ adversary budget executions, FamilyQueryBound family adversary budget →
    concreteFailure adversary executions ≤
      idealFailure (translate adversary) executions +
        queryCost.loss budget (queryCost.expansion executions)

namespace Simulation
variable {ι D Family ExecBound α : Type} [DecidableEq Family] {primitive : OracleSpec ι}
  {family : ι → Family} {R : D → Type}
  {concreteFailure : OracleComp primitive α → ExecBound → ENNReal}
  {idealFailure : OracleComp (OracleSpec.ofFn R) α → ExecBound → ENNReal}

/-- The translated adversary's charge on every path, each key weighted at most
`bound`, is at most its TranscriptQuery budget times `bound`: the weighted
budget of the typed engine. -/
theorem weightedBudget [∀ key, Nonempty (R key)]
    (simulation : Simulation primitive family R concreteFailure idealFailure)
    (weight : D → ENNReal) {bound : ENNReal} (bounded : ∀ key, weight key ≤ bound)
    (adversary : OracleComp primitive α) (budget : Budget Family)
    (within : FamilyQueryBound family adversary budget) :
    WorstCaseCostBound (simulation.translate adversary) ⟨weight⟩
      (simulation.queryCost.cost budget * bound) :=
  Typed.worstCaseCostBound_of_isTotalQueryBound weight bounded _ _
    (simulation.transport adversary budget within)

/-- An ideal bound in the adversary's query count transfers to the concrete
experiment with the loss added. -/
theorem concrete_le (simulation : Simulation primitive family R concreteFailure idealFailure)
    {idealBound : ℕ → ExecBound → ENNReal}
    (ideal : ∀ adversary queries executions, IsTotalQueryBound adversary queries →
      idealFailure adversary executions ≤ idealBound queries executions)
    (adversary : OracleComp primitive α) (budget : Budget Family) (executions : ExecBound)
    (within : FamilyQueryBound family adversary budget) :
    concreteFailure adversary executions ≤
      idealBound (simulation.queryCost.cost budget) executions +
        simulation.queryCost.loss budget (simulation.queryCost.expansion executions) :=
  (simulation.bound adversary budget executions within).trans
    (add_le_add_left (ideal _ _ executions (simulation.transport adversary budget within)) _)

end Simulation

end ZkcSecurity.FiatShamir.Provider
