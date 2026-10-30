module

public import ZkcSecurity.ProgramLogic.Games.Relation
public import ZkcSecurity.Transformations.FiatShamir.ProviderSimulation

@[expose] public section

/-! # Provider simulations as stage relations

A provider simulation (`ZkcSecurity.FiatShamir.Provider.Simulation`) relates, at
one execution bound, the concrete game, in which the adversary calls the
primitive families within a per-family budget (`concreteGame`), to the ideal
game over the history oracle, in which a prover is admissible at its total
query count (`idealGame`). Its translation draws the private tape and runs the
adversary against the simulator; its budget map is the query-cost relation's
`cost`; its loss at a budget `q` is `loss q (expansion b)`, the verifier
expansion at the execution bound included. Every translated program is
admissible at `cost q` (`Simulation.transport`).

The simulation's inequality bounds the concrete failure by the ideal failure of
the translated mixture. When the ideal failure of a mixture is at most that of
its worst prover (`Mixes`), as for any event of an experiment run after drawing
the prover, the simulation is a stage relation (`Simulation.toRelation`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Provider
open OracleComp OracleSpec

variable {ι D Family ExecBound α : Type} [DecidableEq Family] [Fintype Family]
  {primitive : OracleSpec ι} {family : ι → Family} {R : D → Type}

/-- The concrete game at an execution bound: adversaries call the primitive
families, admissible within a budget per family. -/
def concreteGame (primitive : OracleSpec ι) (family : ι → Family)
    (concreteFailure : OracleComp primitive α → ExecBound → ENNReal) (executions : ExecBound) :
    Stage.Game where
  Adversary := OracleComp primitive α
  Budget := Budget Family
  Admissible budget adversary := FamilyQueryBound family adversary budget
  bad adversary := concreteFailure adversary executions

/-- The ideal game at an execution bound: provers on the history oracle,
admissible at their total query count; a prover's failure is that of the point
mixture. -/
def idealGame (R : D → Type)
    (idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal)
    (executions : ExecBound) : Stage.Game where
  Adversary := OracleComp (OracleSpec.ofFn R) α
  Budget := ℕ
  Admissible queries prover := IsTotalQueryBound prover queries
  bad prover := idealFailure (pure prover) executions

/-- The ideal failure of a mixture of provers is at most that of its worst
prover. -/
def Mixes (idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal)
    (executions : ExecBound) : Prop :=
  ∀ provers, idealFailure provers executions ≤
    ⨆ prover ∈ support provers, idealFailure (pure prover) executions

namespace Simulation
variable {concreteFailure : OracleComp primitive α → ExecBound → ENNReal}
  {idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal}

/-- A provider simulation as a stage relation, at one execution bound. -/
noncomputable def toRelation (simulation : Simulation primitive family R concreteFailure idealFailure)
    (executions : ExecBound) (mixes : Mixes idealFailure executions) :
    Stage.Relation (idealGame R idealFailure executions)
      (concreteGame primitive family concreteFailure executions) where
  translate budget adversary := simulation.translate budget adversary
  budget := simulation.queryCost.cost
  admissible budget adversary within program member :=
    simulation.transport adversary budget within program member
  loss budget := simulation.queryCost.loss budget (simulation.queryCost.expansion executions)
  bound budget adversary within :=
    (simulation.bound_translate adversary budget executions within).trans
      (add_le_add_left (mixes _) _)

end Simulation

end ZkcSecurity.FiatShamir.Provider
