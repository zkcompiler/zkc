module

public import ZkcSecurity.ArkLib.FiatShamir.Prefix.Cache

@[expose] public section

/-! The two-round full-transcript experiment and its concrete restoration
adversary. The reduction queries the first selected message once before choosing
its second salt. ArkLib completion subsequently repeats that first access in
the shared cache. That repetition is charged, although it draws no new coin. -/

namespace ZkcSecurity.ArkLib.FiatShamir.Prefix
open OracleComp OracleSpec Interaction.Oracle.Security

variable {Input W : Type} {round : StateRestoration.Round}

abbrev Path (round : StateRestoration.Round) :=
  (StateRestoration.protocol [round, round]).tree.ExecutionPath

/-- Public input, two selected messages, and an arbitrary terminal witness. -/
abbrev Output (Input W : Type) (round : StateRestoration.Round) :=
  Input × round.Message × round.Message × W

/-- Full-prefix verification derives both challenges in order. -/
def complete (z : Input) (first second : round.Message) :
    OracleComp (Spec Input round) (Path round) := do
  let challenge ← liftM ((Spec Input round).query (.inl (z, first)))
  let final ← liftM ((Spec Input round).query (.inr (z, first, challenge, second)))
  pure ⟨first, challenge, second, final, PUnit.unit⟩

/-- The adversary and verification share one full-prefix oracle. -/
def execution (adversary : OracleComp (Spec Input round) (Output Input W round)) :
    OracleComp (Spec Input round) (Input × Path round × W) := do
  let (z, first, second, witness) ← adversary
  let path ← complete z first second
  pure (z, path, witness)

/-- The second salt is selected only after reading the shared first-round answer. -/
def prepare (output : Output Input W round) :
    OracleComp (TargetSpec Input round)
      (Input × StateRestoration.Messages (Salt round) [round, round] × W) := do
  let (z, first, second, witness) := output
  let challenge ← liftM ((TargetSpec Input round).query
    (StateRestoration.Key.here z first none))
  pure (z, (first, none, second, some challenge, PUnit.unit), witness)

/-- A concrete reduction, with no assumed correspondence or salt-consistency field. -/
def adversaryMap (adversary : OracleComp (Spec Input round) (Output Input W round)) :
    OracleComp (TargetSpec Input round)
      (Input × StateRestoration.Messages (Salt round) [round, round] × W) :=
  simulateQ translate adversary >>= prepare

/-- Translation preserves all-branch total access bounds. -/
theorem translate_queryBound {Result : Type}
    (program : OracleComp (Spec Input round) Result) (Q : Nat)
    (bounded : IsTotalQueryBound program Q) :
    IsTotalQueryBound (simulateQ translate program) Q := by
  have h := bounded.simulateQ_of_step_le (impl := translate) (step := 1) (by
    intro key
    simp only [translate, map_eq_bind_pure_comp, isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun _ => trivial⟩)
  simpa using h

/-- The salt-selection step makes exactly one access, even on a cache hit. -/
theorem prepare_queryBound (output : Output Input W round) :
    IsTotalQueryBound (prepare output) 1 := by
  rcases output with ⟨z, first, second, witness⟩
  simp only [prepare, isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun _ => trivial⟩

/-- An adversary with `Q` full-prefix accesses becomes a `Q+1` restoration adversary. -/
theorem adversaryMap_queryBound
    (adversary : OracleComp (Spec Input round) (Output Input W round)) (Q : Nat)
    (bounded : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (adversaryMap adversary) (Q + 1) :=
  isTotalQueryBound_bind (translate_queryBound adversary Q bounded) prepare_queryBound

variable [DecidableEq Input] [DecidableEq round.Challenge]

/-- A repeated immediate access uses the first answer and preserves the cache. -/
theorem repeat_query {Result : Type} (key : TargetKey Input round)
    (next : key.Challenge → key.Challenge →
      StateT (TargetSpec Input round).QueryCache ProbComp Result) :
    (do
      let first ← (TargetSpec Input round).randomOracle key
      let second ← (TargetSpec Input round).randomOracle key
      next first second) =
    (do
      let first ← (TargetSpec Input round).randomOracle key
      next first first) := by
  funext cache
  change (do
    let p ← ((TargetSpec Input round).randomOracle key).run cache
    let q ← ((TargetSpec Input round).randomOracle key).run p.2
    (next p.1 q.1).run q.2) = (do
    let p ← ((TargetSpec Input round).randomOracle key).run cache
    (next p.1 p.1).run p.2)
  cases cached : cache key <;>
    simp [cached]

/-- Completion agrees after selecting the salt from the cached first answer. -/
theorem prepare_complete (output : Output Input W round) :
    simulateQ (TargetSpec Input round).randomOracle
      (do
        let (z, messages, witness) ← prepare output
        let path ← StateRestoration.complete [round, round] z messages
        pure (z, path, witness)) =
    simulateQ (TargetSpec Input round).randomOracle
      (simulateQ translate (do
        let (z, first, second, witness) := output
        let path ← complete z first second
        pure (z, path, witness))) := by
  rcases output with ⟨z, first, second, witness⟩
  simp only [prepare, complete, StateRestoration.complete,
    StateRestoration.prependQuery, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, translate_first, translate_second, bind_assoc, pure_bind, Path,
    StateRestoration.protocol, Interaction.Oracle.Protocol.oracleWith,
    Interaction.Oracle.Protocol.public, Interaction.Oracle.Protocol.done]
  exact repeat_query (Input := Input) (round := round) _ _

/-- The real mapped adversary plus pinned ArkLib completion has exactly the same
output and target cache as translated full-prefix execution. -/
theorem restoration_simulation
    (adversary : OracleComp (Spec Input round) (Output Input W round)) :
    simulateQ (TargetSpec Input round).randomOracle
        (StateRestoration.restoredExecution [round, round] (adversaryMap adversary)) =
      simulateQ (TargetSpec Input round).randomOracle
        (simulateQ translate (execution adversary)) := by
  simp only [StateRestoration.restoredExecution, adversaryMap, execution,
    bind_assoc, simulateQ_bind]
  congr 1
  funext output
  simpa only [simulateQ_bind] using prepare_complete output

/-- Equality of the complete cached experiments, for arbitrary initial target cache.
This quantifies over all adaptive full-prefix adversaries, including prequeries,
inconsistent challenge prefixes, and repeated or out-of-order queries. -/
theorem experiment_eq
    (adversary : OracleComp (Spec Input round) (Output Input W round))
    (cache : (TargetSpec Input round).QueryCache) :
    (simulateQ (TargetSpec Input round).randomOracle
        (StateRestoration.restoredExecution [round, round] (adversaryMap adversary))).run' cache =
      (simulateQ (Spec Input round).randomOracle (execution adversary)).run' (view cache) := by
  rw [restoration_simulation]
  exact adaptive_output _ _

end ZkcSecurity.ArkLib.FiatShamir.Prefix
