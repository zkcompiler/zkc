module

public import ZkcSecurity.ArkLib.FiatShamir.Prefix.Keys

@[expose] public section

/-! Adaptive cache transport through the fixed two-round key injection.
Queries need not describe reachable transcript prefixes. The target cache is
retained, including entries outside the image, throughout the simulation. -/

namespace ZkcSecurity.ArkLib.FiatShamir.Prefix
open OracleComp OracleSpec Interaction.Oracle.Security

variable {Input : Type} {round : StateRestoration.Round}
variable [DecidableEq Input] [DecidableEq round.Challenge]

/-- The actual restoration RO, viewed through the full-prefix query interface. -/
def handler : QueryImpl (Spec Input round)
    (StateT (TargetSpec Input round).QueryCache ProbComp) :=
  fun key => responseEquiv key <$> (TargetSpec Input round).randomOracle (encode key)

/-- A translated access agrees with the independent full-prefix lazy RO step. -/
theorem local_projection (key : Key Input round)
    (cache : (TargetSpec Input round).QueryCache) :
    Prod.map id view <$> (handler key).run cache =
      ((Spec Input round).randomOracle key).run (view cache) := by
  cases key with
  | inl data =>
    rcases data with ⟨z, first⟩
    cases cached : cache (encode (.inl (z, first))) <;>
      simp only [handler, StateT.run_map, randomOracle.run_eq, view_apply, cached,
        Option.map_none, Option.map_some, map_bind, map_pure, Prod.map_apply, id_eq]
    · apply bind_congr
      intro answer
      apply congrArg pure
      exact Prod.ext rfl (view_cacheQuery cache _ answer)
  | inr data =>
    rcases data with ⟨z, first, challenge, second⟩
    cases cached : cache (encode (.inr (z, first, challenge, second))) <;>
      simp only [handler, StateT.run_map, randomOracle.run_eq, view_apply, cached,
        Option.map_none, Option.map_some, map_bind, map_pure, Prod.map_apply, id_eq]
    · apply bind_congr
      intro answer
      apply congrArg pure
      exact Prod.ext rfl (view_cacheQuery cache _ answer)

/-- The projection holds for every adaptive client, with arbitrary initial target cache. -/
theorem adaptive_projection {Result : Type} (program : OracleComp (Spec Input round) Result)
    (cache : (TargetSpec Input round).QueryCache) :
    Prod.map id view <$> (simulateQ handler program).run cache =
      (simulateQ (Spec Input round).randomOracle program).run (view cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ view local_projection program cache

/-- Translating the client, then using the actual restoration RO, gives `handler`. -/
theorem translate_simulate {Result : Type} (program : OracleComp (Spec Input round) Result) :
    simulateQ (TargetSpec Input round).randomOracle (simulateQ translate program) =
      simulateQ handler program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind key next ih =>
    simp [simulateQ_bind, translate, handler, ih]

/-- Output equality retains the same cache across all parts of an adaptive client. -/
theorem adaptive_output {Result : Type} (program : OracleComp (Spec Input round) Result)
    (cache : (TargetSpec Input round).QueryCache) :
    (simulateQ (TargetSpec Input round).randomOracle (simulateQ translate program)).run' cache =
      (simulateQ (Spec Input round).randomOracle program).run' (view cache) := by
  rw [translate_simulate]
  have h := congrArg (Prod.fst <$> ·) (adaptive_projection program cache)
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map, id_eq] using h

end ZkcSecurity.ArkLib.FiatShamir.Prefix
