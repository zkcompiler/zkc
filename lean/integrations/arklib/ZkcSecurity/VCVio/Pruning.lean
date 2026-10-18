module

public import Zkc.Executable.Pruning
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import ToMathlib.Control.StateT

@[expose] public section

/-! Pruned oracle computations accept less often.

`Zkc.Executable.Prunes rejects first second` says that `first` is `second` with
some continuations replaced by results that `rejects` holds of, the two making
the same oracle calls in the same order otherwise. Simulated by any stateful
oracle implementation from any initial state, `first` then satisfies an event
disjoint from `rejects` with at most the probability of `second`
(`Prunes.prEvent_le`). Host validation of proof bytes prunes the ideal
acceptance of the decoded proof by rejections (`Zkc.Executable.validate_prunes`),
so this bounds executable acceptance by ideal acceptance in every random-oracle
experiment, at every budget.
-/

set_option autoImplicit false

namespace ZkcSecurity.VCVio.Pruning
open OracleComp OracleSpec
open Zkc.Executable

/-- Pointwise dominated continuations bound the event after a common draw. -/
theorem prEvent_bind_mono {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type} (start : m α) (first second : α → m β) (event : β → Prop)
    (dominated : ∀ value, Pr{let result ← first value}[event result] ≤
      Pr{let result ← second value}[event result]) :
    Pr{let result ← start >>= first}[event result] ≤
      Pr{let result ← start >>= second}[event result] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  exact MeasureTheory.lintegral_mono dominated

/-- A pruned computation, simulated by a stateful oracle implementation from
any state, satisfies an event disjoint from its rejections at most as often as
the computation it prunes. -/
theorem Prunes.prEvent_le {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {σ : Type}
    (implementation : QueryImpl spec (StateT σ m)) {α : Type}
    {rejects event : α → Prop} (disjoint : ∀ result, rejects result → ¬ event result)
    {first second : OracleComp spec α} (pruned : Prunes rejects first second) (state : σ) :
    Pr{let result ← (simulateQ implementation first).run' state}[event result] ≤
      Pr{let result ← (simulateQ implementation second).run' state}[event result] := by
  induction pruned generalizing state with
  | refl computation => exact le_rfl
  | stop result rejected computation =>
      rw [simulateQ_pure, StateT.run'_pure',
        show (pure result : m α) = (fun _ => result) <$> (pure () : m Unit) by simp,
        prEvent_map, prEvent_eq_zero_of_forall_not _ _ fun _ => disjoint result rejected]
      exact zero_le
  | bind first pruned original step ih =>
      simp only [simulateQ_bind, StateT.run'_bind']
      exact prEvent_bind_mono _ _ _ _ fun pair => ih pair.1 pair.2

end ZkcSecurity.VCVio.Pruning
