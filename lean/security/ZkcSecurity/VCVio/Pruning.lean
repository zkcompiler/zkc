module

public import Zkc.Executable.Pruning
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Constructions.SampleableType.Measure
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

`prEvent_le_of_prunes_image` is the one transport lemma for verdicts: a
computation that prunes an outcome image of another, by results its event
excludes, hits its event at most as often as the other hits any event that every
image hit comes from. It holds under every stateful oracle implementation, the
lazily sampled random oracle and handlers alike. Acceptance inclusion through an
exact image is the case without pruning (`prEvent_le_of_image`). Extraction and
provider composition need stronger relations than acceptance inclusion and do
not go through it.
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

/-- Outcome image and pruning: when `compiled` prunes the image of `ideal` under
`image`, by results its event excludes, and an image hitting the compiled event
comes only from an ideal result hitting the ideal event, the compiled computation
hits its event at most as often as the ideal one, simulated by any stateful oracle
implementation from any state. -/
theorem prEvent_le_of_prunes_image {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] {σ : Type}
    (implementation : QueryImpl spec (StateT σ m)) {α β : Type} (image : α → β)
    {rejects event : β → Prop} {idealEvent : α → Prop}
    (disjoint : ∀ result, rejects result → ¬ event result)
    (preserves : ∀ result, event (image result) → idealEvent result)
    {compiled : OracleComp spec β} {ideal : OracleComp spec α}
    (pruned : Prunes rejects compiled (image <$> ideal)) (state : σ) :
    Pr{let result ← (simulateQ implementation compiled).run' state}[event result] ≤
      Pr{let result ← (simulateQ implementation ideal).run' state}[idealEvent result] := by
  have mapped : (simulateQ implementation (image <$> ideal)).run' state =
      image <$> (simulateQ implementation ideal).run' state := by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  refine (Prunes.prEvent_le implementation disjoint pruned state).trans ?_
  rw [mapped, prEvent_map]
  exact prEvent_mono _ _ _ fun result hit => preserves result hit

/-- Acceptance inclusion through an exact outcome image. -/
theorem prEvent_le_of_image {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] {σ : Type}
    (implementation : QueryImpl spec (StateT σ m)) {α β : Type} (image : α → β)
    {event : β → Prop} {idealEvent : α → Prop}
    (preserves : ∀ result, event (image result) → idealEvent result)
    {compiled : OracleComp spec β} {ideal : OracleComp spec α} (exact : compiled = image <$> ideal)
    (state : σ) :
    Pr{let result ← (simulateQ implementation compiled).run' state}[event result] ≤
      Pr{let result ← (simulateQ implementation ideal).run' state}[idealEvent result] :=
  prEvent_le_of_prunes_image implementation image (rejects := fun _ => False) (fun _ => False.elim)
    preserves (exact ▸ Prunes.refl _) state

end ZkcSecurity.VCVio.Pruning
