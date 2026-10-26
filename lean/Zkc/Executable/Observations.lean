module

public import Zkc.Construction.Scalar

@[expose] public section

/-! Observable pruning of monadic computations. This definition is independent
of the syntax, evaluator and implementation correspondence of either stage. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction

/-- `Prunes rejects first second`: `first` is `second` with some continuations
replaced by a result that `rejects` holds of. -/
inductive Prunes {m : Type → Type} [Monad m] {α : Type} (rejects : α → Prop) : m α → m α → Prop
  | refl (computation : m α) : Prunes rejects computation computation
  | stop (result : α) (rejected : rejects result) (computation : m α) :
      Prunes rejects (pure result) computation
  | bind {β : Type} (first : m β) (pruned original : β → m α)
      (step : ∀ value, Prunes rejects (pruned value) (original value)) :
      Prunes rejects (first >>= pruned) (first >>= original)

theorem Prunes.map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {rejects : α → Prop}
    {rejects' : β → Prop} (f : α → β) (preserves : ∀ result, rejects result → rejects' (f result))
    {first second : m α} (pruned : Prunes rejects first second) :
    Prunes rejects' (f <$> first) (f <$> second) := by
  induction pruned with
  | refl computation => exact .refl _
  | stop result rejected computation =>
      rw [map_pure]
      exact .stop _ (preserves result rejected) _
  | bind first pruned original step ih =>
      rw [map_bind, map_bind]
      exact .bind _ _ _ ih

/-- A stopped result. -/
def Stopped {F G R : Type} (result : PIR.Outcome R × Proof F G) : Prop :=
  ∃ stop, result.1 = .stopped stop

theorem stopped_pure {F G R : Type} {m : Type → Type} [Monad m] (stop : PIR.Stop) (proof : Proof F G)
    (computation : m (PIR.Outcome R × Proof F G)) :
    Prunes Stopped (pure (.stopped stop, proof)) computation :=
  .stop _ ⟨stop, rfl⟩ _


end Zkc.Executable
