import Zkc.Semantics.AdaptiveClient

set_option autoImplicit false

namespace Zkc.Semantics.Locality
-- Necessity of factoring the complete selected action through a local view.
theorem local_factor_necessary {H V A : Type} (view : H → V) (act : H → A)
    (f : V → A) (realizes : ∀ h, f (view h) = act h)
    (h k : H) (same : view h = view k) : act h = act k := by
  rw [← realizes h, ← realizes k, same]

def projectedResult {G V O : Type} (view : G → V) (x : O × G) : O × V :=
  (x.1, view x.2)

/-- The selected result includes callback identity, arguments and memory when
those are part of the claimed observation. -/
def FiberConstant {G V X : Type} (view : G → V) (f : G → X) : Prop :=
  ∀ g h, view g = view h → f g = f h

/-- Constructive representatives are supplied explicitly, never chosen from
    an existence proof. The section law is needed only on the image of view;
    stability below still quantifies over all G, not a reachability invariant. -/
theorem descent {G V X : Type} (view : G → V) (represent : V → G)
    (sectionLaw : ∀ g, view (represent (view g)) = view g)
    (f : G → X) (stable : FiberConstant view f) (g : G) :
    f (represent (view g)) = f g := stable _ _ (sectionLaw g)

theorem descent_iff {G V X : Type} (view : G → V) (represent : V → G)
    (sectionLaw : ∀ g, view (represent (view g)) = view g) (f : G → X) :
    FiberConstant view f ↔ ∀ g, f (represent (view g)) = f g := by
  constructor
  · exact fun h g => descent view represent sectionLaw f h g
  · intro h g k eqv
    rw [← h g, ← h k, eqv]

/-- Equality of enabled outputs is distinct from the transition law. -/
def OutputExact {G V A : Type} (view : G → V) (enabled : G → A → Bool)
    (localEnabled : V → A → Bool) : Prop :=
  ∀ g a, localEnabled (view g) a = enabled g a

theorem output_necessary {G V A : Type} (view : G → V)
    (enabled : G → A → Bool) (localEnabled : V → A → Bool)
    (h : OutputExact view enabled localEnabled) (g k : G)
    (same : view g = view k) (a : A) : enabled g a = enabled k a := by
  rw [← h g a, ← h k a, same]

def localStep {G V A O : Type} (view : G → V) (represent : V → G)
    (step : A → G → O × G) (a : A) (v : V) : O × V :=
  projectedResult view (step a (represent v))

theorem step_descent {G V A O : Type} (view : G → V) (represent : V → G)
    (sectionLaw : ∀ g, view (represent (view g)) = view g)
    (step : A → G → O × G)
    (stable : ∀ a, FiberConstant view (fun g => projectedResult view (step a g)))
    (a : A) (g : G) :
    localStep view represent step a (view g) = projectedResult view (step a g) :=
  descent view represent sectionLaw _ (stable a) g

/-- Reuses Zkc.Semantics.AdaptiveClient's adaptive-client transport with a newly constructed local step.
    Every realized client branch terminates; no common horizon or efficiency
    bound is obtained from the inductive client type. -/
theorem local_adaptive {G V A O : Type} (view : G → V) (represent : V → G)
    (sectionLaw : ∀ g, view (represent (view g)) = view g)
    (step : A → G → O × G)
    (stable : ∀ a, FiberConstant view (fun g => projectedResult view (step a g)))
    (client : Zkc.Semantics.AdaptiveClient.Client A O) (g : G) :
    (Zkc.Semantics.AdaptiveClient.execClient step client g).1 =
      (Zkc.Semantics.AdaptiveClient.execClient (localStep view represent step) client (view g)).1 ∧
    view (Zkc.Semantics.AdaptiveClient.execClient step client g).2 =
      (Zkc.Semantics.AdaptiveClient.execClient (localStep view represent step) client (view g)).2 := by
  apply Zkc.Semantics.AdaptiveClient.adaptive_transport step (localStep view represent step)
    (fun s v => view s = v)
  · intro a s v h
    subst v
    have he := step_descent view represent sectionLaw step stable a s
    exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
  · rfl


-- This general impossibility statement does not presuppose a syntactic checker.
-- It rules out every deterministic local adapter for two observationally equal
-- worlds demanding different actions.
theorem no_local_adapter {World Local Action : Type}
    (view : World → Local) (required : World → Action) (s t : World)
    (same : view s = view t) (different : required s ≠ required t) :
    ¬ ∃ f : Local → Action, ∀ w, f (view w) = required w := by
  rintro ⟨f, realizes⟩
  exact different (local_factor_necessary view required f realizes s t same)

end Zkc.Semantics.Locality
