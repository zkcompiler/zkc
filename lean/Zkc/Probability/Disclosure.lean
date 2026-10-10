import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Exact randomized release under the actual joint distribution.

Artifact and runtime channels may share hidden randomness. Equal marginal
distributions alone do not establish joint permission. A common coupling must
preserve the whole selected observation. These are normalized discrete laws,
not computational indistinguishability or a native release theorem.
-/

set_option autoImplicit false

namespace Zkc.Probability.Disclosure

variable {W X Y A B O : Type}

def Permitted (allowed : W → W → Prop) (release : W → PMF O) : Prop :=
  ∀ w v, allowed w v → release w = release v

/-- Equality is needed only on the actual sample support. -/
theorem map_supported (p : PMF X) (f g : X → O)
    (same : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  apply PMF.ext
  intro o
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · rw [same x hx]

/-- Both marginal laws and agreement on the SAME coupling are required. -/
theorem coupled_release (p : PMF X) (q : PMF Y) (joint : PMF (X × Y))
    (left : joint.map Prod.fst = p) (right : joint.map Prod.snd = q)
    (f : X → O) (g : Y → O)
    (agrees : ∀ xy ∈ joint.support, f xy.1 = g xy.2) : p.map f = q.map g := by
  rw [← left, ← right, PMF.map_comp, PMF.map_comp]
  exact map_supported joint _ _ agrees

/-- Instantiate `O` with the whole artifact/runtime pair. -/
theorem joint_release (p : PMF X) (q : PMF Y) (joint : PMF (X × Y))
    (left : joint.map Prod.fst = p) (right : joint.map Prod.snd = q)
    (artifact : X → A) (otherArtifact : Y → A)
    (runtime : X → B) (otherRuntime : Y → B)
    (artifacts : ∀ xy ∈ joint.support, artifact xy.1 = otherArtifact xy.2)
    (runtimes : ∀ xy ∈ joint.support, runtime xy.1 = otherRuntime xy.2) :
    p.map (fun x => (artifact x, runtime x)) =
      q.map (fun y => (otherArtifact y, otherRuntime y)) :=
  coupled_release p q joint left right _ _
    (fun xy h => Prod.ext (artifacts xy h) (runtimes xy h))

theorem project_release (allowed : W → W → Prop) (release : W → PMF O)
    (permitted : Permitted allowed release) (project : O → A) :
    Permitted allowed (fun w => (release w).map project) := by
  intro w v h
  exact congrArg (PMF.map project) (permitted w v h)

/-- An event must be determined by the preserved observation. -/
theorem event_transport (p q : PMF O) (same : p = q) (event : O → Bool) :
    (p.map event) true = (q.map event) true := by rw [same]

end Zkc.Probability.Disclosure
