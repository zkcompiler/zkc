import Zkc.Semantics.Execution

set_option autoImplicit false

namespace PIR.Disclosure

variable {W A O V : Type}

/-- A disclosure policy is an actual equivalence/relation on allowed worlds.
    It need not classify every pair of worlds as indistinguishable. -/
def Permitted (allowed : W → W → Prop) (release : W → A) : Prop :=
  ∀ w v, allowed w v → release w = release v

/-- Artifacts and runtime observations are independently visible channels. -/
def publish (artifact : W → A) (runtime : W → O) (w : W) : A × O :=
  (artifact w, runtime w)

theorem joint_release (allowed : W → W → Prop) (artifact : W → A) (runtime : W → O)
    (ha : Permitted allowed artifact) (hr : Permitted allowed runtime) :
    Permitted allowed (publish artifact runtime) := by
  intro w v h
  exact Prod.ext (ha w v h) (hr w v h)

theorem project_release (allowed : W → W → Prop) (release : W → A) (project : A → V)
    (h : Permitted allowed release) : Permitted allowed (project ∘ release) := by
  intro w v same
  exact congrArg project (h w v same)

/-- Deliberate disclosure weakens the confidentiality comparison only by the
    explicitly named released value. -/
theorem deliberate_release (allowed : W → W → Prop) (approved : W → V) :
    Permitted (fun w v => allowed w v ∧ approved w = approved v) approved := by
  intro w v h
  exact h.2

theorem joint_requires_artifact (allowed : W → W → Prop)
    (artifact : W → A) (runtime : W → O)
    (h : Permitted allowed (publish artifact runtime)) : Permitted allowed artifact := by
  intro w v same
  exact congrArg Prod.fst (h w v same)

end PIR.Disclosure
