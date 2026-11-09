module

public import Zkc.IR.Source.Structured.DomainEvaluation
public import Zkc.Program.Source.RegionCongruence

@[expose] public section

/-! Transfer between domain models that differ only in the inverse.

The ring-only model has no inverse. A model that enables inversion must supply
an inverse and discharge its separate completeness premise; the conditional
`DomainLaws.inverse` alone does not imply availability. For bodies whose stored
operations never invert, replacing only that optional capability preserves
denotation. The congruence behind this per-operation result is
`Region.denote_congr`: two meanings with the same values that agree on every
operation a region stores give it the same denotation. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The model with its inverse replaced. -/
abbrev DomainModel.withInverse (model : DomainModel)
    (inverse : ∀ d, Option (model.Field d → model.Field d)) : DomainModel :=
  { model with inverse := inverse }

/-- Optional inverse dependencies are explicit for each fixed primitive. -/
def Primitive.usesInverse : Primitive → Bool
  | .numerical op _ _ => op.usesInverse
  | _ => false

/-- Structural transfer requires each stored operation to avoid inversion. -/
def Op.usesInverse : Op → Bool
  | .exec primitive => primitive.usesInverse
  | _ => false

theorem Primitive.evaluateOn_inverse_congr (model : FieldModel)
    (inverse : ∀ d, Option (model.Field d → model.Field d)) (primitive : Primitive)
    (free : primitive.usesInverse = false) (args : Values model.Value primitive.arguments) :
    Primitive.evaluateOn { model with inverse := inverse } primitive args =
      Primitive.evaluateOn model primitive args := by
  cases primitive with
  | numerical op d base =>
    cases op <;> simp only [usesInverse, Numerical.usesInverse] at free <;>
      try contradiction
    all_goals rfl
  | binaryConstant d bits => cases args; rfl
  | _ => (iterate 3 (try (rcases args with _ | ⟨_, args⟩))); rfl

namespace Evaluation

/-- Every operation that does not invert ignores the model's inverse. -/
theorem operationOn_inverse_congr (model : DomainModel)
    (inverse : ∀ d, Option (model.Field d → model.Field d)) {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : MeaningsOn model.toCarriers interface)
    (op : Op) (free : op.usesInverse = false) :
    operationOn (model.withInverse inverse) observations table op =
      operationOn model observations table op := by
  funext args bodies
  cases op with
  | exec primitive =>
    rcases bodies with _ | _
    exact congrArg primitiveOutcome
      (Primitive.evaluateOn_inverse_congr model.toFieldModel inverse primitive free args)
  | invoke helper => rcases bodies with _ | _; rfl
  | fold spec | collect spec => rcases bodies with _ | _; rfl
  | map spec => rcases bodies with _ | _; rfl
  | branch captures outputs =>
    rcases bodies with _ | ⟨yes, _ | ⟨no, _ | _⟩⟩
    rcases args with _ | ⟨condition, captured⟩
    rfl
  | loop state captures =>
    rcases bodies with _ | ⟨body, _ | _⟩
    rcases args with _ | ⟨lower, _ | ⟨upper, rest⟩⟩
    rfl
  | loopCondition state captures =>
    rcases bodies with _ | ⟨body, _ | _⟩
    rcases args with _ | ⟨lower, _ | ⟨upper, rest⟩⟩
    rfl
  | boundedAt domain =>
    rcases bodies with _ | _
    rcases args with _ | ⟨container, _ | ⟨index, _ | _⟩⟩
    rw [operationOn_boundedAt, operationOn_boundedAt]
    cases (show List (model.Field domain) from container)[index]? <;> rfl
  | _ =>
    (try rcases bodies with _ | _)
    (iterate 4 (try (rcases args with _ | ⟨_, args⟩)))
    rfl

/-- A region that never inverts has the same denotation under every inverse. -/
theorem denote_inverse_free (model : DomainModel)
    (inverse : ∀ d, Option (model.Field d → model.Field d)) {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : MeaningsOn model.toCarriers interface)
    {Γ out : List Ty} (region : Region dialect Γ out)
    (free : ∀ op ∈ region.erase.operations, op.usesInverse = false) :
    region.denote (meaningOn (model.withInverse inverse) observations table) =
      region.denote (meaningOn model observations table) :=
  Region.denote_congr _ _ region fun op member =>
    operationOn_inverse_congr model inverse observations table op (free op member)


end Evaluation

end Zkc.Source.Structured
