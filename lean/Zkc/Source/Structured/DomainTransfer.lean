module

public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.RegionCongruence

@[expose] public section

/-! Transfer between domain models that differ only in the inverse.

A model built from a commutative ring has no inverse; a model built from a
field supplies one, and only the latter can satisfy the inverse law that a
`Field` fact of a catalogue row selects. For bodies that never invert a field
element the two models give the same denotation, so a theorem proved for every
lawful model applies at the ring model for such bodies, with the lawful
model's assumptions. The congruence behind it is `Region.denote_congr`: two
meanings with the same values that agree on every operation a region stores
give it the same denotation. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The model with its inverse replaced. -/
abbrev DomainModel.withInverse (model : DomainModel)
    (inverse : ∀ d, Option (model.Field d → model.Field d)) : DomainModel :=
  { model with inverse := inverse }

/-- Whether an operation evaluates a field inverse. The current vocabulary has
no inverse operation. -/
def Op.usesInverse : Op → Bool
  | _ => false

theorem Primitive.evaluateOn_inverse_congr (model : FieldModel)
    (inverse : ∀ d, Option (model.Field d → model.Field d)) :
    Primitive.evaluateOn { model with inverse := inverse } = Primitive.evaluateOn model := by
  funext primitive args
  cases primitive <;> (iterate 3 (try (rcases args with _ | ⟨_, args⟩))) <;> rfl

namespace Evaluation

/-- Every operation that does not invert ignores the model's inverse. -/
theorem operationOn_inverse_congr (model : DomainModel)
    (inverse : ∀ d, Option (model.Field d → model.Field d)) {interface : PIR.Signature}
    (observations : SiteObservations interface) (table : MeaningsOn model.toCarriers interface)
    (op : Op) (_free : op.usesInverse = false) :
    operationOn (model.withInverse inverse) observations table op =
      operationOn model observations table op := by
  funext args bodies
  cases op with
  | exec primitive =>
    rcases bodies with _ | _
    exact congrArg primitiveOutcome
      (congrFun (congrFun (Primitive.evaluateOn_inverse_congr model.toFieldModel inverse) primitive) args)
  | invoke helper => rcases bodies with _ | _; rfl
  | fold spec => rcases bodies with _ | _; rfl
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

/-- Every region of the current vocabulary is inverse-free. -/
theorem inverse_free {Γ out : List Ty} (region : Region dialect Γ out) :
    ∀ op ∈ region.erase.operations, op.usesInverse = false :=
  fun _ _ => rfl

end Evaluation

end Zkc.Source.Structured
