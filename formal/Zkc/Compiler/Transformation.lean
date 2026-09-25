import Zkc.Compiler.Refinement
import Zkc.Compiler.PlanEncoding

/-! Check actual candidate data using a proved, model-specific transformation.

Each rule selects certificate data and proves its own soundness. A serialized
consumer must separately select a finite certificate codec and an admitted rule;
this interface supplies neither. The candidate must match the proved rule's
output under the same interpretation and relation.
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

variable {sourceLanguage targetLanguage : Language}
  {sourceModel : ExecutionModel sourceLanguage} {targetModel : ExecutionModel targetLanguage}
  {Γ : List sourceLanguage.Ty} {Δ : List targetLanguage.Ty}
  {result : sourceLanguage.Ty} {output : targetLanguage.Ty}

/-- Soundness belongs to the rule, rather than an unchecked candidate assertion.
Concrete rules choose their certificate representation. -/
structure TransformationRule (relation : Refinement sourceModel targetModel Γ Δ result output) where
  Certificate : Type
  apply : Program sourceLanguage Γ result → Certificate → Option (Plan targetLanguage Δ output)
  sound : ∀ program certificate plan, apply program certificate = some plan →
    relation.Holds program plan

variable [DecidableEq targetLanguage.Ty]

structure CheckedTransformation
    (relation : Refinement sourceModel targetModel Γ Δ result output)
    (source : Program sourceLanguage Γ result)
    (candidate : RawProgram targetLanguage.Ty targetLanguage.Op) where
  plan : Plan targetLanguage Δ output
  decoded : decodePlan Δ output candidate = .ok plan
  correct : relation.Holds source plan

def checkTransformation [DecidableEq targetLanguage.Op]
    {relation : Refinement sourceModel targetModel Γ Δ result output}
    (rule : TransformationRule relation) (source : Program sourceLanguage Γ result)
    (certificate : rule.Certificate) (candidate : RawProgram targetLanguage.Ty targetLanguage.Op) :
    Option (CheckedTransformation relation source candidate) :=
  match accepted : rule.apply source certificate with
  | none => none
  | some plan =>
    if same : plan.erase = candidate then
      some {
        plan := plan
        decoded := same ▸ Plan.decode_erase plan
        correct := rule.sound source certificate plan accepted
      }
    else none

theorem CheckedTransformation.decoded_unique
    {relation : Refinement sourceModel targetModel Γ Δ result output}
    {source : Program sourceLanguage Γ result}
    {candidate : RawProgram targetLanguage.Ty targetLanguage.Op}
    (checked : CheckedTransformation relation source candidate)
    (other : Plan targetLanguage Δ output) (decoded : decodePlan Δ output candidate = .ok other) :
    checked.plan = other := Except.ok.inj (checked.decoded.symm.trans decoded)

end Zkc.Compiler
