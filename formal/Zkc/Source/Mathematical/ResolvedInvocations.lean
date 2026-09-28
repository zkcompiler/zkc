import Zkc.Source.Mathematical.InstanceProvenance
import Zkc.Source.Mathematical.ProtocolInvocations

/-! Invocation provenance across carrier resolution and intrinsic lowering.
Every collected invocation retains the resolver's actual call-selection proof.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.ProtocolResolution

variable {vocabulary : Protocol.Vocabulary} {resolver : Resolver vocabulary}

structure Invocation (resolver : Resolver vocabulary) where
  site : Nat
  source : CallUse
  callee : Nat
  valid : resolver.CallValid source callee

def Invocation.authored (call : Invocation resolver) : ClosedInstances.CallSite := ⟨call.site, call.source⟩
def Invocation.lower (call : Invocation resolver) : Protocol.Invocation :=
  ⟨call.site, call.callee, call.source.capabilities.map (·.index)⟩

mutual
  def Step.invocations : Step resolver → List (Invocation resolver)
    | .invoke site source callee valid _ => [⟨site, source, callee, valid⟩]
    | .repeat _ _ _ _ _ _ _ body => body.invocations
    | _ => []
  def Body.invocations : Body resolver → List (Invocation resolver)
    | .mk steps _ => steps.flatMap Step.invocations
end

mutual
  theorem Step.invocations_cover (step : Step resolver) :
      ClosedInstances.StepCalls step.erase (step.invocations.map Invocation.authored) := by
    cases step <;> simp only [Step.erase, Step.invocations, List.map_nil, List.map_cons, Invocation.authored]
    case pure => exact .pure _
    case «local» => exact .local ..
    case query => exact .query ..
    case «guard» => exact .guard ..
    case message => exact .message ..
    case invoke => exact .invoke ..
    case «repeat» site source count valid carried initial captures body =>
        exact .repeat _ _ _ _ _ body.invocations_cover
  theorem steps_invocations_cover (steps : List (Step resolver)) :
      ClosedInstances.StepsCalls (steps.map Step.erase) ((steps.flatMap Step.invocations).map Invocation.authored) := by
    cases steps with
    | nil => exact .nil
    | cons first rest =>
        simpa only [List.map_cons, List.flatMap_cons, List.map_append] using
          ClosedInstances.StepsCalls.cons first.invocations_cover (steps_invocations_cover rest)
  theorem Body.invocations_cover (body : Body resolver) :
      ClosedInstances.BodyCalls body.erase (body.invocations.map Invocation.authored) := by
    cases body with
    | mk steps terminal =>
        simpa only [Body.erase, Body.invocations] using ClosedInstances.BodyCalls.mk _ (steps_invocations_cover steps)
end

mutual
  theorem Step.lower_invocations (step : Step resolver) (next : Protocol.Raw Nat vocabulary) :
      (step.lower next).invocations = step.invocations.map Invocation.lower ++ next.invocations := by
    cases step <;> simp [Step.lower, Step.invocations, Protocol.Raw.invocations, Invocation.lower, Body.lower_invocations]
  theorem steps_lower_invocations (steps : List (Step resolver)) (next : Protocol.Raw Nat vocabulary) :
      (steps.foldr (fun step tail => step.lower tail) next).invocations =
        (steps.flatMap Step.invocations).map Invocation.lower ++ next.invocations := by
    cases steps with
    | nil => rfl
    | cons first rest =>
        simp [Step.lower_invocations, steps_lower_invocations rest, List.append_assoc]
  theorem Body.lower_invocations (body : Body resolver) :
      body.lower.invocations = body.invocations.map Invocation.lower := by
    cases body with
    | mk steps terminal =>
        rw [Body.lower, steps_lower_invocations]
        cases terminal <;> simp [Terminal.lower, Protocol.Raw.invocations, Body.invocations]
end

theorem Formed.invocations {parties capabilities scope Γ results raw}
    (formed : Formed resolver parties capabilities scope Γ results raw) :
    formed.checked.program.invocations = formed.resolved.invocations.map Invocation.lower := by
  rw [← formed.checked.program.erase_invocations, formed.checked.erasure, formed.resolved.lower_invocations]

end Zkc.Source.Mathematical.ProtocolResolution
