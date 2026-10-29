module

public import ZkcSecurity.Source.PublicProperties
public import ZkcSecurity.Families.Sumcheck.Round

@[expose] public section

/-! Two properties use one actual challenge. Their union is charged by the
sum, with no independence premise. Installation retains an arbitrary captured
residual and both predicates through the actual routed public interpreter.
-/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.SourcePublicProperties
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Source ZkcSecurity.FiatShamir OracleComp OracleSpec

variable {carriers : Carriers}
  [samples : ∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
  (field site : String) (handle : Nat) (captured : Nat)
  (left right : carriers.Field field → Prop) (leftError rightError : ENNReal)
  (leftBound : ∀ (origin : Origin) (request : origin.request = some (.draw field)),
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[
      left (Original.fieldReply origin field request raw)] ≤ leftError)
  (rightBound : ∀ (origin : Origin) (request : origin.request = some (.draw field)),
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[
      right (Original.fieldReply origin field request raw)] ≤ rightError)

def source : PIR.Process (Occurrence.signature carriers) (carriers.Field field × Nat) :=
  .call (.action (.query site field (.cons handle .nil))) fun reply => .done (reply, captured)

def residual (result : carriers.Field field × Nat) : Prop :=
  result.2 = captured ∧ ¬ left result.1 ∧ ¬ right result.1

def shared_source : Derivation PublicProperties.interface
    (PublicProperties.escape (leftError + rightError))
    (fun _ => residual field captured left right) [] (source field site handle captured) := by
  refine .query rfl (fun reply => left reply ∨ right reply) ?_ ?_
  · intro origin request
    exact ZkcSecurity.Families.Sumcheck.shared_challenge_union_le
      ($ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers)))
      (fun raw => left (Original.fieldReply origin field request raw))
      (fun raw => right (Original.fieldReply origin field request raw))
      leftError rightError (leftBound origin request) (rightBound origin request)
  · intro raw reply decoded outside
    cases decoded
    exact .done ⟨rfl, fun bad => outside (.inl bad), fun bad => outside (.inr bad)⟩

def shared_installed (routing : Original.Routing) (mode : routing.mode = .validator)
    (state : Original.State carriers) :
    Derivation NominalDomain.interface
      (ZkcSecurity.Obligations.boundedEscape (fun _ _ => leftError + rightError))
      (fun _ result => residual field captured left right result.1) state.history
      (DomainSourceReading.presentation routing (source field site handle captured) state) :=
  PublicProperties.install routing mode (leftError + rightError)
    (residual field captured left right) _ []
    (shared_source field site handle captured left right leftError rightError leftBound rightBound) state

omit samples in
/-- A third residual is neither the selected Yes fact nor the selected No
fact. The installation above requires no complementary classification. -/
theorem non_complement_residual (reply : carriers.Field field) :
    ¬ (((reply, 2) : carriers.Field field × Nat).2 = 0) ∧
    ¬ (((reply, 2) : carriers.Field field × Nat).2 = 1) := by
  change ¬ (2 : Nat) = 0 ∧ ¬ (2 : Nat) = 1
  decide

#print axioms shared_source
#print axioms shared_installed
end TestsSecurity.SourcePublicProperties
