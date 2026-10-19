module

public import Zkc.Source.Structured.ProtocolContext
public import Zkc.Source.Participant

@[expose] public section

namespace Zkc.Source.Structured

/-- Scopes hide supplied inputs before work and returned components after work.
They do not discard preceding effects or stops. -/
def maskValues {Value : Ty → Type} (self : Nat) :
    {types : List Ty} → List (List Nat) → Values (Component Value) types →
      Values (Component Value) types
  | [], _, .nil => .nil
  | _ :: _, scopes, .cons value rest =>
    .cons (Participant.restrict ((scopes.headD []).contains self) value)
      (maskValues self scopes.tail rest)

/-- Hiding components never creates a value and preserves the complete ABI. -/
theorem maskValues_absent {Value : Ty → Type} (self : Nat)
    (types : List Ty) (scopes : List (List Nat)) :
    maskValues self scopes (Values.absent Value types) = Values.absent Value types := by
  induction types generalizing scopes with
  | nil => rfl
  | cons ty types ih =>
    simp only [Values.absent, maskValues, ih]
    congr 1
    simp [Participant.restrict]

theorem maskValues_idempotent {Value : Ty → Type} {types : List Ty}
    (self : Nat) (scopes : List (List Nat)) (values : Values (Component Value) types) :
    maskValues self scopes (maskValues self scopes values) = maskValues self scopes values := by
  induction values generalizing scopes with
  | nil => rfl
  | cons value rest ih =>
    simp only [maskValues, ih]
    congr 1
    unfold Participant.restrict
    split <;> rfl

theorem maskValues_commute {Value : Ty → Type} {types : List Ty}
    (self : Nat) (left right : List (List Nat)) (values : Values (Component Value) types) :
    maskValues self left (maskValues self right values) =
      maskValues self right (maskValues self left values) := by
  induction values generalizing left right with
  | nil => rfl
  | cons value rest ih =>
    simp only [maskValues, ih]
    congr 1
    unfold Participant.restrict
    split <;> split <;> rfl

theorem maskValues_enter {Value : Ty → Type} {types : List Ty}
    (self : Nat) (context : ProtocolContext) (site : String) (roles : List Nat)
    (scopes : List (List Nat)) (values : Values (Component Value) types) :
    maskValues self ((context.enter site roles).mapScopes scopes) values =
      maskValues self (context.mapScopes (scopes.map (List.map (roleSubstitution roles)))) values := by
  rw [ProtocolContext.mapScopes_enter]

end Zkc.Source.Structured
