module

public import Zkc.Construction.ConnectionInputs

@[expose] public section

/-! Source-owned visibility at connection boundaries. Masking preserves the
entire typed tuple and every preceding effect. Only the source's scopes decide
which components are hidden; physical locations cannot select that policy. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

/-- Symbolic counterpart of the existing participant mask. -/
def mask (role : Nat) {scope : Scope} : {types : List Ty} →
    List (List Nat) → Values (Comp [] scope) types → Values (Comp [] scope) types
  | [], _, .nil => .nil
  | _ :: _, scopes, .cons value rest =>
    .cons (if (scopes.headD []).contains role then value else .absent)
      (mask role scopes.tail rest)

theorem mask_eval (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (role : Nat) (scopes : List (List Nat)) {types : List Ty} (values : Values (Comp [] scope) types) :
    Comps.eval (LawResults.empty model) (mask role scopes values) binders =
      maskValues role scopes (Comps.eval (LawResults.empty model) values binders) := by
  induction values generalizing scopes with
  | nil => rfl
  | cons value rest ih =>
    simp only [mask, Comps.eval, maskValues, ih, Participant.restrict]
    split <;> rfl

/-- Checked readback of all source outputs after their actual visibility mask.
A hidden raw result need not have a physical slot. A visible result still does. -/
theorem Readback.masked {model : DomainModel} {scope : Scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    {role : Nat} {scopes : List (List Nat)} {types : List Ty}
    {values : Values (Comp [] scope) types} {locations : List Original.Location}
    (certificate : Readback layout (mask role scopes values) locations)
    (related : Holds model binders history layout environment) :
    Original.ValuesHolds environment locations
      (maskValues role scopes (Comps.eval (LawResults.empty model) values binders)) := by
  simpa only [mask_eval] using certificate.sound related

/-- The source input scope agrees with every fixed ABI location. Visible
capabilities are allowed, but a hidden input must be absent. Both lists are
consumed, so a missing scope cannot silently hide an extra input. -/
def inputScopes (role : Nat) : List (List Nat) → List Original.Location → Bool
  | [], [] => true
  | scope :: scopes, location :: locations =>
    ((scope.contains role) || match location with | .absent => true | _ => false) &&
      inputScopes role scopes locations
  | _, _ => false

theorem inputScopes_mask {carriers : Carriers} {types : List Ty} {role : Nat}
    {scopes : List (List Nat)} {locations : List Original.Location}
    {frame : Domain.Environment carriers} (values : Values (Component carriers.Value) types)
    (checked : inputScopes role scopes locations = true)
    (related : Original.ValuesHolds frame locations values) :
    maskValues role scopes values = values := by
  induction values generalizing scopes locations with
  | nil => rfl
  | cons value rest ih =>
    cases locations with
    | nil => exact False.elim related
    | cons location locations =>
      cases scopes with
      | nil => simp [inputScopes] at checked
      | cons scope scopes =>
        have tail : inputScopes role scopes locations = true := (Bool.and_eq_true_iff.mp checked).2
        simp only [maskValues, List.headD_cons, List.tail_cons, ih tail related.2]
        congr 1
        by_cases visible : role ∈ scope
        · simp [Participant.restrict, visible]
        · cases location with
          | absent =>
            have hidden : value = none := related.1
            simp [Participant.restrict, visible, hidden]
          | data reference => simp [inputScopes, visible] at checked
          | capability handle => simp [inputScopes, visible] at checked

end Zkc.Construction.ConnectionFrame
