import Zkc.Source.Region

/-! Agreement of actual participant-local control values.

The synchronous reference may check separately bound guards or loop counts.
A successful check is evidence about those actual bindings. It neither sends
a choice to an uninformed participant nor proves that a network delivers it.
-/

set_option autoImplicit false

namespace Zkc.Source.ControlAgreement

inductive Error (Role : Type) where
  | noParticipants
  | unavailable (role : Role)
  | disagreement (role : Role)
  deriving DecidableEq, Repr

variable {Role A : Type}

/-- Missing bindings are distinct from a local false guard or zero loop count. -/
def Agrees (participants : List Role) (values : Role → Option A) (value : A) : Prop :=
  ∀ role ∈ participants, values role = some value

def checkRest [DecidableEq A] (values : Role → Option A) (value : A) :
    List Role → Except (Error Role) Unit
  | [] => .ok ()
  | role :: rest => match values role with
    | none => .error (.unavailable role)
    | some actual =>
        if actual = value then checkRest values value rest else .error (.disagreement role)

theorem checkRest_ok_iff [DecidableEq A] (values : Role → Option A)
    (value : A) (participants : List Role) :
    checkRest values value participants = .ok () ↔ Agrees participants values value := by
  induction participants with
  | nil => simp [checkRest, Agrees]
  | cons role rest ih =>
      cases found : values role with
      | none => simp [checkRest, found, Agrees]
      | some actual =>
          by_cases same : actual = value
          · subst actual
            simpa [checkRest, found, Agrees] using ih
          · simp [checkRest, found, same, Agrees]

/-- Return the common actual value, or identify the first missing/divergent binding. -/
def check [DecidableEq A] (participants : List Role) (values : Role → Option A) :
    Except (Error Role) A :=
  match participants with
  | [] => .error .noParticipants
  | role :: rest => match values role with
    | none => .error (.unavailable role)
    | some value => (checkRest values value rest).map fun _ => value

/-- Exact soundness and completeness for a nonempty declared participant list. -/
theorem check_ok_iff [DecidableEq A] (participants : List Role)
    (values : Role → Option A) (value : A) :
    check participants values = .ok value ↔
      participants ≠ [] ∧ Agrees participants values value := by
  cases participants with
  | nil => simp [check]
  | cons role rest =>
      cases found : values role with
      | none => simp [check, found, Agrees]
      | some actual =>
          cases checked : checkRest values actual rest with
          | error error =>
              have bad : ¬ Agrees rest values actual := by
                intro agreement
                have success := (checkRest_ok_iff values actual rest).mpr agreement
                rw [checked] at success
                cases success
              simp [check, found, checked, Except.map, Agrees] at *
              intro same
              subst actual
              exact bad
          | ok result =>
              have agreement := (checkRest_ok_iff values actual rest).mp checked
              simp only [check, found, checked, Except.map, Except.ok.injEq]
              constructor
              · intro same
                subst actual
                exact ⟨List.cons_ne_nil _ _, by
                  simpa [Agrees, found] using agreement⟩
              · intro ⟨_, all⟩
                exact Option.some.inj (found.symm.trans (all role (by simp)))

theorem check_role [DecidableEq A] (participants : List Role) (values : Role → Option A)
    (value : A) (accepted : check participants values = .ok value)
    (role : Role) (member : role ∈ participants) : values role = some value :=
  ((check_ok_iff participants values value).mp accepted).2 role member

/-- Agreement is unique for the same actual bindings and declared participants. -/
theorem check_unique [DecidableEq A] (participants : List Role) (values : Role → Option A)
    (left right : A) (hl : check participants values = .ok left)
    (hr : check participants values = .ok right) : left = right :=
  Except.ok.inj (hl.symm.trans hr)

/-- A checked common choice selects each role's actual typed local branch.
The binding premise concerns this condition/environment, not a same-named guard. -/
theorem branch_denote {language : Language} {interface : PIR.Signature}
    (meaning : Interpretation language interface) {Γ : List language.Ty} {ty : language.Ty}
    (condition : Var Γ language.condition) (yes no : Region language Γ ty)
    (env : Environment meaning.Value Γ) (participants : List Role)
    (values : Role → Option Bool) (choice : Bool)
    (accepted : check participants values = .ok choice)
    (role : Role) (member : role ∈ participants)
    (binding : values role = some (meaning.condition (env condition))) :
    (Region.branch condition yes no).denote meaning env =
      if choice then yes.denote meaning env else no.denote meaning env := by
  have same : meaning.condition (env condition) = choice :=
    Option.some.inj (binding.symm.trans
      (check_role participants values choice accepted role member))
  simp only [Region.denote, same]

end Zkc.Source.ControlAgreement
