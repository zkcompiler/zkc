module

public import Zkc.Source.Context

@[expose] public section

/-! Role-indexed mathematical values and total operations.

A common mathematical value can have different components at different roles.
`none` means unavailable, not a public default or a failed execution. A total
operation reads every ordered operand at the selected role before applying its
mathematical function. Consequently an unused argument still limits availability.

This model supplies mathematical meaning, not admission of an entire native
program. In particular, nonempty availability, declared input/result scopes and
the validity of restrictions remain formation obligations. No communication,
resource usage, cryptographic agreement or native correspondence follows from a
family of values.
-/

set_option autoImplicit false

namespace Zkc.Source.RoleFamily

variable {Role Ty A B : Type} {Value : Ty → Type}

/-- A role's component is present independently of every other role's value. -/
abbrev Family (Role A : Type) := Role → Option A

/-- Availability records presence only; it asserts no equality between roles. -/
def available (value : Family Role A) (role : Role) : Bool :=
  (value role).isSome

/-- A restriction selects existing components. It cannot create a component. -/
def restrict (scope : Role → Bool) (value : Family Role A) : Family Role A :=
  fun role => if scope role then value role else none

@[simp] theorem available_restrict (scope : Role → Bool) (value : Family Role A)
    (role : Role) :
    available (restrict scope value) role = (scope role && available value role) := by
  cases h : scope role <;> simp [available, restrict, h]

/-- Restricting twice is intersection, not a transfer between participants. -/
theorem restrict_restrict (first second : Role → Bool) (value : Family Role A) :
    restrict second (restrict first value) =
      restrict (fun role => first role && second role) value := by
  funext role
  cases hf : first role <;> cases hs : second role <;> simp [restrict, hf, hs]

@[simp] theorem restrict_component (scope : Role → Bool) (value : Family Role A)
    (role : Role) (selected : scope role = true) :
    restrict scope value role = value role := by simp [restrict, selected]

/-- Read all arguments in their declared order, retaining repeated positions. -/
def read (role : Role) : {types : List Ty} →
    Values (fun ty => Family Role (Value ty)) types → Option (Values Value types)
  | [], .nil => some .nil
  | _ :: _, .cons value rest => do
      let head ← value role
      let tail ← read role rest
      pure (.cons head tail)

/-- Read an already projected environment without access to any other role. -/
def sequence : {types : List Ty} →
    Values (fun ty => Option (Value ty)) types → Option (Values Value types)
  | [], .nil => some .nil
  | _ :: _, .cons value rest => do
      let head ← value
      let tail ← sequence rest
      pure (.cons head tail)

/-- The conjunction includes every operand even when the operation ignores it. -/
def allAvailable (role : Role) : {types : List Ty} →
    Values (fun ty => Family Role (Value ty)) types → Bool
  | [], .nil => true
  | _ :: _, .cons value rest => available value role && allAvailable role rest

theorem read_available (role : Role) {types : List Ty}
    (args : Values (fun ty => Family Role (Value ty)) types) :
    (read role args).isSome = allAvailable role args := by
  induction args with
  | nil => rfl
  | cons value rest ih =>
      simp only [allAvailable, ← ih, available]
      cases head : value role <;> cases tail : read role rest <;>
        simp only [read, head, tail] <;> rfl

/-- Pointwise application of a total, deterministic mathematical operation. -/
def apply {types : List Ty} (operation : Values Value types → A)
    (args : Values (fun ty => Family Role (Value ty)) types) : Family Role A :=
  fun role => (read role args).map operation

theorem apply_available {types : List Ty} (operation : Values Value types → A)
    (args : Values (fun ty => Family Role (Value ty)) types) (role : Role) :
    available (apply operation args) role = allAvailable role args := by
  simp [available, apply, read_available]

/-- Equality of the chosen mathematical functions lifts to every component.
No assertion about other dialect operations is inferred from their types. -/
theorem apply_congr {types : List Ty} (first second : Values Value types → A)
    (same : ∀ args, first args = second args)
    (args : Values (fun ty => Family Role (Value ty)) types) :
    apply first args = apply second args := by
  have h : first = second := funext same
  rw [h]

/-- Componentwise equality is the premise for a whole-family replacement. -/
theorem ext (first second : Family Role A)
    (components : ∀ role, first role = second role) : first = second :=
  funext components

/-- Agreement on a selected scope suffices only after selecting that scope. -/
theorem restrict_congr (scope : Role → Bool) (first second : Family Role A)
    (same : ∀ role, scope role = true → first role = second role) :
    restrict scope first = restrict scope second := by
  funext role
  cases h : scope role with
  | false => simp [restrict, h]
  | true => simp [restrict, h, same role h]

/-- A role-local environment contains no components belonging to other roles. -/
def project {types : List Ty}
    (env : Environment (fun ty => Family Role (Value ty)) types) (role : Role) :
    Environment (fun ty => Option (Value ty)) types := fun ref => env ref role

/-- Ordered operand capture commutes with selecting one role's components. -/
theorem read_operands {types args : List Ty}
    (env : Environment (fun ty => Family Role (Value ty)) types)
    (operands : Operands types args) (role : Role) :
    read role (operands.eval env) =
      sequence (operands.eval (project env role)) := by
  induction operands with
  | nil => rfl
  | cons value rest ih => simp only [Operands.eval, read, sequence, project, ih]

@[simp] theorem project_push {types : List Ty} {ty : Ty}
    (env : Environment (fun ty => Family Role (Value ty)) types)
    (value : Family Role (Value ty)) (role : Role) :
    @Eq (Environment (fun sort => Option (Value sort)) (ty :: types))
      (project (env.push value) role) (Environment.push (project env role) (value role)) := by
  funext sort ref
  cases ref <;> rfl

end Zkc.Source.RoleFamily
