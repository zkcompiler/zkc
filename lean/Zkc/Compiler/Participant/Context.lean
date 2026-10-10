import Zkc.Source.Protocol.Context

/-! Participant environments expose only references at their own role.

Global port lists remain static typing metadata. They do not grant a participant
access to another role's values. The joint driver can assemble declared outputs.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Participant

open Zkc.Source Zkc.Source.Protocol

variable {Role Ty : Type} {Value : Ty → Type} {Γ Δ : List (Port Role Ty)}

abbrev LocalEnvironment (Value : Ty → Type) (role : Role) (Γ : List (Port Role Ty)) :=
  {ty : Ty} → Var Γ (role, ty) → Value ty

abbrev Environments (Value : Ty → Type) (Γ : List (Port Role Ty)) :=
  (role : Role) → LocalEnvironment Value role Γ

def separate (env : Environment (PortValue Value) Γ) : Environments Value Γ :=
  fun _ {_} ref => env ref

def assemble (envs : Environments Value Γ) : Environment (PortValue Value) Γ :=
  fun {port} ref => envs port.1 ref

@[simp] theorem assemble_separate (env : Environment (PortValue Value) Γ) :
    @Eq (Environment (PortValue Value) Γ) (assemble (separate env)) env := rfl

def readLocal (role : Role) (env : LocalEnvironment Value role Γ) :
    {types : List Ty} → Operands Γ (owned role types) → Values Value types
  | [], .nil => .nil
  | _ :: _, .cons ref rest => .cons (env ref) (readLocal role env rest)

theorem readLocal_separate (env : Environment (PortValue Value) Γ) (role : Role)
    {types : List Ty} (args : Operands Γ (owned role types)) :
    readLocal role (separate env role) args = localValues role (Operands.eval env args) := by
  induction types with
  | nil => cases args; rfl
  | cons ty types ih => cases args with
    | cons ref rest => exact congrArg (Values.cons (Value := Value) (ty := ty) (env ref)) (ih rest)

/-- Capture each participant's declared callee operands from that participant alone. -/
def capture (envs : Environments Value Γ) (args : Operands Γ Δ) : Environments Value Δ :=
  fun role {_} ref => envs role (args.get ref)

theorem capture_separate (env : Environment (PortValue Value) Γ) (args : Operands Γ Δ) :
    capture (separate env) args = separate (Operands.eval env args).get := by
  funext role ty ref
  exact (Operands.get_eval env args ref).symm

/-- A callee's local inputs cannot depend on changing another participant's environment. -/
theorem capture_local (left right : Environments Value Γ) (args : Operands Γ Δ) (role : Role)
    (same : @Eq (LocalEnvironment Value role Γ) (left role) (right role)) :
    @Eq (LocalEnvironment Value role Δ) (capture left args role) (capture right args role) := by
  funext ty ref
  exact congrArg (fun env : LocalEnvironment Value role Γ => env (args.get ref)) same

def push {port : Port Role Ty} (envs : Environments Value Γ) (value : Value port.2) :
    Environments Value (port :: Γ) := separate (Environment.push (assemble envs) value)

def prepend (envs : Environments Value Γ) (values : Values (PortValue Value) Δ) :
    Environments Value (Δ ++ Γ) := separate (Environment.prepend (assemble envs) values)

@[simp] theorem push_separate {port : Port Role Ty}
    (env : Environment (PortValue Value) Γ) (value : Value port.2) :
    push (port := port) (separate env) value = separate (Environment.push env value) := rfl

@[simp] theorem prepend_separate (env : Environment (PortValue Value) Γ)
    (values : Values (PortValue Value) Δ) :
    prepend (separate env) values = separate (Environment.prepend env values) := rfl

end Zkc.Compiler.Participant
