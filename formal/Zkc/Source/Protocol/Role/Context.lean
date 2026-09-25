import Zkc.Source.Protocol.Context

/-! A single role's typed values. Foreign ports survive only as static indices.
Neither inputs, call results nor loop accumulators contain peer values.
-/

set_option autoImplicit false

namespace Zkc.Source.Protocol.Role

variable {Party Ty : Type} {Value : Ty → Type} {self : Party}
  {Γ Δ : List (Port Party Ty)}

abbrev Environment (Value : Ty → Type) (self : Party) (Γ : List (Port Party Ty)) :=
  {ty : Ty} → Var Γ (self, ty) → Value ty

def Environment.empty : Environment Value self [] := fun ref => nomatch ref

def Environment.push {ty : Ty} (env : Environment Value self Γ) (value : Value ty) :
    Environment Value self ((self, ty) :: Γ)
  | _, .here => value
  | _, .there ref => env ref

/-- Add static metadata without supplying any value for a foreign port. -/
def Environment.skip {owner : Party} {ty : Ty} (different : owner ≠ self)
    (env : Environment Value self Γ) : Environment Value self ((owner, ty) :: Γ)
  | _, .here => False.elim (different rfl)
  | _, .there ref => env ref

/-- Select only locally owned operands, including for mixed-role signatures. -/
def Environment.capture (env : Environment Value self Γ) (args : Operands Γ Δ) :
    Environment Value self Δ := fun ref => env (args.get ref)

private def split {T : Type} {Γ : List T} {ty : T} :
    (Δ : List T) → Var (Δ ++ Γ) ty → Sum (Var Δ ty) (Var Γ ty)
  | [], ref => .inr ref
  | _ :: _, .here => .inl .here
  | _ :: Δ, .there ref =>
      match split Δ ref with
      | .inl ref => .inl (.there ref)
      | .inr ref => .inr ref

def Environment.prepend (env : Environment Value self Γ)
    (values : Environment Value self Δ) : Environment Value self (Δ ++ Γ) :=
  fun ref => match split Δ ref with
    | .inl ref => values ref
    | .inr ref => env ref

/-- Looking past the first prepended port agrees with prepending the tail.
This equation is independent of the private context-splitting implementation. -/
@[simp] theorem Environment.prepend_there {head : Port Party Ty} {ty : Ty}
    (env : Environment Value self Γ) (values : Environment Value self (head :: Δ))
    (ref : Var (Δ ++ Γ) (self, ty)) :
    env.prepend values (.there ref) =
      env.prepend (fun tail => values (.there tail)) ref := by
  simp only [Environment.prepend, split]
  cases split Δ ref <;> rfl

def Environment.read (env : Environment Value self Γ) :
    {types : List Ty} → Operands Γ (owned self types) → Values Value types
  | [], .nil => .nil
  | _ :: _, .cons ref rest => .cons (env ref) (env.read rest)

end Zkc.Source.Protocol.Role
