import Std

/-! Public dimension expressions with indexed parameter scope and substitution. -/

set_option autoImplicit false

namespace Zkc.Source.PublicDimensions
-- Fin n expresses the public scope; private/future values have no constructor.
inductive Dim (n : Nat) where
  | lit : Nat → Dim n
  | param : Fin n → Dim n
  | add : Dim n → Dim n → Dim n
  | mul : Dim n → Dim n → Dim n
  deriving Repr

variable {n m : Nat}

def Dim.eval (ρ : Fin n → Nat) : Dim n → Nat
  | .lit k => k
  | .param i => ρ i
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ

def Dim.subst (σ : Fin n → Dim m) : Dim n → Dim m
  | .lit k => .lit k
  | .param i => σ i
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)

theorem eval_subst (e : Dim n) (σ : Fin n → Dim m) (ρ : Fin m → Nat) :
    (e.subst σ).eval ρ = e.eval (fun i => (σ i).eval ρ) := by
  induction e with
  | lit => rfl
  | param => rfl
  | add a b ha hb => simp [Dim.subst, Dim.eval, ha, hb]
  | mul a b ha hb => simp [Dim.subst, Dim.eval, ha, hb]

inductive RawDim where
  | lit : Nat → RawDim
  | pub : Nat → RawDim
  | hidden : Nat → RawDim
  | future : Nat → RawDim
  | add : RawDim → RawDim → RawDim
  | mul : RawDim → RawDim → RawDim
  deriving Repr

def RawDim.scope (n : Nat) : RawDim → Option (Dim n)
  | .lit k => some (.lit k)
  | .pub i => if h : i < n then some (.param ⟨i,h⟩) else none
  | .hidden _ | .future _ => none
  | .add a b => return .add (← a.scope n) (← b.scope n)
  | .mul a b => return .mul (← a.scope n) (← b.scope n)

def publicEnv (xs : List Nat) (n : Nat) : Option (Fin n → Nat) :=
  if xs.length = n then some (fun i => xs[i.val]!) else none

/-- Successful dimension binding retains the exact supplied entries in order.
The length check makes the total lookup's fallback unreachable at every index. -/
theorem publicEnv_exact (xs : List Nat) (n : Nat) (env : Fin n → Nat)
    (formed : publicEnv xs n = some env) :
    xs.length = n ∧ ∀ i : Fin n, xs[i.val]? = some (env i) := by
  unfold publicEnv at formed
  split at formed
  next size =>
    cases Option.some.inj formed
    refine ⟨size, fun i => ?_⟩
    have within : i.val < xs.length := by omega
    simp [within]
  next size => simp at formed

end Zkc.Source.PublicDimensions
