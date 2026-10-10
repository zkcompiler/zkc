import Zkc.Source.PublicDimensions

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.ParameterFamily
open Zkc.Source.PublicDimensions

variable {n m : Nat}

structure Family (n : Nat) where
  rounds : Dim n
  degree : Dim n
structure Params where
  rounds : Nat
  degree : Nat
  deriving Repr, DecidableEq

def Family.inst (f : Family n) (ρ : Fin n → Nat) : Params :=
  ⟨f.rounds.eval ρ, f.degree.eval ρ⟩
def Family.subst (f : Family n) (σ : Fin n → Dim m) : Family m :=
  ⟨f.rounds.subst σ, f.degree.subst σ⟩
theorem inst_subst (f : Family n) (σ : Fin n → Dim m) (ρ : Fin m → Nat) :
    (f.subst σ).inst ρ = f.inst (fun i => (σ i).eval ρ) := by
  simp [Family.inst, Family.subst, eval_subst]

/-- Public round count and degree are independently supplied parameters. -/
def sumcheckFamily : Family 2 := ⟨.param 0,.param 1⟩
def env2 (rounds degree : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then rounds else degree

end Zkc.Protocols.AlgebraicRounds.ParameterFamily
