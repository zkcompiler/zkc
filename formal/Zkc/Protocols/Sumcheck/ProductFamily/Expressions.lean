import Zkc.Protocols.Sumcheck.ProductFamily.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.ProductFamily
open Zkc.Protocols.AlgebraicRounds.Scalar

inductive Expr (I : Type) where
  | var : I → Expr I
  | add : Expr I → Expr I → Expr I
  | mul : Expr I → Expr I → Expr I
deriving DecidableEq

def Expr.rename {I J} (f : I → J) : Expr I → Expr J
  | .var i => .var (f i)
  | .add a b => .add (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)
def Expr.eval {I F} [Semiring F] (env : I → F) : Expr I → F
  | .var i => env i
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
theorem eval_rename {I J F} [Semiring F] (f : I → J) (env : J → F) (e : Expr I) :
    (e.rename f).eval env = e.eval (env ∘ f) := by
  induction e <;> simp_all [Expr.rename, Expr.eval, Function.comp_def]

-- Typed value namespaces, distinct from attachment and operand-role binders.
inductive Ref (n : Nat) where
  | claim
  | coeff : Fin n → Fin 3 → Ref n
  | draw : Fin n → Ref n
deriving DecidableEq
def origin {n} : Ref n → Nat
  | .claim => 0
  | .coeff i j => 1 + 5*i.val + j.val
  | .draw i => 5 + 5*i.val
theorem origin_injective (n : Nat) : Function.Injective (@origin n) := by
  intro a b h
  cases a with
  | claim => cases b <;> simp_all [origin] <;> omega
  | coeff i j =>
    cases b with
    | claim => simp_all [origin]
    | coeff k l =>
      simp only [origin] at h
      have hi : i = k := Fin.ext (by omega)
      have hj : j = l := Fin.ext (by omega)
      subst hi; subst hj; rfl
    | draw k => simp only [origin] at h; omega
  | draw i =>
    cases b with
    | claim => simp_all [origin]
    | coeff k l => simp only [origin] at h; omega
    | draw k => simp only [origin] at h; have hi : i = k := Fin.ext (by omega); subst hi; rfl

abbrev E := Expr Nat
def cf (i j : Nat) : E := .var (1+5*i+j)
def dr (i : Nat) : E := .var (5+5*i)
def poly (a b c r : E) : E := .add a (.add (.mul b r) (.mul c (.mul r r)))
def bound (i : Nat) : E := .add (.add (.add (cf i 0) (cf i 0)) (cf i 1)) (cf i 2)
def atRound (i : Nat) : E := poly (cf i 0) (cf i 1) (cf i 2) (dr i)
def roundCheck (i : Nat) : Nat × E × E :=
  (4+5*i, bound i, if i=0 then .var 0 else atRound (i-1))
def productExpr (acc : E) : List Nat → E
  | [] => acc
  | i :: is => productExpr (.mul acc (dr i)) is
def finalCheck (m : Nat) : Nat × E × E :=
  (1+5*(m+1), atRound m,
    .add (productExpr (dr 0) ((List.range m).map (·+1))) (dr 0))
def checks (m : Nat) : List (Nat × E × E) :=
  (List.range (m+1)).map roundCheck ++ [finalCheck m]

variable {F : Type} [CommRing F]
def loadRound (env : Nat → F) (i : Nat) : Round F :=
  ⟨env (1+5*i), env (1+5*i+1), env (1+5*i+2), env (5+5*i)⟩
theorem eval_bound (env : Nat → F) (i : Nat) :
    (bound i).eval env = boundary (loadRound env i) := by
  rfl
theorem eval_atRound (env : Nat → F) (i : Nat) :
    (atRound i).eval env = value (loadRound env i) := by
  simp only [atRound, poly, cf, dr, Expr.eval, value, loadRound, Nat.add_zero]
  ring
theorem eval_product (env : Nat → F) (acc : E) (is : List Nat) :
    (productExpr acc is).eval env =
      acc.eval env * (is.map (fun i => env (5+5*i))).prod := by
  induction is generalizing acc with
  | nil => simp [productExpr]
  | cons i is ih => simp [productExpr, ih, Expr.eval, dr, mul_assoc]
theorem eval_final_rhs (env : Nat → F) (m : Nat) :
    (finalCheck m).2.2.eval env =
      (env 5 :: ((List.range m).map (fun i => env (5+5*(i+1))))).prod + env 5 := by
  simp [finalCheck, Expr.eval, eval_product, dr, List.map_map, Function.comp_def]

-- The templates are useful to a source checker at arbitrary m. Concrete
-- canonical files are quoted separately; this is not a proved MLIR parser.
theorem round_equation (env : Nat → F) (i : Nat) :
    (roundCheck i).2.1.eval env = (roundCheck i).2.2.eval env ↔
    boundary (loadRound env i) =
      (if i=0 then env 0 else value (loadRound env (i-1))) := by
  by_cases h : i=0 <;> simp [roundCheck, h, eval_bound, eval_atRound, Expr.eval]


end Zkc.Protocols.Sumcheck.ProductFamily
