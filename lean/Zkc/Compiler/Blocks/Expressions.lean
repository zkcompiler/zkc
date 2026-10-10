import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Erase

/-! Pure primitive expressions and conservative data dependencies, including guards. -/

set_option autoImplicit false
namespace Zkc.Compiler.Blocks

section

-- V can contain words, digests, rows or another explicitly interpreted domain.
-- The language has total pure primitives; stateful actions belong to Program.
inductive Expr (V : Type) where
  | input : Nat → Expr V
  | literal : V → Expr V
  | apply : String → Expr V → Expr V → Expr V
  | choose : Expr V → Expr V → Expr V → Expr V
  deriving Repr, DecidableEq

abbrev Key (V : Type) := String × V × V

def eval {V : Type} (f : Key V → V) (truth : V → Bool) (env : Nat → V) : Expr V → V
  | .input i => env i
  | .literal v => v
  | .apply op a b => f (op, eval f truth env a, eval f truth env b)
  | .choose c a b => if truth (eval f truth env c) then eval f truth env a else eval f truth env b

def dependencies {V : Type} : Expr V → Finset Nat
  | .input i => {i}
  | .literal _ => ∅
  | .apply _ a b => dependencies a ∪ dependencies b
  | .choose c a b => dependencies c ∪ dependencies a ∪ dependencies b

def AgreeOn {V : Type} (d : Finset Nat) (a b : Nat → V) : Prop :=
  ∀ i ∈ d, a i = b i

theorem agree_union_left {V : Type} {d e : Finset Nat} {a b : Nat → V}
    (h : AgreeOn (d ∪ e) a b) : AgreeOn d a b := by
  intro i hi; exact h i (Finset.mem_union_left _ hi)

theorem agree_union_right {V : Type} {d e : Finset Nat} {a b : Nat → V}
    (h : AgreeOn (d ∪ e) a b) : AgreeOn e a b := by
  intro i hi; exact h i (Finset.mem_union_right _ hi)

-- An inferred sufficient dependency set, not a minimal semantic footprint.
theorem dependency_sound {V : Type} (f : Key V → V) (truth : V → Bool)
    (e : Expr V) (a b : Nat → V) (h : AgreeOn (dependencies e) a b) :
    eval f truth a e = eval f truth b e := by
  induction e with
  | input i => exact h i (Finset.mem_singleton_self i)
  | literal v => rfl
  | apply op x y ihx ihy =>
    simp only [dependencies] at h
    simp only [eval, ihx (agree_union_left h), ihy (agree_union_right h)]
  | choose c x y ihc ihx ihy =>
    simp only [dependencies] at h
    simp only [eval, ihc (agree_union_left (agree_union_left h)),
      ihx (agree_union_right (agree_union_left h)), ihy (agree_union_right h)]

def projectedContext {V : Type} (e : Expr V) (env : Nat → V) :
    {i : Nat // i ∈ dependencies e} → V := fun i => env i.val

theorem projected_key_sufficient {V : Type} (f : Key V → V) (truth : V → Bool)
    (e : Expr V) (a b : Nat → V) (h : projectedContext e a = projectedContext e b) :
    eval f truth a e = eval f truth b e := by
  apply dependency_sound f truth e a b
  intro i hi
  exact congrFun h ⟨i,hi⟩

def dependencyCheck {V : Type} (e : Expr V) (declared : Finset Nat) : Bool :=
  decide (dependencies e ⊆ declared)

theorem checked_dependency_sound {V : Type} (f : Key V → V) (truth : V → Bool)
    (e : Expr V) (declared : Finset Nat) (a b : Nat → V)
    (hc : dependencyCheck e declared = true) (ha : AgreeOn declared a b) :
    eval f truth a e = eval f truth b e := by
  have hs : dependencies e ⊆ declared := of_decide_eq_true hc
  apply dependency_sound f truth e a b
  intro i hi; exact ha i (hs hi)

-- Ignoring control dependencies is unsound even for total arithmetic.
theorem branch_condition_needed :
    eval (fun (_ : Key Nat) => 0) (fun x => x != 0) (fun _ => 0)
      (.choose (.input 0) (.literal 1) (.literal 2)) ≠
    eval (fun (_ : Key Nat) => 0) (fun x => x != 0) (fun _ => 1)
      (.choose (.input 0) (.literal 1) (.literal 2)) := by decide


end

end Zkc.Compiler.Blocks
