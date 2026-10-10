import Zkc.Compiler.Blocks.Analysis

/-! Registry-relative formation and export typing. Formation does not supply operation equations. -/

set_option autoImplicit false
namespace Zkc.Compiler.Blocks

section

structure Signature (T : Type) where
  left : T
  right : T
  result : T
  deriving DecidableEq, Repr

variable {T V : Type} [DecidableEq T]
abbrev Context (T : Type) := Nat → Option T

-- A registry is resolved by the surrounding provider binding, not by the body.
-- These are total logical pure functions; native purity is a separate premise.
def infer (registry : String → Option (Signature T)) (typeOf : V → T)
    (flag : T) (ctx : Context T) : Expr V → Option T
  | .input i => ctx i
  | .literal v => some (typeOf v)
  | .apply op a b => match registry op, infer registry typeOf flag ctx a,
      infer registry typeOf flag ctx b with
    | some s, some x, some y => if x = s.left ∧ y = s.right then some s.result else none
    | _, _, _ => none
  | .choose c a b => match infer registry typeOf flag ctx c,
      infer registry typeOf flag ctx a, infer registry typeOf flag ctx b with
    | some z, some x, some y => if z = flag ∧ x = y then some x else none
    | _, _, _ => none

def Fits (typeOf : V → T) (ctx : Context T) (env : Nat → V) : Prop :=
  ∀ i t, ctx i = some t → typeOf (env i) = t

def Respects (registry : String → Option (Signature T)) (typeOf : V → T)
    (f : Key V → V) : Prop :=
  ∀ op s x y, registry op = some s → typeOf x = s.left → typeOf y = s.right →
    typeOf (f (op,x,y)) = s.result

theorem infer_sound (registry : String → Option (Signature T)) (typeOf : V → T)
    (flag : T) (f : Key V → V) (truth : V → Bool)
    (law : Respects registry typeOf f) (ctx : Context T) (env : Nat → V)
    (fit : Fits typeOf ctx env) (e : Expr V) (t : T)
    (ok : infer registry typeOf flag ctx e = some t) :
    typeOf (eval f truth env e) = t := by
  induction e generalizing t with
  | input i => exact fit i t ok
  | literal v => simpa [infer, eval] using ok
  | apply op a b iha ihb =>
    simp only [infer] at ok
    split at ok <;> try contradiction
    next s x y hs hx hy =>
      split at ok <;> try contradiction
      next h =>
        have ht : s.result = t := Option.some.inj ok
        exact (law op s _ _ hs ((iha x hx).trans h.1) ((ihb y hy).trans h.2)).trans ht
  | choose c a b ihc iha ihb =>
    simp only [infer] at ok
    split at ok <;> try contradiction
    next z x y hz hx hy =>
      split at ok <;> try contradiction
      next h =>
        have ht : x = t := Option.some.inj ok
        simp only [eval]
        split
        · exact (iha x hx).trans ht
        · exact (ihb y hy).trans (h.2.symm.trans ht)

def inferBlock (registry : String → Option (Signature T)) (typeOf : V → T)
    (flag : T) : Block V → Context T → Option (Context T)
  | [], ctx => some ctx
  | (dst,e) :: rest, ctx =>
    if (ctx dst).isSome then none else
    match infer registry typeOf flag ctx e with
    | none => none
    | some t => inferBlock registry typeOf flag rest (Function.update ctx dst (some t))

theorem infer_block_sound (registry : String → Option (Signature T)) (typeOf : V → T)
    (flag : T) (f : Key V → V) (truth : V → Bool) (law : Respects registry typeOf f)
    (block : Block V) (ctx out : Context T) (env : Nat → V)
    (fit : Fits typeOf ctx env) (ok : inferBlock registry typeOf flag block ctx = some out) :
    Fits typeOf out (runBlock f truth block env) := by
  induction block generalizing ctx out env with
  | nil => simpa [inferBlock, runBlock, Option.some.inj ok] using fit
  | cons step rest ih =>
    rcases step with ⟨dst,e⟩
    simp only [inferBlock] at ok
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    next _ t ht =>
      apply ih _ out _ _ ok
      intro i u hu
      by_cases hi : i = dst
      · subst i
        simp only [Function.update_self, Option.some.injEq] at hu
        simpa [assign, hu] using infer_sound registry typeOf flag f truth law ctx env fit e t ht
      · simp only [Function.update_of_ne hi] at hu
        simpa [assign, Function.update_of_ne hi] using fit i u hu

-- Checked output types and scoped local formation, not equivalence or security.
def exportsCheck (ctx : Context T) (exports : List (Nat × T)) : Bool :=
  exports.all fun it => decide (ctx it.1 = some it.2)

theorem checked_exports (registry : String → Option (Signature T)) (typeOf : V → T)
    (flag : T) (f : Key V → V) (truth : V → Bool) (law : Respects registry typeOf f)
    (block : Block V) (ctx out : Context T) (env : Nat → V) (exports : List (Nat × T))
    (fit : Fits typeOf ctx env) (ok : inferBlock registry typeOf flag block ctx = some out)
    (he : exportsCheck out exports = true) :
    ∀ i t, (i,t) ∈ exports → typeOf (runBlock f truth block env i) = t := by
  intro i t hit
  apply infer_block_sound registry typeOf flag f truth law block ctx out env fit ok i t
  exact of_decide_eq_true ((List.all_eq_true.mp he) (i,t) hit)


end

end Zkc.Compiler.Blocks
