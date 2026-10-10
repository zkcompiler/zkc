import Zkc.Compiler.Blocks.Rewriting

/-! Complete contextual state refinement for the admitted block replacement. Parsing is a separate boundary. -/

set_option autoImplicit false
namespace Zkc.Compiler.Blocks.StateRefinement

open Zkc.Compiler.Blocks

section
variable {V A O S T E : Type}

def RunRel (R : S → T → Prop) (x : List E × (O × S)) (y : List E × (O × T)) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ R x.2.2 y.2.2

def HandlerRel (R : S → T → Prop)
    (left : A → S → V × S × List E) (right : A → T → V × T × List E) : Prop :=
  ∀ a s t, R s t →
    (left a s).1 = (right a t).1 ∧
    (left a s).2.2 = (right a t).2.2 ∧ R (left a s).2.1 (right a t).2.1

-- Same replies and observations allow the same program to use different
-- representations of its caller state. Native partiality is not inferred.
theorem run_related (f : Key V → V) (R : S → T → Prop)
    (left : A → S → V × S × List E) (right : A → T → V × T × List E)
    (handlers : HandlerRel R left right) (p : Program V A O)
    (s : S) (t : T) (states : R s t) :
    RunRel R (runProgram f left p s) (runProgram f right p t) := by
  induction p generalizing s t with
  | done o => exact ⟨rfl, rfl, states⟩
  | pureCall k next ih => exact ih (f k) s t states
  | action a next ih =>
    obtain ⟨reply, events, related⟩ := handlers a s t states
    have h := ih (left a s).1 (left a s).2.1 (right a t).2.1 related
    rw [reply] at h
    dsimp [RunRel, runProgram]
    rw [reply, events]
    exact ⟨congrArg ((right a t).2.2 ++ ·) h.1, h.2⟩

-- This corollary consumes the actual Zkc.Compiler.Blocks admission theorem. It is a join,
-- not a new local block language or a theorem about arbitrary stateful bodies.
theorem admitted_related [DecidableEq V]
    (registry : String → Option (Signature String)) (typeOf : V → String) (flag : String)
    (f : Key V → V) (truth : V → Bool) (types : Respects registry typeOf f)
    (R : S → T → Prop)
    (left : A → S → V × S × List E) (right : A → T → V × T × List E)
    (handlers : HandlerRel R left right) (ctx : Context String)
    (source target : Block V) (ss ts : List (Nat × String)) (rule : Rule)
    (meaning : rule = .horner → HornerMeaning f truth (Fits typeOf ctx))
    (ok : admission registry typeOf flag ctx source target ss ts rule = true)
    (env : Nat → V) (fit : Fits typeOf ctx env) (next : List V → Program V A O)
    (s : S) (t : T) (states : R s t)
    (store : Zkc.Modules.ImmutableCache.Cache (Key V) V → Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    RunRel R
      (runProgram f left (moduleCall truth source (ss.map Prod.fst) env next) s)
      (Zkc.Transformations.Memoization.runMemo f store cache
        (lower right (moduleCall truth target (ts.map Prod.fst) env next) t)).1 ∧
    Zkc.Modules.ImmutableCache.Valid f (Zkc.Transformations.Memoization.runMemo f store cache
      (lower right (moduleCall truth target (ts.map Prod.fst) env next) t)).2 := by
  obtain ⟨_, _, equality, cacheValid⟩ := admission_sound registry typeOf flag f truth types
    right ctx source target ss ts rule meaning ok env fit next t store cache valid
  refine ⟨?_, cacheValid⟩
  rw [equality]
  exact run_related f R left right handlers _ s t states

-- No zero, identities, additive associativity, commutativity or inverses are
-- needed for this particular parenthesized identity. This is sufficiency,
-- not a claim that these two global laws are logically necessary/minimal.
theorem horner_two_laws {F : Type} [Add F] [Mul F]
    (distribute : ∀ x y z : F, (x + y) * z = x*z + y*z)
    (associate : ∀ x y z : F, (x*y)*z = x*(y*z)) (a b c r : F) :
    a + (b*r + c*(r*r)) = a + ((b+c*r)*r) := by
  rw [distribute, associate]


end

end Zkc.Compiler.Blocks.StateRefinement
