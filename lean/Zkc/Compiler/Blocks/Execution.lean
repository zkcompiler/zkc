import Zkc.Compiler.Blocks.Expressions
import Zkc.Transformations.Memoization

/-! Primitive expression compilation with an explicit effectful continuation and immutable caching. -/

set_option autoImplicit false
namespace Zkc.Compiler.Blocks

section

-- Explicit stateful actions coexist with the cacheable pure primitive calls.
-- State is retained in the final result. Effects can return rejection/phase/
-- cursor/draw observations; arbitrary hidden native failures are not inferred.
inductive Program (V A O : Type) where
  | done : O → Program V A O
  | pureCall : Key V → (V → Program V A O) → Program V A O
  | action : A → (V → Program V A O) → Program V A O

variable {V A O S E : Type}

def emits (es : List E) (p : Zkc.Transformations.Memoization.Client (Key V) V E O) : Zkc.Transformations.Memoization.Client (Key V) V E O :=
  es.foldr Zkc.Transformations.Memoization.Client.emit p

theorem run_emits (f : Key V → V) (es : List E) (p : Zkc.Transformations.Memoization.Client (Key V) V E O) :
    Zkc.Transformations.Memoization.run f (emits es p) = (es ++ (Zkc.Transformations.Memoization.run f p).1, (Zkc.Transformations.Memoization.run f p).2) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [emits, Zkc.Transformations.Memoization.run] at ih ⊢; rw [ih]; simp

def runProgram (f : Key V → V) (handler : A → S → V × S × List E) :
    Program V A O → S → List E × (O × S)
  | .done o, s => ([],o,s)
  | .pureCall key next, s => runProgram f handler (next (f key)) s
  | .action a next, s =>
    let r := handler a s
    let result := runProgram f handler (next r.1) r.2.1
    (r.2.2 ++ result.1, result.2)

-- Elaborate an explicit stateful handler into the existing pure-client model.
-- This is a mathematical state interpretation, not a claim that Rust is pure.
def lower (handler : A → S → V × S × List E) :
    Program V A O → S → Zkc.Transformations.Memoization.Client (Key V) V E (O × S)
  | .done o, s => .done (o,s)
  | .pureCall key next, s => .call key (fun v => lower handler (next v) s)
  | .action a next, s =>
    let r := handler a s
    emits r.2.2 (lower handler (next r.1) r.2.1)

theorem lower_correct (f : Key V → V) (handler : A → S → V × S × List E)
    (p : Program V A O) (s : S) :
    Zkc.Transformations.Memoization.run f (lower handler p s) = runProgram f handler p s := by
  induction p generalizing s with
  | done o => rfl
  | pureCall key next ih => exact ih (f key) s
  | action a next ih =>
    simp only [lower,runProgram,run_emits]
    rw [ih]

def compile (env : Nat → V) (truth : V → Bool) :
    Expr V → (V → Program V A O) → Program V A O
  | .input i, next => next (env i)
  | .literal v, next => next v
  | .apply op a b, next =>
    compile env truth a (fun x => compile env truth b (fun y => .pureCall (op,x,y) next))
  | .choose c a b, next =>
    compile env truth c (fun v => if truth v then compile env truth a next else compile env truth b next)

theorem compile_correct (f : Key V → V) (truth : V → Bool) (env : Nat → V)
    (handler : A → S → V × S × List E) (e : Expr V)
    (next : V → Program V A O) (s : S) :
    runProgram f handler (compile env truth e next) s =
      runProgram f handler (next (eval f truth env e)) s := by
  induction e generalizing next with
  | input i => rfl
  | literal v => rfl
  | apply op a b iha ihb =>
    simp only [compile,eval]
    rw [iha,ihb]
    rfl
  | choose c a b ihc iha ihb =>
    simp only [compile,eval]
    rw [ihc]
    split
    · exact iha next
    · exact ihb next

theorem memoized_module_correct [DecidableEq V]
    (f : Key V → V) (truth : V → Bool) (env : Nat → V)
    (handler : A → S → V × S × List E) (e : Expr V)
    (next : V → Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Key V) V → Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    (Zkc.Transformations.Memoization.runMemo f store cache (lower handler (compile env truth e next) s)).1 =
      runProgram f handler (next (eval f truth env e)) s ∧
    Zkc.Modules.ImmutableCache.Valid f (Zkc.Transformations.Memoization.runMemo f store cache (lower handler (compile env truth e next) s)).2 := by
  obtain ⟨ho,hv⟩ := Zkc.Transformations.Memoization.client_preservation f store
    (lower handler (compile env truth e next) s) cache valid
  exact ⟨ho.trans ((lower_correct f handler _ s).trans
    (compile_correct f truth env handler e next s)), hv⟩

end

end Zkc.Compiler.Blocks
