import Zkc.Compiler.Blocks.Analysis
import Zkc.Modules.BoundedCache

set_option autoImplicit false
namespace Zkc.Compiler.Blocks.BoundedCache
open Zkc.Modules.BoundedCache

variable {V A O S E : Type} {n : Nat} [DecidableEq V]

-- The new replacement policy consumes the existing block compiler and effect
-- interpretation, not a fresh unrelated hash-program semantics.
theorem bounded_block_correct (f : Zkc.Compiler.Blocks.Key V → V) (truth : V → Bool)
    (handler : A → S → V × S × List E) (block : Zkc.Compiler.Blocks.Block V) (env : Nat → V)
    (next : (Nat → V) → Zkc.Compiler.Blocks.Program V A O) (s : S)
    (slot : Zkc.Compiler.Blocks.Key V → Option (Fin n)) (cache : Slots n (Zkc.Compiler.Blocks.Key V) V) (valid : Valid f cache) :
    (run f slot cache (Zkc.Compiler.Blocks.lower handler (Zkc.Compiler.Blocks.compileBlock truth block env next) s)).1 =
      Zkc.Compiler.Blocks.runProgram f handler (next (Zkc.Compiler.Blocks.runBlock f truth block env)) s ∧
    Valid f (run f slot cache (Zkc.Compiler.Blocks.lower handler (Zkc.Compiler.Blocks.compileBlock truth block env next) s)).2 := by
  obtain ⟨ho,hv⟩ := preservation f slot
    (Zkc.Compiler.Blocks.lower handler (Zkc.Compiler.Blocks.compileBlock truth block env next) s) cache valid
  exact ⟨ho.trans ((Zkc.Compiler.Blocks.lower_correct f handler _ s).trans
    (Zkc.Compiler.Blocks.compile_block_correct f truth handler block env next s)),hv⟩

-- Full result-dependent continuations may terminate early with a failure value
-- and emit already-observable events. No new cryptographic premise is involved.
theorem policy_same_context {m : Nat} (f : Zkc.Compiler.Blocks.Key V → V) (truth : V → Bool)
    (handler : A → S → V × S × List E) (block : Zkc.Compiler.Blocks.Block V) (env : Nat → V)
    (next : (Nat → V) → Zkc.Compiler.Blocks.Program V A O) (s : S)
    (a : Zkc.Compiler.Blocks.Key V → Option (Fin n)) (b : Zkc.Compiler.Blocks.Key V → Option (Fin m)) :
    (run f a (fun _ => none) (Zkc.Compiler.Blocks.lower handler (Zkc.Compiler.Blocks.compileBlock truth block env next) s)).1 =
    (run f b (fun _ => none) (Zkc.Compiler.Blocks.lower handler (Zkc.Compiler.Blocks.compileBlock truth block env next) s)).1 :=
  policy_independent f a b _


end Zkc.Compiler.Blocks.BoundedCache
