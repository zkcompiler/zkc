import Zkc.Protocols.BackendProfiles.Definitions
import Zkc.Compiler.Readback.Compilation
import Zkc.Compiler.Blocks.Rewriting
import Zkc.Compiler.Blocks.BoundedCache

set_option autoImplicit false

namespace Zkc.Protocols.BackendProfiles
open Zkc.Compiler.Readback

variable {V A O S E : Type}

def nativeModule (r : Request) (literal : Literal → V) (truth : V → Bool)
    (env : Nat → V) (next : List V → Zkc.Compiler.Blocks.Program V A O) : Zkc.Compiler.Blocks.Program V A O :=
  Zkc.Compiler.Readback.compileNativeBlock (resolve r.profile) literal truth r.native env
    (fun locals => next (Zkc.Compiler.Blocks.exports r.nativeExports locals))

-- Equality of interaction trees preserves lazy control and ordered logical
-- calls, stronger than only evaluating both programs with one pure function.
theorem accepted_program (r : Request) (ok : check r = .accepted)
    (literal : Literal → V) (truth : V → Bool) (env : Nat → V)
    (next : List V → Zkc.Compiler.Blocks.Program V A O) :
    nativeModule r literal truth env next =
      Zkc.Compiler.Blocks.moduleCall truth (embedBlock literal r.expected) r.expectedExports env next := by
  obtain ⟨hb,ho⟩ := accepted_readback r ok
  unfold nativeModule Zkc.Compiler.Blocks.moduleCall
  rw [ho,Zkc.Compiler.Readback.read_block_program (resolve r.profile) literal truth _ _ hb]

-- Reuse the actual prior replacement theorem. The relation is still a
-- separate premise; successful lowering does not prove an algebraic rewrite.
theorem accepted_replacement [DecidableEq V] (r : Request) (ok : check r = .accepted)
    (literal : Literal → V) (truth : V → Bool) (f : Zkc.Compiler.Blocks.Key V → V)
    (handler : A → S → V × S × List E) (source : Zkc.Compiler.Blocks.Block V) (ss : List Nat)
    (pre : (Nat → V) → Prop)
    (relation : Zkc.Compiler.Blocks.EquivalentOn f truth pre source (embedBlock literal r.expected) ss r.expectedExports)
    (env : Nat → V) (hp : pre env) (next : List V → Zkc.Compiler.Blocks.Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Zkc.Compiler.Blocks.Key V) V → Zkc.Compiler.Blocks.Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Zkc.Compiler.Blocks.Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    (Zkc.Transformations.Memoization.runMemo f store cache (Zkc.Compiler.Blocks.lower handler (nativeModule r literal truth env next) s)).1 =
      Zkc.Compiler.Blocks.runProgram f handler (Zkc.Compiler.Blocks.moduleCall truth source ss env next) s := by
  rw [accepted_program r ok]
  exact (Zkc.Compiler.Blocks.replacement_with_sharing f truth handler pre source _ ss _ relation env hp next s store cache valid).1

theorem accepted_bounded_memo [DecidableEq V] {n : Nat} (r : Request) (ok : check r = .accepted)
    (literal : Literal → V) (truth : V → Bool) (f : Zkc.Compiler.Blocks.Key V → V)
    (handler : A → S → V × S × List E) (env : Nat → V)
    (next : List V → Zkc.Compiler.Blocks.Program V A O) (s : S)
    (slot : Zkc.Compiler.Blocks.Key V → Option (Fin n)) (cache : Zkc.Modules.BoundedCache.Slots n (Zkc.Compiler.Blocks.Key V) V) (valid : Zkc.Modules.BoundedCache.Valid f cache) :
    (Zkc.Modules.BoundedCache.run f slot cache (Zkc.Compiler.Blocks.lower handler (nativeModule r literal truth env next) s)).1 =
      Zkc.Compiler.Blocks.runProgram f handler (next (Zkc.Compiler.Blocks.exports r.expectedExports
        (Zkc.Compiler.Blocks.runBlock f truth (embedBlock literal r.expected) env))) s := by
  rw [accepted_program r ok]
  exact (Zkc.Compiler.Blocks.BoundedCache.bounded_block_correct f truth handler (embedBlock literal r.expected) env
    (fun locals => next (Zkc.Compiler.Blocks.exports r.expectedExports locals)) s slot cache valid).1

end Zkc.Protocols.BackendProfiles
