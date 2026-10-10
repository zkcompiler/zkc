import Zkc.Modules.ImmutableCache

/-! Memoization of finite, adaptive clients of immutable operations.
Storage choices may depend on the cache. Return values and ordered emitted events
are preserved under validity relative to the actual fixed provider.
-/

set_option autoImplicit false

namespace Zkc.Transformations.Memoization

open Modules.ImmutableCache

variable {K V E O : Type}

-- Finite, result-dependent clients. Emits are visible, pure calls are not.
-- O can contain failure classes, unread bytes, provider state and final values.
-- This does not itself interpret a Rust verifier or permit effectful calls.
inductive Client (K V E O : Type) where
  | done : O → Client K V E O
  | emit : E → Client K V E O → Client K V E O
  | call : K → (V → Client K V E O) → Client K V E O

def run (f : K → V) : Client K V E O → List E × O
  | .done o => ([], o)
  | .emit e p => let r := run f p; (e :: r.1, r.2)
  | .call k next => run f (next (f k))

def runMemo [DecidableEq K] (f : K → V) (store : Cache K V → K → Bool)
    (c : Cache K V) : Client K V E O → (List E × O) × Cache K V
  | .done o => (([], o), c)
  | .emit e p => let r := runMemo f store c p; ((e :: r.1.1, r.1.2), r.2)
  | .call k next => let r := lookup f store c k; runMemo f store r.2 (next r.1)

theorem client_preservation [DecidableEq K] (f : K → V)
    (store : Cache K V → K → Bool) (p : Client K V E O)
    (c : Cache K V) (h : Valid f c) :
    (runMemo f store c p).1 = run f p ∧ Valid f (runMemo f store c p).2 := by
  induction p generalizing c with
  | done o => exact ⟨rfl,h⟩
  | emit e p ih =>
    obtain ⟨hv,hc⟩ := ih c h
    constructor
    · simp only [runMemo,run]; rw [hv]
    · exact hc
  | call k next ih =>
    have hc := lookup_valid f store c k h
    have hv := lookup_value f store c k h
    simpa only [runMemo,run,hv] using ih (f k) (lookup f store c k).2 hc

theorem arbitrary_policy_same_observer [DecidableEq K] (f : K → V)
    (a b : Cache K V → K → Bool) (p : Client K V E O) :
    (runMemo f a (fun _ => none) p).1 = (runMemo f b (fun _ => none) p).1 :=
  (client_preservation f a p _ (empty_valid f)).1.trans
    (client_preservation f b p _ (empty_valid f)).1.symm


end Zkc.Transformations.Memoization
