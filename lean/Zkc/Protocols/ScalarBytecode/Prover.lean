import Zkc.Protocols.ScalarBytecode.ProverPrograms
import Zkc.Transformations.EncodingReuse

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Prover
open Zkc.Realization.ByteEncoding Zkc.Protocols.ScalarBytecode.Codec
-- SHA implementation is an explicit interpretation parameter, not a fresh law.
abbrev Hash := Bytes → Bytes
def absorb (hash : Hash) (s b : Bytes) : Bytes := hash (s ++ [⟨0,by decide⟩] ++ b)
def draw (hash : Hash) (s : Bytes) : Bytes × Nat :=
  let s' := hash (s ++ [⟨1,by decide⟩] ++ Zkc.Protocols.ScalarBytecode.ProverPrograms.domainASCII)
  (s', valueBE (s'.take 8) % Zkc.Protocols.ScalarBytecode.Parameters.challengeBound)
def first (cheat : Bool) : List Nat := if cheat then Zkc.Protocols.ScalarBytecode.ProverPrograms.cheatFirst else Zkc.Protocols.ScalarBytecode.ProverPrograms.honestFirst
def program (cheat : Bool) : Zkc.Source.LocalArithmetic.Program := if cheat then Zkc.Protocols.ScalarBytecode.ProverPrograms.cheatProgram else Zkc.Protocols.ScalarBytecode.ProverPrograms.honestProgram
def values (cheat : Bool) (r : Nat) : List Nat := if cheat then [Zkc.Protocols.ScalarBytecode.AdaptiveProver.b0 r,r,0] else [r,r,0]
def prefixState (hash : Hash) (cheat : Bool) (claim : Nat) : Bytes :=
  (first cheat).foldl (fun s x => absorb hash s (enc x))
    (absorb hash (hash Zkc.Protocols.ScalarBytecode.ProverPrograms.sourceASCII) (enc claim))
def derived (hash : Hash) (cheat : Bool) (claim : Nat) : Bytes × Nat :=
  draw hash (prefixState hash cheat claim)
def localView (hash : Hash) (cheat : Bool) (claim : Nat) : Zkc.Source.LocalArithmetic.View :=
  Zkc.Protocols.ScalarBytecode.AdaptiveProver.view (derived hash cheat claim).2
-- The global interpretation has the SAME source-occurrence key 2. No network input.
def environment (hash : Hash) (cheat : Bool) (claim : Nat) : Zkc.Source.LocalArithmetic.Env :=
  fun k => if k = 2 then (derived hash cheat claim).2 else 0

theorem derived_support (hash : Hash) (cheat : Bool) (claim : Nat) :
    (derived hash cheat claim).2 < Zkc.Protocols.ScalarBytecode.Parameters.challengeBound :=
  Nat.mod_lt _ (by decide)
theorem derived_canonical (hash : Hash) (cheat : Bool) (claim : Nat) :
    (derived hash cheat claim).2 < Zkc.Protocols.ScalarBytecode.Parameters.modulus :=
  Nat.lt_trans (derived_support hash cheat claim) (by decide)
theorem view_realizes (hash : Hash) (cheat : Bool) (claim : Nat) :
    Zkc.Source.LocalArithmetic.Realizes (localView hash cheat claim) (environment hash cheat claim) := by
  intro k n h
  simp only [localView, Zkc.Protocols.ScalarBytecode.AdaptiveProver.view] at h
  split at h
  next hk => simp only [Option.some.injEq] at h; simp [environment, hk, h]
  next => simp at h

def raw (xs : List Nat) : Zkc.Source.MessageSchema.Raw := ⟨10,20,30,1,xs⟩
theorem values_valid (cheat : Bool) (r : Nat) (hr : r < Zkc.Protocols.ScalarBytecode.Parameters.modulus) :
    Zkc.Source.MessageSchema.Valid Zkc.Protocols.ScalarBytecode.AdaptiveProver.context (raw (values cheat r)) := by
  cases cheat with
  | false => simp [values, raw, Zkc.Source.MessageSchema.Valid, Zkc.Protocols.ScalarBytecode.AdaptiveProver.context, Zkc.Protocols.ScalarBytecode.Parameters.modulus] at hr ⊢; exact hr
  | true => exact Zkc.Protocols.ScalarBytecode.AdaptiveProver.output_valid r hr

theorem program_run (cheat : Bool) (r : Nat) (m : Zkc.Source.LocalArithmetic.Memory) :
    Zkc.Source.LocalArithmetic.checkedRun (program cheat) (Zkc.Protocols.ScalarBytecode.AdaptiveProver.view r) m = some ⟨values cheat r,m⟩ := by
  cases cheat with
  | false => exact Zkc.Protocols.ScalarBytecode.ProverPrograms.honest_meaning r m
  | true => exact Zkc.Protocols.ScalarBytecode.AdaptiveProver.block_run r m

-- This adapter reads only the scheduled round's 24 bytes, preserving the suffix.
-- It injects trusted nominal context after decoding; T5 headers never enter wire.
def receive (bs : Bytes) : Option (List Nat × Bytes) := do
  let (xs,tail) ← readWords 3 bs
  let payload ← Zkc.Source.MessageSchema.check Zkc.Protocols.ScalarBytecode.AdaptiveProver.context (raw xs)
  return (payload.val.values,tail)

theorem receive_legal (xs : List Nat) (hv : Zkc.Source.MessageSchema.Valid Zkc.Protocols.ScalarBytecode.AdaptiveProver.context (raw xs))
    (tail : Bytes) : receive (wire xs ++ tail) = some (xs,tail) := by
  have hl : xs.length = 3 := hv.2.2.2.2.2.2.1
  have hc : ∀ x ∈ xs, x < Zkc.Protocols.ScalarBytecode.Parameters.modulus := hv.2.2.2.2.2.2.2
  unfold receive
  rw [← hl, words_complete xs hc tail]
  simp only [bind, Option.bind]
  rw [Zkc.Source.MessageSchema.check_complete _ _ hv]
  rfl

def execute (hash : Hash) (cheat : Bool) (claim : Nat) (m : Zkc.Source.LocalArithmetic.Memory)
    (tail : Bytes) : Option (Bytes × Nat × List Nat × Bytes × Zkc.Source.LocalArithmetic.Memory) := do
  let d := derived hash cheat claim
  let result ← Zkc.Source.LocalArithmetic.checkedRun (program cheat) (localView hash cheat claim) m
  let decoded ← receive (wire result.sent ++ tail)
  return (d.1,d.2,decoded.1,decoded.2,result.memory)

-- The previously missing derived-view / canonical byte egress interface is discharged.
-- No caller supplies a canonical-r, realizes, output-valid, or codec-inverse premise.
theorem actual_interpreted_connection (hash : Hash) (cheat : Bool) (claim : Nat)
    (m : Zkc.Source.LocalArithmetic.Memory) (tail : Bytes) :
    execute hash cheat claim m tail =
      some ((derived hash cheat claim).1,(derived hash cheat claim).2,
        values cheat (derived hash cheat claim).2,tail,m) := by
  unfold execute localView
  rw [program_run]
  simp only [bind, Option.bind]
  rw [receive_legal _ (values_valid cheat _ (derived_canonical hash cheat claim))]
  rfl

-- Concrete bytes and the selected provider transitions instantiate W5 cache equality.
-- Equality includes the post-draw provider bytes, derived value, ordered absorbs, proof.
theorem cached_bytes_provider (hash : Hash) (cheat : Bool) (claim : Nat) :
    Zkc.Transformations.EncodingReuse.cached enc (absorb hash) (draw hash) (hash Zkc.Protocols.ScalarBytecode.ProverPrograms.sourceASCII)
      claim (first cheat) (values cheat) =
    Zkc.Transformations.EncodingReuse.direct enc (absorb hash) (draw hash) (hash Zkc.Protocols.ScalarBytecode.ProverPrograms.sourceASCII)
      claim (first cheat) (values cheat) :=
  Zkc.Transformations.EncodingReuse.cache_encoding_preserves _ _ _ _ _ _ _

-- The cache law's tuple is now identified with this materializer and codec.
theorem cached_tuple (hash : Hash) (cheat : Bool) (claim : Nat) :
    Zkc.Transformations.EncodingReuse.cached enc (absorb hash) (draw hash) (hash Zkc.Protocols.ScalarBytecode.ProverPrograms.sourceASCII)
      claim (first cheat) (values cheat) =
    ((derived hash cheat claim).1, (derived hash cheat claim).2,
      enc claim :: (first cheat).map enc,
      wire (first cheat ++ values cheat (derived hash cheat claim).2)) := by
  rw [cached_bytes_provider]
  rfl

-- Canonical input context is a checked entry gate; outside it Python's be8
-- and this total Nat encoder need not have the same behavior.
def admittedExecute (hash : Hash) (cheat : Bool) (claim : Nat) (m : Zkc.Source.LocalArithmetic.Memory)
    (tail : Bytes) : Option (Bytes × Nat × List Nat × Bytes × Zkc.Source.LocalArithmetic.Memory) :=
  if claim < Zkc.Protocols.ScalarBytecode.Parameters.modulus then execute hash cheat claim m tail else none

theorem admitted_connection (hash : Hash) (cheat : Bool) (claim : Nat)
    (hc : claim < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (m : Zkc.Source.LocalArithmetic.Memory) (tail : Bytes) :
    admittedExecute hash cheat claim m tail =
      some ((derived hash cheat claim).1,(derived hash cheat claim).2,
        values cheat (derived hash cheat claim).2,tail,m) := by
  simp [admittedExecute, hc, actual_interpreted_connection]

-- Every admitted output has exact canonical content and remainder, without honesty.
theorem receive_faithful (bs : Bytes) (xs : List Nat) (tail : Bytes)
    (h : receive bs = some (xs,tail)) : bs = wire xs ++ tail ∧ xs.length = 3 := by
  unfold receive at h
  cases hr : readWords 3 bs with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨vs,rest⟩
    cases hc : Zkc.Source.MessageSchema.check Zkc.Protocols.ScalarBytecode.AdaptiveProver.context (raw vs) with
    | none => simp [hr,hc] at h
    | some p =>
      have hp := Zkc.Source.MessageSchema.check_exact _ _ p hc
      simp only [hr, bind, Option.bind, hc, pure] at h
      simp only [Option.some.injEq, Prod.mk.injEq, hp, raw] at h
      rcases h with ⟨rfl,rfl⟩
      have hw := words_faithful 3 bs vs rest hr
      exact ⟨hw.1,hw.2.1⟩

end Zkc.Protocols.ScalarBytecode.Prover
