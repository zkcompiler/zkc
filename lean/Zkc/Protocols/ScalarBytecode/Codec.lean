import Zkc.Protocols.ScalarBytecode.Parameters
import Zkc.Realization.ByteEncoding

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Codec
open Zkc.Realization.ByteEncoding
def enc (v : Nat) : Bytes := be 8 v
-- Exact content check makes the reference recognizer fail closed. It adds no bytes.
def readScalar (bs : Bytes) : Option (Nat × Bytes) :=
  let front := bs.take 8
  let v := valueBE front
  if front.length = 8 ∧ v < Zkc.Protocols.ScalarBytecode.Parameters.modulus ∧ enc v = front then
    some (v, bs.drop 8)
  else none

-- The extra equality guard is provably redundant: exactly width and canonicality.
theorem readScalar_implementation (bs : Bytes) :
    readScalar bs =
      if (bs.take 8).length = 8 ∧ valueBE (bs.take 8) < Zkc.Protocols.ScalarBytecode.Parameters.modulus then
        some (valueBE (bs.take 8), bs.drop 8) else none := by
  unfold readScalar
  dsimp only
  by_cases h : (bs.take 8).length = 8
  · have he : enc (valueBE (bs.take 8)) = bs.take 8 := by
      simpa [enc, h] using be_reencode (bs.take 8)
    simp [h, he]
  · simp only [h, false_and, ↓reduceIte]

theorem scalar_complete (v : Nat) (h : v < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (tail : Bytes) :
    readScalar (enc v ++ tail) = some (v,tail) := by
  have hv : v < 256^8 := Nat.lt_trans h (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
  simp [readScalar, enc, value_be 8 v hv, h]

theorem scalar_faithful (bs : Bytes) (v : Nat) (tail : Bytes)
    (h : readScalar bs = some (v,tail)) :
    v < Zkc.Protocols.ScalarBytecode.Parameters.modulus ∧ bs = enc v ++ tail ∧ tail = bs.drop 8 := by
  simp only [readScalar] at h
  split at h
  next hg =>
    have hp := Option.some.inj h
    have hv := congrArg Prod.fst hp
    have ht := congrArg Prod.snd hp
    simp only at hv ht
    refine ⟨hv ▸ hg.2.1, ?_, ht.symm⟩
    rw [← hv, ← ht, hg.2.2]
    exact (List.take_append_drop 8 bs).symm
  next => simp at h

def wire (xs : List Nat) : Bytes := xs.flatMap enc
def readWords : Nat → Bytes → Option (List Nat × Bytes)
  | 0, bs => some ([],bs)
  | n+1, bs => do
    let (v,rest) ← readScalar bs
    let (vs,tail) ← readWords n rest
    return (v::vs,tail)

theorem words_complete (xs : List Nat) (h : ∀ v ∈ xs, v < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (tail : Bytes) :
    readWords xs.length (wire xs ++ tail) = some (xs,tail) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    have hv := h v (by simp)
    have hx : ∀ w ∈ xs, w < Zkc.Protocols.ScalarBytecode.Parameters.modulus := fun w hw => h w (by simp [hw])
    change (do
      let (a,rest) ← readScalar (enc v ++ (wire xs ++ tail))
      let (vs,remaining) ← readWords xs.length rest
      pure (a::vs,remaining)) = some (v::xs,tail)
    rw [scalar_complete v hv]
    simp [bind, pure, ih hx]

theorem words_faithful (n : Nat) (bs : Bytes) (xs : List Nat) (tail : Bytes)
    (h : readWords n bs = some (xs,tail)) :
    bs = wire xs ++ tail ∧ xs.length = n ∧ ∀ v ∈ xs, v < Zkc.Protocols.ScalarBytecode.Parameters.modulus := by
  induction n generalizing bs xs with
  | zero =>
    simp only [readWords, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simp [wire]
  | succ n ih =>
    cases hs : readScalar bs with
    | none => simp [readWords, hs] at h
    | some pair =>
      rcases pair with ⟨v,rest⟩
      cases hw : readWords n rest with
      | none => simp [readWords, hs, hw] at h
      | some pair =>
        rcases pair with ⟨vs,remainder⟩
        simp [readWords, hs, hw] at h
        rcases h with ⟨rfl,rfl⟩
        have a := scalar_faithful bs v rest hs
        have b := ih rest vs hw
        refine ⟨?_, by simp [b.2.1], ?_⟩
        · simp [a.2.1, b.1, wire, List.append_assoc]
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact a.1
          · exact b.2.2 w hw

end Zkc.Protocols.ScalarBytecode.Codec
