import Std

set_option autoImplicit false

namespace Zkc.Realization.ByteEncoding
abbrev Byte := Fin 256
abbrev Bytes := List Byte

def little : Nat → Nat → Bytes
  | 0, _ => []
  | n+1, v => ⟨v % 256, Nat.mod_lt _ (by decide)⟩ :: little n (v / 256)
def valueLE : Bytes → Nat
  | [] => 0
  | b::bs => b.val + 256 * valueLE bs
def be (n v : Nat) : Bytes := (little n v).reverse
def valueBE (bs : Bytes) : Nat := valueLE bs.reverse
@[simp] theorem little_length (n v : Nat) : (little n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [little, ih]
@[simp] theorem be_length (n v : Nat) : (be n v).length = n := by simp [be]
theorem little_value (n v : Nat) (h : v < 256^n) : valueLE (little n v) = v := by
  induction n generalizing v with
  | zero => simp at h; subst v; rfl
  | succ n ih =>
    have hd : v / 256 < 256^n := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa [Nat.pow_succ, Nat.mul_comm] using h
    simp only [little, valueLE, ih _ hd]
    exact Nat.mod_add_div v 256
@[simp] theorem value_be (n v : Nat) (h : v < 256^n) : valueBE (be n v) = v := by
  simpa [valueBE, be] using little_value n v h

-- Every bounded byte sequence has its exact positional representation.
theorem little_reencode (bs : Bytes) : little bs.length (valueLE bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, valueLE, little]
    have hb := b.isLt
    have hm : (b.val + 256 * valueLE bs) % 256 = b.val := by omega
    have hd : (b.val + 256 * valueLE bs) / 256 = valueLE bs := by omega
    simp only [hd, ih]
    congr 1
    apply Fin.ext
    exact hm

theorem be_reencode (bs : Bytes) : be bs.length (valueBE bs) = bs := by
  have h := little_reencode bs.reverse
  simpa [be, valueBE] using congrArg List.reverse h


def utf8 (s : String) : Bytes := s.toUTF8.toList.map (fun b => b.toFin)


end Zkc.Realization.ByteEncoding
