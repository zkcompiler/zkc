import M0.Datum

/-!
# The canonical encoding `M(v)`

`docs-next/foundation/executable-foundations.md` Section 2.1 fixes the
canonical byte encoding of one `MetaValueV0` value: a one-octet tag, then a
payload built from `u64(n)` (unsigned 64-bit big-endian) and
`F(x) = u64(length(x)) || x`. `evaluation/k1-executable-foundations/
reference_model.py` (`encode_datum`) and `evaluation/k1-executable-foundations/
oracle/CONTRACT.md` Section 2 carry the same table. This file transcribes it.

`encode` is total over `Datum`; the values on which the Foundation page
assigns no encoding are exactly those `wellFormed` refuses (an unsigned
64-bit overflow in a length, count, ordinal, or case; an invalid symbol; a
non-octet in an octet string; unsorted record ordinals). `encodeChecked`
refuses those, and additionally the four constitutional data limits, exactly
as the Python encoder refuses them with `CanonicalError`.
-/

namespace M0

/-- Big-endian octets of `n` in exactly `k` positions; `n` is taken modulo
`256 ^ k`. -/
def beOctets : Nat → Nat → List Octet
  | 0, _ => []
  | k + 1, n => beOctets k (n / 256) ++ [n % 256]

/-- `u64(n)`: unsigned 64-bit big-endian. -/
def u64 (n : Nat) : List Octet := beOctets 8 n

/-- The M0 specification-shaped magnitude. Its recursive right append is
quadratic in the number of octets and is retained only as an equivalence
reference for the M1 linear implementation. -/
def magnitudeQuadratic (n : Nat) : List Octet :=
  if n < 256 then [n] else magnitudeQuadratic (n / 256) ++ [n % 256]
termination_by n
decreasing_by omega

/-- Tail-recursive minimal-magnitude worker. Low octets are consed onto the
front of the accumulator, so the result is already big-endian and performs no
right append. -/
def magnitudeCore : Nat → Nat → List Octet → List Octet
  | 0, _, accumulated => accumulated
  | fuel + 1, n, accumulated =>
      let digit := n % 256
      let next := n / 256
      if next = 0 then digit :: accumulated
      else magnitudeCore fuel next (digit :: accumulated)

/-- Linear-list-work minimal unsigned big-endian magnitude; zero is one
octet `0x00`. Exact powers of `256` use their direct one-followed-by-zeroes
form; the general path conses each low octet onto an accumulator. -/
def magnitude (n : Nat) : List Octet :=
  let exponent := Nat.log2 n / 8
  if n = 256 ^ exponent then 1 :: List.replicate exponent 0
  else magnitudeCore (n + 1) n []

/-- `F(x) = u64(length(x)) || x`. -/
def frame (b : List Octet) : List Octet := u64 b.length ++ b

/-- The sign octet of a signed integer: `0` for nonnegative, `1` for negative. -/
def signOctet (i : Int) : Octet := if i < 0 then 1 else 0

mutual
  /-- The canonical encoding `M(v)` (Foundation Section 2.1 table). -/
  def encode : Datum → List Octet
    | .unit => [0x00]
    | .bool false => [0x01]
    | .bool true => [0x02]
    | .nat n => 0x03 :: frame (magnitude n)
    | .int i => 0x04 :: signOctet i :: frame (magnitude i.natAbs)
    | .bytes bs => 0x05 :: frame bs
    | .symbol s => 0x06 :: frame s
    | .seq xs => 0x07 :: (u64 xs.length ++ encodeSeq xs)
    | .record fs => 0x08 :: (u64 fs.length ++ encodeFields fs)
    | .variant c p => 0x09 :: (u64 c ++ frame (encode p))
  /-- `F(M(child))` for each child in order. -/
  def encodeSeq : List Datum → List Octet
    | [] => []
    | x :: xs => frame (encode x) ++ encodeSeq xs
  /-- `u64(ordinal) || F(M(value))` for each field in order. -/
  def encodeFields : List (Nat × Datum) → List Octet
    | [] => []
    | (o, x) :: fs => u64 o ++ frame (encode x) ++ encodeFields fs
end

/-- Constitutional data limits (Foundation Section 2.1). -/
def maxCanonicalBytes : Nat := 2 ^ 20
def maxCanonicalNodes : Nat := 2 ^ 14
def maxCanonicalEdges : Nat := 2 ^ 14
def maxRootZeroDepth : Nat := 384

/-- The four cumulative limits, evaluated on the value. Reaching a bound is
allowed and crossing it refuses. -/
def withinLimits (d : Datum) : Bool :=
  (encode d).length ≤ maxCanonicalBytes
    && nodes d ≤ maxCanonicalNodes
    && edges d ≤ maxCanonicalEdges
    && depth d ≤ maxRootZeroDepth

/-- The encoder the runner uses for golden comparison. After the M1 K1
byte-bound decision, both implementations admit a natural whose complete
encoding reaches the constitutional limit and refuse one that crosses it. -/
def encodeChecked (d : Datum) : Option (List Octet) :=
  if wellFormed d && withinLimits d then some (encode d) else none

/-! ## Arithmetic facts about the fixed-width and minimal magnitudes -/

/-- Read big-endian octets back as a natural number. -/
def fromBE (ds : List Octet) : Nat := ds.foldl (fun acc d => acc * 256 + d) 0

theorem fromBE_snoc (a : List Octet) (d : Octet) :
    fromBE (a ++ [d]) = fromBE a * 256 + d := by
  simp [fromBE, List.foldl_append]

theorem length_beOctets (k n : Nat) : (beOctets k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [beOctets, ih]

theorem length_u64 (n : Nat) : (u64 n).length = 8 := length_beOctets 8 n

theorem fromBE_beOctets (k n : Nat) : fromBE (beOctets k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [beOctets, fromBE, Nat.mod_one]
  | succ k ih =>
    rw [beOctets, fromBE_snoc, ih, Nat.pow_succ', Nat.mod_mul]
    omega

theorem fromBE_u64 (n : Nat) (h : n < 2 ^ 64) : fromBE (u64 n) = n := by
  have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [u64, fromBE_beOctets, this, Nat.mod_eq_of_lt h]

theorem magnitudeCore_eq_quadratic (fuel n : Nat) (accumulated : List Octet)
    (enough : n < fuel) :
    magnitudeCore fuel n accumulated = magnitudeQuadratic n ++ accumulated := by
  induction fuel generalizing n accumulated with
  | zero => omega
  | succ fuel ih =>
      rw [magnitudeCore]
      by_cases nextZero : n / 256 = 0
      · rw [if_pos nextZero]
        have small : n < 256 := (Nat.div_eq_zero_iff).mp nextZero |>.resolve_left (by decide)
        rw [magnitudeQuadratic]
        simp [small]
      · rw [if_neg nextZero]
        have notSmall : ¬ n < 256 := by
          intro small
          exact nextZero (Nat.div_eq_zero_iff.mpr (.inr small))
        rw [magnitudeQuadratic]
        simp only [notSmall, ↓reduceIte]
        rw [ih (n / 256) (n % 256 :: accumulated) (by omega)]
        simp [List.append_assoc]

theorem magnitudeQuadratic_pow_256 (exponent : Nat) :
    magnitudeQuadratic (256 ^ exponent) = 1 :: List.replicate exponent 0 := by
  induction exponent with
  | zero => simp [magnitudeQuadratic]
  | succ exponent ih =>
      rw [Nat.pow_succ]
      have large : ¬ 256 ^ exponent * 256 < 256 := by
        have positive : 0 < 256 ^ exponent := Nat.pow_pos (by decide)
        omega
      rw [magnitudeQuadratic]
      simp only [large, ↓reduceIte]
      rw [Nat.mul_comm, Nat.mul_div_right _ (by decide), Nat.mul_mod_right, ih]
      rw [List.replicate_succ']
      rfl

/-- The M1 accumulator implementation computes exactly the M0 reference
magnitude for every natural. -/
theorem magnitude_eq_quadratic (n : Nat) : magnitude n = magnitudeQuadratic n := by
  simp only [magnitude]
  by_cases power : n = 256 ^ (Nat.log2 n / 8)
  · rw [if_pos power]
    calc
      1 :: List.replicate (Nat.log2 n / 8) 0 =
          magnitudeQuadratic (256 ^ (Nat.log2 n / 8)) :=
        (magnitudeQuadratic_pow_256 _).symm
      _ = magnitudeQuadratic n := congrArg magnitudeQuadratic power.symm
  · rw [if_neg power]
    simpa using magnitudeCore_eq_quadratic (n + 1) n [] (by omega)

theorem magnitude_eq_of_lt (n : Nat) (h : n < 256) : magnitude n = [n] := by
  rw [magnitude_eq_quadratic, magnitudeQuadratic]; simp [h]

theorem magnitude_eq_of_ge (n : Nat) (h : ¬ n < 256) :
    magnitude n = magnitude (n / 256) ++ [n % 256] := by
  rw [magnitude_eq_quadratic, magnitudeQuadratic]
  simp only [h, ↓reduceIte]
  rw [← magnitude_eq_quadratic]

theorem fromBE_magnitude (n : Nat) : fromBE (magnitude n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 256
    · rw [magnitude_eq_of_lt n h]; simp [fromBE]
    · rw [magnitude_eq_of_ge n h, fromBE_snoc, ih (n / 256) (by omega)]
      omega

theorem magnitude_ne_nil (n : Nat) : magnitude n ≠ [] := by
  by_cases h : n < 256
  · rw [magnitude_eq_of_lt n h]; simp
  · rw [magnitude_eq_of_ge n h]; simp

/-- Above `255`, a minimal magnitude starts with a nonzero octet. -/
theorem magnitude_head_ne_zero (n : Nat) (h : ¬ n < 256) :
    ∃ (d : Nat) (rest : List Nat), magnitude n = d :: rest ∧ d ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h2 : n / 256 < 256
    · refine ⟨n / 256, [n % 256], ?_, by omega⟩
      rw [magnitude_eq_of_ge n h, magnitude_eq_of_lt _ h2]
      rfl
    · obtain ⟨d, rest, hm, hd⟩ := ih (n / 256) (by omega) h2
      refine ⟨d, rest ++ [n % 256], ?_, hd⟩
      rw [magnitude_eq_of_ge n h, hm]
      rfl

end M0
