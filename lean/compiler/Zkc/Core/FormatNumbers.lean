module

public import Zkc.Core.Format

@[expose] public section

/-! The formats of numbers.

- `Format.number bound width`: a number below a bound in a fixed number of bytes, least
  significant first. Its domain is the numbers below the bound that the width holds, so the
  writer never drops a digit of a value of the domain; the reader refuses a number not below
  the bound.
- `Format.below bound`: a number below a bound in the fewest bytes that hold every such number,
  the least `k` with `bound ≤ 256 ^ k` (`byteWidth`). A bound of at most 1 takes no bytes, a
  bound of at most 256 one.
- `Format.natural`: any natural, of variable length: groups of seven bits, least significant
  first, the high bit of a byte saying that another group follows, and no final group of zero
  except for the number 0. This is unsigned LEB128 in its shortest form; the reader refuses
  every other form.
-/

set_option autoImplicit false

namespace Zkc.Core

/-! ## A number in a fixed width -/

/-- The bytes of a number in a width, least significant first: its digits in base 256 below the
width. -/
def littleEndian : Nat → Nat → Bytes
  | 0, _ => []
  | width + 1, value => Byte.ofNat value :: littleEndian width (value / 256)

/-- The number of bytes, least significant first. -/
def ofLittleEndian : Bytes → Nat
  | [] => 0
  | byte :: rest => byte.val + 256 * ofLittleEndian rest

theorem littleEndian_length : ∀ (width value : Nat), (littleEndian width value).length = width
  | 0, _ => rfl
  | width + 1, value => by simp [littleEndian, littleEndian_length width]

/-- The number of the bytes of a number in a width is the number modulo `256 ^ width`. -/
theorem ofLittleEndian_littleEndian : ∀ (width value : Nat),
    ofLittleEndian (littleEndian width value) = value % 256 ^ width
  | 0, value => by simp [littleEndian, ofLittleEndian, Nat.mod_one]
  | width + 1, value => by
    simp only [littleEndian, ofLittleEndian, Byte.val_ofNat,
      ofLittleEndian_littleEndian width (value / 256)]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ width) 256, Nat.mod_mul]

/-- The bytes of the number of bytes, in their width, are the bytes. -/
theorem littleEndian_ofLittleEndian : ∀ (bytes : Bytes),
    littleEndian bytes.length (ofLittleEndian bytes) = bytes
  | [] => rfl
  | byte :: rest => by
    have below := byte.isLt
    simp only [List.length_cons, littleEndian, ofLittleEndian]
    have first : Byte.ofNat (byte.val + 256 * ofLittleEndian rest) = byte := by
      apply Fin.ext
      rw [Byte.val_ofNat]
      omega
    have later : (byte.val + 256 * ofLittleEndian rest) / 256 = ofLittleEndian rest := by omega
    rw [first, later, littleEndian_ofLittleEndian rest]

/-- The number of bytes is below `256` to their number. -/
theorem ofLittleEndian_lt : ∀ (bytes : Bytes), ofLittleEndian bytes < 256 ^ bytes.length
  | [] => by simp [ofLittleEndian]
  | byte :: rest => by
    have below := byte.isLt
    have later := ofLittleEndian_lt rest
    simp only [ofLittleEndian, List.length_cons, Nat.pow_succ]
    omega

namespace Format

/-- A number below a bound in a fixed number of bytes, least significant first. The domain is
the numbers below the bound that the width holds. The reader looks at no more bytes than the
width. -/
def number (bound width : Nat) : Format Nat where
  domain value := decide (value < bound) && decide (value < 256 ^ width)
  admits value := decide (value < bound) && decide (value < 256 ^ width)
  write value := littleEndian width value
  read bytes :=
    if (bytes.take width).length < width then none
    else if ofLittleEndian (bytes.take width) < bound then
      some (ofLittleEndian (bytes.take width), bytes.drop width)
    else none
  width := some width
  readWithin limit bytes :=
    Reading.ofOption limit
      (if (bytes.take width).length < width then none
      else if ofLittleEndian (bytes.take width) < bound then
        some (ofLittleEndian (bytes.take width), bytes.drop width)
      else none)

theorem number_lawful (bound width : Nat) : (number bound width).Lawful where
  round_trip := by
    intro value inDomain rest
    simp only [number, Bool.and_eq_true, decide_eq_true_eq] at inDomain ⊢
    have length := littleEndian_length width value
    have taken : (littleEndian width value ++ rest).take width = littleEndian width value := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have dropped : (littleEndian width value ++ rest).drop width = rest := by
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append]
    have read : ofLittleEndian (littleEndian width value) = value := by
      rw [ofLittleEndian_littleEndian, Nat.mod_eq_of_lt inDomain.2]
    have long : ¬ (littleEndian width value).length < width := by omega
    simp only [taken, dropped, read, long, inDomain.1, ↓reduceIte]
  canonical := by
    intro bytes value rest read
    simp only [number] at read ⊢
    by_cases short : (bytes.take width).length < width
    · simp only [short, ↓reduceIte, reduceCtorEq] at read
    · simp only [short, ↓reduceIte] at read
      by_cases below : ofLittleEndian (bytes.take width) < bound
      · simp only [below, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        have length : (bytes.take width).length = width := by
          have most := List.length_take_le width bytes
          omega
        have holds := ofLittleEndian_lt (bytes.take width)
        rw [length] at holds
        refine ⟨by simp [below, holds], ?_⟩
        have written := littleEndian_ofLittleEndian (bytes.take width)
        rw [length] at written
        rw [written, List.take_append_drop]
      · simp [below] at read
  width_written := by
    intro stated same value _
    simp only [number, Option.some.injEq] at same ⊢
    rw [littleEndian_length, same]
  admits_domain := fun _ inDomain => inDomain

theorem number_agrees (bound width : Nat) : (number bound width).Agrees := by
  intro limit bytes result answered
  simp only [number, Reading.answer_ofOption, Option.some.injEq] at answered ⊢
  exact answered

end Format

/-! ## A number below a bound in the fewest bytes -/

/-- The fewest bytes that hold every number below a bound: the least `k` with
`bound ≤ 256 ^ k`. -/
def byteWidth (bound : Nat) : Nat :=
  if bound ≤ 1 then 0 else ((bound - 1).log2 + 8) / 8

/-- The width of a bound holds every number below it. -/
theorem le_pow_byteWidth (bound : Nat) : bound ≤ 256 ^ byteWidth bound := by
  unfold byteWidth
  by_cases small : bound ≤ 1
  · simp [small]
  · simp only [small, ↓reduceIte]
    have below := Nat.lt_log2_self (n := bound - 1)
    have grows : 2 ^ ((bound - 1).log2 + 1) ≤ 2 ^ (8 * (((bound - 1).log2 + 8) / 8)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have same : (256 : Nat) ^ (((bound - 1).log2 + 8) / 8) =
        2 ^ (8 * (((bound - 1).log2 + 8) / 8)) := by
      rw [Nat.pow_mul]
    omega

/-- The width of a bound is the least that holds every number below it. -/
theorem byteWidth_le {bound width : Nat} (holds : bound ≤ 256 ^ width) :
    byteWidth bound ≤ width := by
  unfold byteWidth
  by_cases small : bound ≤ 1
  · simp [small]
  · simp only [small, ↓reduceIte]
    have same : (256 : Nat) ^ width = 2 ^ (8 * width) := by rw [Nat.pow_mul]
    have below : (bound - 1).log2 < 8 * width :=
      (Nat.log2_lt (by omega)).mpr (by omega)
    omega

namespace Format

/-- A number below a bound in the fewest bytes that hold every such number, least significant
first. -/
def below (bound : Nat) : Format Nat := number bound (byteWidth bound)

theorem below_lawful (bound : Nat) : (below bound).Lawful := number_lawful bound (byteWidth bound)

theorem below_agrees (bound : Nat) : (below bound).Agrees := number_agrees bound (byteWidth bound)

/-- The domain of a number below a bound is the numbers below the bound. -/
theorem below_domain (bound value : Nat) : (below bound).domain value = decide (value < bound) := by
  simp only [below, number]
  have holds := le_pow_byteWidth bound
  by_cases small : value < bound
  · have fits : value < 256 ^ byteWidth bound := by omega
    simp [small, fits]
  · simp [small]

end Format

/-! ## A natural of variable length -/

/-- The bytes of a natural: its groups of seven bits, least significant first, each but the
last with its high bit set. The last group of a number other than 0 is not zero. -/
def writeNatural (value : Nat) : Bytes :=
  if value < 128 then [Byte.ofNat value]
  else Byte.ofNat (value % 128 + 128) :: writeNatural (value / 128)
termination_by value
decreasing_by omega

/-- The groups of a natural at the front of bytes, after the groups read so far: `scale` is the
weight of the next group, `total` the number of the groups so far, and `first` whether the next
group is the first. A last group of zero after another group is refused. The recursion keeps
the number so far in an argument, so that a long number does not grow the stack. -/
def readGroups : Bytes → (first : Bool) → (scale total : Nat) → Option (Nat × Bytes)
  | [], _, _, _ => none
  | byte :: rest, first, scale, total =>
    if byte.val < 128 then
      if byte.val = 0 && !first then none else some (total + scale * byte.val, rest)
    else readGroups rest false (scale * 128) (total + scale * (byte.val - 128))

/-- The natural at the front of bytes and the bytes after it, when they start with the bytes of
a natural. -/
def readNatural (bytes : Bytes) : Option (Nat × Bytes) := readGroups bytes true 1 0

/-- The groups that the writer wrote are read as the number, after the groups read so far, when
the number is not zero or its group is the first. -/
theorem readGroups_written (value : Nat) : ∀ (first : Bool) (scale total : Nat) (rest : Bytes),
    (first = true ∨ value ≠ 0) →
      readGroups (writeNatural value ++ rest) first scale total = some (total + scale * value, rest) := by
  induction value using Nat.strongRecOn with
  | _ value hypothesis =>
    intro first scale total rest allowed
    rw [writeNatural]
    by_cases small : value < 128
    · have byteVal : (Byte.ofNat value).val = value := by
        rw [Byte.val_ofNat]
        omega
      simp only [small, ↓reduceIte, List.cons_append, List.nil_append, readGroups, byteVal]
      rcases allowed with isFirst | nonzero
      · simp [isFirst]
      · simp [nonzero]
    · have byteVal : (Byte.ofNat (value % 128 + 128)).val = value % 128 + 128 := by
        rw [Byte.val_ofNat]
        omega
      have large : ¬ value % 128 + 128 < 128 := by omega
      simp only [small, ↓reduceIte, List.cons_append, readGroups, byteVal, large]
      rw [hypothesis (value / 128) (by omega) false (scale * 128)
        (total + scale * (value % 128 + 128 - 128)) rest (.inr (by omega))]
      have split : scale * (value % 128 + 128 - 128) + scale * 128 * (value / 128) = scale * value := by
        rw [Nat.add_sub_cancel, Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]
      rw [Nat.add_assoc, split]

/-- What is read as groups is what the writer writes for a number, which is not zero unless its
group is the first. -/
theorem readGroups_canonical : ∀ (bytes : Bytes) (first : Bool) (scale total : Nat) (found : Nat)
    (rest : Bytes), readGroups bytes first scale total = some (found, rest) →
      ∃ value, found = total + scale * value ∧ bytes = writeNatural value ++ rest ∧
        (first = true ∨ value ≠ 0)
  | [], _, _, _, _, _, read => by simp [readGroups] at read
  | byte :: later, first, scale, total, found, rest, read => by
    have below := byte.isLt
    simp only [readGroups] at read
    by_cases small : byte.val < 128
    · simp only [small, ↓reduceIte] at read
      by_cases refused : byte.val = 0 ∧ first = false
      · simp [refused.1, refused.2] at read
      · have kept : (decide (byte.val = 0) && !first) = false := by
          cases first <;> simp_all
        simp only [kept, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        refine ⟨byte.val, rfl, ?_, ?_⟩
        · rw [writeNatural]
          simp [small, Byte.ofNat_val]
        · cases first with
          | true => exact .inl rfl
          | false => exact .inr fun zero => refused ⟨zero, rfl⟩
    · simp only [small, ↓reduceIte] at read
      obtain ⟨high, rfl, rfl, nonzero⟩ := readGroups_canonical later false _ _ _ _ read
      have highNonzero : high ≠ 0 := by
        rcases nonzero with impossible | nonzero
        · cases impossible
        · exact nonzero
      refine ⟨byte.val - 128 + 128 * high, ?_, ?_, .inr (by omega)⟩
      · rw [Nat.add_assoc, Nat.mul_add, Nat.mul_assoc]
      · have large : ¬ byte.val - 128 + 128 * high < 128 := by omega
        have low : (byte.val - 128 + 128 * high) % 128 + 128 = byte.val := by omega
        have rest : (byte.val - 128 + 128 * high) / 128 = high := by omega
        have unfolded : writeNatural (byte.val - 128 + 128 * high) =
            Byte.ofNat ((byte.val - 128 + 128 * high) % 128 + 128) ::
              writeNatural ((byte.val - 128 + 128 * high) / 128) := by
          rw [writeNatural]
          simp only [large, ↓reduceIte]
        rw [unfolded, low, rest, Byte.ofNat_val, List.cons_append]

namespace Format

/-- A natural of variable length: unsigned LEB128 in its shortest form. Every natural is of the
domain. -/
def natural : Format Nat where
  domain _ := true
  admits _ := true
  write := writeNatural
  read := readNatural
  width := none
  readWithin limit bytes := Reading.ofOption limit (readNatural bytes)

theorem natural_lawful : natural.Lawful where
  round_trip := by
    intro value _ rest
    simp only [natural, readNatural]
    rw [readGroups_written value true 1 0 rest (.inl rfl)]
    simp
  canonical := by
    intro bytes value rest read
    simp only [natural, readNatural] at read ⊢
    obtain ⟨found, rfl, rfl, _⟩ := readGroups_canonical bytes true 1 0 value rest read
    simp
  width_written := by
    intro width stated
    simp [natural] at stated
  admits_domain := fun _ _ => rfl

theorem natural_agrees : natural.Agrees := by
  intro limit bytes result answered
  simp only [natural, Reading.answer_ofOption, Option.some.injEq] at answered ⊢
  exact answered

end Format

end Zkc.Core
