import M0.Decode
import M0.PCGraph

/-!
# Mechanically checked statements

The primary statement is that the strict parser inverts the canonical
encoder on every well-formed datum: `parse_encode`. Its corollaries are
`decode_encode` (the executable decoder inverts the executable encoder within
the constitutional limits), `encode_injective` (two well-formed data with the
same canonical bytes are equal), and `encode_prefix_free` (no canonical
encoding is a proper prefix of another; a decoder "consumes exactly one
value", Foundation Section 2.1). The secondary statements are the lattice
laws of `Join` from `docs-next/pir/interactive-core.md` Section 11.

These statements are about the Lean transcriptions in this package and about
nothing else. They do not establish that the transcriptions agree with the
Foundation page, the Python model, or any implementation; the package runner
measures that agreement on exact vectors only.
-/

namespace M0

/-! ## Reading back what the encoder wrote -/

theorem fitsU64_eq_true (n : Nat) : fitsU64 n = true ↔ n < 2 ^ 64 := by
  simp [fitsU64]

theorem readOctets_append (a r : List Octet) : readOctets a.length (a ++ r) = some (a, r) := by
  simp [readOctets]

theorem readOctets_append_of_eq (k : Nat) (a r : List Octet) (h : k = a.length) :
    readOctets k (a ++ r) = some (a, r) := by
  subst h; exact readOctets_append a r

theorem readU64_append (n : Nat) (r : List Octet) (h : n < 2 ^ 64) :
    readU64 (u64 n ++ r) = some (n, r) := by
  unfold readU64
  simp only [readOctets_append_of_eq 8 (u64 n) r (length_u64 n).symm, fromBE_u64 n h]

theorem readFrame_append (b r : List Octet) (h : b.length < 2 ^ 64) :
    readFrame (frame b ++ r) = some (b, r) := by
  unfold readFrame frame
  rw [List.append_assoc]
  simp only [readU64_append _ _ h, readOctets_append]

theorem minimalMagnitude_magnitude (n : Nat) : minimalMagnitude (magnitude n) = true := by
  by_cases h : n < 256
  · rw [magnitude_eq_of_lt n h]; rfl
  · obtain ⟨d, rest, hm, hd⟩ := magnitude_head_ne_zero n h
    rw [hm]
    cases rest with
    | nil => rfl
    | cons e tail => simp [minimalMagnitude, hd]

theorem magnitudeValue_magnitude (n : Nat) : magnitudeValue (magnitude n) = some n := by
  unfold magnitudeValue
  rw [minimalMagnitude_magnitude, fromBE_magnitude]
  rfl

theorem length_frame (b : List Octet) : (frame b).length = 8 + b.length := by
  simp [frame, length_u64]

/-! ## The parser inverts the encoder -/

mutual
  theorem parse_encode : ∀ (d : Datum) (fuel : Nat) (r : List Octet),
      wellFormed d = true → (encode d).length < 2 ^ 64 → depth d < fuel →
      parse fuel (encode d ++ r) = some (d, r)
    | _, 0, _, _, _, hdepth => absurd hdepth (Nat.not_lt_zero _)
    | .unit, fuel + 1, r, _, _, _ => by simp [encode, parse]
    | .bool false, fuel + 1, r, _, _, _ => by simp [encode, parse]
    | .bool true, fuel + 1, r, _, _, _ => by simp [encode, parse]
    | .nat n, fuel + 1, r, _, hlen, _ => by
      have hm : (magnitude n).length < 2 ^ 64 := by
        simp only [encode, List.length_cons, length_frame] at hlen; omega
      simp only [encode, parse, List.cons_append]
      simp only [readFrame_append _ _ hm, magnitudeValue_magnitude]
    | .int i, fuel + 1, r, _, hlen, _ => by
      have hm : (magnitude i.natAbs).length < 2 ^ 64 := by
        simp only [encode, List.length_cons, length_frame] at hlen; omega
      simp only [encode, parse, List.cons_append]
      simp only [readFrame_append _ _ hm, magnitudeValue_magnitude]
      by_cases hneg : i < 0
      · have hnz : i.natAbs ≠ 0 := by omega
        have hval : -(i.natAbs : Int) = i := by omega
        simp [signOctet, hneg, hnz, hval]
      · have hval : (i.natAbs : Int) = i := by omega
        simp [signOctet, hneg, hval]
    | .bytes bs, fuel + 1, r, hwf, _, _ => by
      have hb : bs.length < 2 ^ 64 := by
        simp only [wellFormed, Bool.and_eq_true, fitsU64_eq_true] at hwf; exact hwf.2
      simp only [encode, parse, List.cons_append]
      simp only [readFrame_append _ _ hb]
    | .symbol s, fuel + 1, r, hwf, _, _ => by
      have hs : s.length < 2 ^ 64 := by
        simp only [wellFormed, Bool.and_eq_true, fitsU64_eq_true] at hwf; exact hwf.2
      have hv : validSymbol s = true := by
        simp only [wellFormed, Bool.and_eq_true] at hwf
        simp [validSymbol, hwf.1.1, hwf.1.2]
      simp only [encode, parse, List.cons_append]
      simp [readFrame_append _ _ hs, hv]
    | .seq xs, fuel + 1, r, hwf, hlen, hdepth => by
      simp only [wellFormed, Bool.and_eq_true, fitsU64_eq_true] at hwf
      have hl : (encodeSeq xs).length < 2 ^ 64 := by
        simp only [encode, List.length_cons, List.length_append, length_u64] at hlen; omega
      have hd : depthSeq xs ≤ fuel := by
        simp only [depth] at hdepth; omega
      simp only [encode, parse, List.cons_append, List.append_assoc]
      simp only [readU64_append _ _ hwf.1, parseFramed_encodeSeq xs fuel r hwf.2 hl hd]
    | .record fs, fuel + 1, r, hwf, hlen, hdepth => by
      simp only [wellFormed, Bool.and_eq_true, fitsU64_eq_true] at hwf
      have hl : (encodeFields fs).length < 2 ^ 64 := by
        simp only [encode, List.length_cons, List.length_append, length_u64] at hlen; omega
      have hd : depthFields fs ≤ fuel := by
        simp only [depth] at hdepth; omega
      simp only [encode, parse, List.cons_append, List.append_assoc]
      simp only [readU64_append _ _ hwf.1.1,
        parseFields_encodeFields fs fuel none r hwf.2 hwf.1.2 (fun _ _ _ => rfl) hl hd]
    | .variant c p, fuel + 1, r, hwf, hlen, hdepth => by
      simp only [wellFormed, Bool.and_eq_true, fitsU64_eq_true] at hwf
      have hl : (encode p).length < 2 ^ 64 := by
        simp only [encode, List.length_cons, List.length_append, length_u64, length_frame] at hlen
        omega
      have hd : depth p < fuel := by
        simp only [depth] at hdepth; omega
      have hp := parse_encode p fuel [] hwf.2 hl hd
      rw [List.append_nil] at hp
      simp only [encode, parse, List.cons_append, List.append_assoc]
      simp [readU64_append _ _ hwf.1, readFrame_append _ _ hl, hp]

  theorem parseFramed_encodeSeq : ∀ (xs : List Datum) (fuel : Nat) (r : List Octet),
      wellFormedSeq xs = true → (encodeSeq xs).length < 2 ^ 64 → depthSeq xs ≤ fuel →
      parseFramed (parse fuel) xs.length (encodeSeq xs ++ r) = some (xs, r)
    | [], fuel, r, _, _, _ => by simp [encodeSeq, parseFramed]
    | x :: xs, fuel, r, hwf, hlen, hdepth => by
      simp only [wellFormedSeq, Bool.and_eq_true] at hwf
      have hx : (encode x).length < 2 ^ 64 := by
        simp only [encodeSeq, List.length_append, length_frame] at hlen; omega
      have hxs : (encodeSeq xs).length < 2 ^ 64 := by
        simp only [encodeSeq, List.length_append, length_frame] at hlen; omega
      have hdx : depth x < fuel := by
        simp only [depthSeq] at hdepth; omega
      have hdxs : depthSeq xs ≤ fuel := by
        simp only [depthSeq] at hdepth; omega
      have hp := parse_encode x fuel [] hwf.1 hx hdx
      rw [List.append_nil] at hp
      simp only [encodeSeq, List.length_cons, parseFramed, List.append_assoc]
      simp only [readFrame_append _ _ hx, hp, List.isEmpty_nil, ite_true,
        parseFramed_encodeSeq xs fuel r hwf.2 hxs hdxs]

  theorem parseFields_encodeFields : ∀ (fs : List (Nat × Datum)) (fuel : Nat)
      (previous : Option Nat) (r : List Octet),
      wellFormedFields fs = true → ordinalsIncreasing fs = true →
      (∀ o x, fs.head? = some (o, x) → previous.all (· < o) = true) →
      (encodeFields fs).length < 2 ^ 64 → depthFields fs ≤ fuel →
      parseFields (parse fuel) fs.length previous (encodeFields fs ++ r) = some (fs, r)
    | [], fuel, previous, r, _, _, _, _, _ => by simp [encodeFields, parseFields]
    | (o, x) :: fs, fuel, previous, r, hwf, hinc, hprev, hlen, hdepth => by
      simp only [wellFormedFields, Bool.and_eq_true, fitsU64_eq_true] at hwf
      have hx : (encode x).length < 2 ^ 64 := by
        simp only [encodeFields, List.length_append, length_frame, length_u64] at hlen; omega
      have hfs : (encodeFields fs).length < 2 ^ 64 := by
        simp only [encodeFields, List.length_append, length_frame, length_u64] at hlen; omega
      have hdx : depth x < fuel := by
        simp only [depthFields] at hdepth; omega
      have hdfs : depthFields fs ≤ fuel := by
        simp only [depthFields] at hdepth; omega
      have hp := parse_encode x fuel [] hwf.1.2 hx hdx
      rw [List.append_nil] at hp
      have hhead : previous.all (· < o) = true := hprev o x rfl
      have hinc' : ordinalsIncreasing fs = true ∧
          ∀ o₂ y, fs.head? = some (o₂, y) → (some o).all (· < o₂) = true := by
        cases fs with
        | nil => exact ⟨rfl, fun _ _ h => by simp at h⟩
        | cons f rest =>
          obtain ⟨o₂, y⟩ := f
          simp only [ordinalsIncreasing, Bool.and_eq_true, decide_eq_true_eq] at hinc
          refine ⟨hinc.2, fun o₃ z h => ?_⟩
          simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [Option.all, hinc.1]
      simp only [encodeFields, List.length_cons, parseFields, List.append_assoc]
      simp only [readU64_append _ _ hwf.1.1]
      rw [if_pos hhead]
      simp only [readFrame_append _ _ hx, hp, List.isEmpty_nil, ite_true,
        parseFields_encodeFields fs fuel (some o) r hwf.2 hinc'.1 hinc'.2 hfs hdfs]
end

/-! ## Corollaries about the executable decoder and the encoding -/

theorem withinLimits_bytes {d : Datum} (h : withinLimits d = true) :
    (encode d).length ≤ maxCanonicalBytes := by
  simp only [withinLimits, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1

theorem withinLimits_depth {d : Datum} (h : withinLimits d = true) :
    depth d ≤ maxRootZeroDepth := by
  simp only [withinLimits, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

/-- The strict decoder inverts the checked encoder. -/
theorem decode_encode (d : Datum) (hwf : wellFormed d = true) (hlim : withinLimits d = true) :
    decode (encode d) = some d := by
  have hbytes := withinLimits_bytes hlim
  have hdepth := withinLimits_depth hlim
  have hp := parse_encode d (maxRootZeroDepth + 1) [] hwf
    (by unfold maxCanonicalBytes at hbytes; omega) (by omega)
  rw [List.append_nil] at hp
  unfold decode
  rw [if_pos hbytes, hp]
  simp [hlim]

/-- Every checked encoding decodes back to its datum. -/
theorem decode_encodeChecked (d : Datum) (b : List Octet) (h : encodeChecked d = some b) :
    decode b = some d := by
  unfold encodeChecked at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    exact decode_encode d hc.1 hc.2
  · cases h

/-- Two well-formed data with the same canonical bytes are the same datum. -/
theorem encode_injective (d₁ d₂ : Datum)
    (h₁ : wellFormed d₁ = true) (h₂ : wellFormed d₂ = true)
    (l₁ : (encode d₁).length < 2 ^ 64) (l₂ : (encode d₂).length < 2 ^ 64)
    (heq : encode d₁ = encode d₂) : d₁ = d₂ := by
  have p₁ := parse_encode d₁ (max (depth d₁) (depth d₂) + 1) [] h₁ l₁ (by omega)
  have p₂ := parse_encode d₂ (max (depth d₁) (depth d₂) + 1) [] h₂ l₂ (by omega)
  rw [heq, p₂] at p₁
  exact ((Prod.mk.inj (Option.some.inj p₁)).1).symm

/-- No canonical encoding is a proper prefix of another: a decoder that
consumes exactly one value cannot be misled by what follows. -/
theorem encode_prefix_free (d₁ d₂ : Datum)
    (h₁ : wellFormed d₁ = true) (h₂ : wellFormed d₂ = true)
    (l₁ : (encode d₁).length < 2 ^ 64) (l₂ : (encode d₂).length < 2 ^ 64)
    (r : List Octet) (heq : encode d₁ ++ r = encode d₂) : d₁ = d₂ ∧ r = [] := by
  have p₁ := parse_encode d₁ (max (depth d₁) (depth d₂) + 1) r h₁ l₁ (by omega)
  have p₂ := parse_encode d₂ (max (depth d₁) (depth d₂) + 1) [] h₂ l₂ (by omega)
  rw [List.append_nil, ← heq, p₁] at p₂
  have := Prod.mk.inj (Option.some.inj p₂)
  exact ⟨this.1, this.2⟩

/-- The checked encoder used for the golden comparison is injective. -/
theorem encodeChecked_injective (d₁ d₂ : Datum) (b : List Octet)
    (h₁ : encodeChecked d₁ = some b) (h₂ : encodeChecked d₂ = some b) : d₁ = d₂ := by
  have := decode_encodeChecked d₁ b h₁
  rw [decode_encodeChecked d₂ b h₂] at this
  exact (Option.some.inj this).symm

/-! ## Lattice laws of `Join` (Section 11) -/

theorem Join_nil : Join [] = .staticPublic := rfl

/-- `Join` over a list is the binary join folded from the right: the prose
definition by membership and the lattice operation agree. -/
theorem Join_cons (x : PCClass) (xs : List PCClass) : Join (x :: xs) = x.join (Join xs) := by
  unfold PCClass.join
  cases x <;> unfold Join <;> simp only [List.contains_cons, List.contains_nil, Bool.or_false,
      beq_self_eq_true, Bool.true_or, ite_true] <;>
    (repeat' split) <;> simp_all [beq_iff_eq]

theorem Join_eq_foldr (xs : List PCClass) : Join xs = xs.foldr PCClass.join .staticPublic := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [Join_cons, ih, List.foldr_cons]

namespace PCClass

theorem join_assoc (a b c : PCClass) : (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem join_comm (a b : PCClass) : a.join b = b.join a := by
  cases a <;> cases b <;> decide

theorem join_idem (a : PCClass) : a.join a = a := by
  cases a <;> decide

theorem join_invalid_left (a : PCClass) : PCClass.invalid.join a = .invalid := by
  cases a <;> decide

theorem join_invalid_right (a : PCClass) : a.join .invalid = .invalid := by
  cases a <;> decide

theorem join_staticPublic_left (a : PCClass) : PCClass.staticPublic.join a = a := by
  cases a <;> decide

end PCClass

theorem Publish_idem (x : PCClass) : Publish (Publish x) = Publish x := by
  cases x <;> rfl

end M0
