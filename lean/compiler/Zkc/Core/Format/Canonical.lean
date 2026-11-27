module

public import Zkc.Core.Format.Format

@[expose] public section

/-!
The canonical wire format for every type of the core, and the proof of its laws on valid values.

Every value of a valid type is encoded into canonical bytes (`< 256`):
- `fin bound`: the fewest little-endian bytes holding every number below `bound`
  (`byteWidth bound`), rejecting values `≥ bound`;
- `bool`: one byte (`0` for `false`, `1` for `true`), rejecting `≥ 2`;
- `nat`: shortest-form unsigned LEB128 (7-bit groups, LSB first, high bit `128` continuing,
  no trailing zero group except for `0`);
- sized sequence `seq item (some n)`: `n` elements concatenated in order;
- unsized sequence `seq item none`: its length in LEB128, followed by its elements;
- `tuple` and `record`: components/fields concatenated in order;
- `variant`: alternative index as `fin count`, followed by its payload;
- `nominal`: delegated to the model's `Codecs`.

The main theorem `canonicalFormat_lawful` establishes both prefix round-trip and canonical
injectivity on valid values (`Format.Lawful`), using only `propext` and `Quot.sound`.
-/

namespace Zkc.Core

/-! ## Fixed-width little-endian natural numbers -/

/-- The fewest bytes needed to represent every natural strictly below `bound`:
the least `k` with `bound ≤ 256 ^ k`. `byteWidth 0 = byteWidth 1 = 0`,
`byteWidth 2 = byteWidth 256 = 1`, `byteWidth (2 ^ 64) = 8`, `byteWidth (2 ^ 65) = 9`. -/
def byteWidth (bound : Nat) : Nat :=
  if bound ≤ 1 then 0 else 1 + byteWidth ((bound + 255) / 256)
termination_by bound

theorem lt_pow_byteWidth (bound : Nat) : ∀ {v : Nat}, v < bound → v < 256 ^ byteWidth bound := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      intro v hv
      unfold byteWidth
      split
      · next hle =>
          have hv0 : v = 0 := by omega
          subst hv0
          decide
      · next hgt =>
          have hsub : (bound + 255) / 256 < bound := by omega
          have hdiv : v / 256 < (bound + 255) / 256 := by omega
          have hrec := ih ((bound + 255) / 256) hsub hdiv
          rw [Nat.add_comm 1, Nat.pow_succ']
          omega

/-- Write `value` in `width` little-endian bytes (`value % 256 ^ width`). -/
def writeFixed : Nat → Nat → List Nat
  | 0, _ => []
  | width + 1, value => (value % 256) :: writeFixed width (value / 256)

/-- Read `width` little-endian bytes, rejecting any entry `≥ 256` or premature end of input. -/
def readFixed : Nat → List Nat → Option (Nat × List Nat)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | width + 1, b :: bs =>
      if b < 256 then
        match readFixed width bs with
        | some (hi, rest) => some (b + 256 * hi, rest)
        | none => none
      else none

theorem writeFixed_bytes : ∀ (width value b : Nat), b ∈ writeFixed width value → b < 256
  | 0, _, _, h => nomatch h
  | width + 1, value, b, h => by
      simp only [writeFixed, List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · exact writeFixed_bytes width (value / 256) b h

theorem readFixed_writeFixed : ∀ (width value : Nat) (rest : List Nat),
    value < 256 ^ width →
    readFixed width (writeFixed width value ++ rest) = some (value, rest)
  | 0, value, rest, hlt => by
      have hv : value = 0 := by
        simp only [Nat.pow_zero] at hlt
        omega
      subst hv
      rfl
  | width + 1, value, rest, hlt => by
      have hdiv : value / 256 < 256 ^ width := by
        rw [Nat.pow_succ'] at hlt
        omega
      have hmod : value % 256 < 256 := by omega
      simp only [writeFixed, List.cons_append, readFixed, hmod, ↓reduceIte,
        readFixed_writeFixed width (value / 256) rest hdiv]
      have hre : value % 256 + 256 * (value / 256) = value := by omega
      rw [hre]

theorem readFixed_written : ∀ (width : Nat) (bs : List Nat) (value : Nat) (rest : List Nat),
    readFixed width bs = some (value, rest) →
    value < 256 ^ width ∧ bs = writeFixed width value ++ rest
  | 0, bs, value, rest, h => by
      simp only [readFixed, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩
  | width + 1, [], _, _, h => by simp [readFixed] at h
  | width + 1, b :: bs, value, rest, h => by
      simp only [readFixed] at h
      split at h
      · next hb =>
          cases hrec : readFixed width bs with
          | none => simp [hrec] at h
          | some pair =>
              obtain ⟨hi, tail⟩ := pair
              simp only [hrec, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hlt, hbs⟩ := readFixed_written width bs hi tail hrec
              refine ⟨?_, ?_⟩
              · rw [Nat.pow_succ']
                omega
              · simp only [writeFixed, List.cons_append]
                have hmod : (b + 256 * hi) % 256 = b := by omega
                have hdiv : (b + 256 * hi) / 256 = hi := by omega
                rw [hmod, hdiv, hbs]
      · simp at h

/-- Canonical format for `fin bound`: `byteWidth bound` little-endian bytes, rejecting `≥ bound`. -/
def formatFin (bound : Nat) : Format Nat where
  write value := writeFixed (byteWidth bound) value
  read bs :=
    match readFixed (byteWidth bound) bs with
    | some (v, rest) => if v < bound then some (v, rest) else none
    | none => none

theorem formatFin_lawful (bound : Nat) : (formatFin bound).Lawful (· < bound) where
  bytes a _ b hb := writeFixed_bytes (byteWidth bound) a b hb
  reads a rest ha := by
    simp only [formatFin, readFixed_writeFixed (byteWidth bound) a rest (lt_pow_byteWidth bound ha),
      ha, ↓reduceIte]
  written bs a rest h := by
    simp only [formatFin] at h
    cases hrec : readFixed (byteWidth bound) bs with
    | none => simp [hrec] at h
    | some pair =>
        obtain ⟨v, tail⟩ := pair
        simp only [hrec] at h
        split at h
        · next hlt =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hlt, (readFixed_written (byteWidth bound) bs v tail hrec).2⟩
        · simp at h

/-! ## Booleans -/

/-- Canonical format for `bool`: one byte (`0` or `1`). -/
def formatBool : Format Bool where
  write b := [if b then 1 else 0]
  read
    | 0 :: rest => some (false, rest)
    | 1 :: rest => some (true, rest)
    | _ => none

theorem formatBool_lawful : formatBool.Lawful (fun _ => True) where
  bytes a _ b hb := by
    cases a <;> simp only [formatBool, List.mem_singleton] at hb <;> subst hb <;> decide
  reads a rest _ := by cases a <;> rfl
  written bs a rest h := by
    cases bs with
    | nil => simp [formatBool] at h
    | cons b tail =>
        match b with
        | 0 =>
            simp only [formatBool, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨trivial, rfl⟩
        | 1 =>
            simp only [formatBool, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨trivial, rfl⟩
        | _ + 2 => simp [formatBool] at h

/-! ## Shortest-form unsigned LEB128 natural numbers -/

/-- Write a natural in shortest-form unsigned LEB128 (7-bit groups, LSB first). -/
def writeNat (n : Nat) : List Nat :=
  if n < 128 then [n] else (n % 128 + 128) :: writeNat (n / 128)
termination_by n

/-- Read a shortest-form unsigned LEB128 natural. `first = false` forbids a terminating `0` group. -/
def readNatAux (first : Bool) : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs =>
      if b < 128 then
        if first = true ∨ 0 < b then some (b, bs) else none
      else if b < 256 then
        match readNatAux false bs with
        | some (hi, rest) => some ((b - 128) + 128 * hi, rest)
        | none => none
      else none

theorem writeNat_bytes (n : Nat) : ∀ b, b ∈ writeNat n → b < 256 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro b hb
      unfold writeNat at hb
      split at hb
      · next hlt =>
          simp only [List.mem_singleton] at hb
          omega
      · next hge =>
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · omega
          · exact ih (n / 128) (by omega) b hb

theorem readNatAux_writeNat (n : Nat) : ∀ (first : Bool) (rest : List Nat),
    (first = true ∨ 0 < n) →
    readNatAux first (writeNat n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro first rest hok
      unfold writeNat
      split
      · next hlt =>
          simp only [List.singleton_append, readNatAux, hlt, ↓reduceIte, hok]
      · next hge =>
          have hdiv_lt : n / 128 < n := by omega
          have hdiv_pos : 0 < n / 128 := by omega
          have hnot_low : ¬ (n % 128 + 128 < 128) := by omega
          have hbyte : n % 128 + 128 < 256 := by omega
          simp only [List.cons_append, readNatAux, hnot_low, ↓reduceIte, hbyte,
            ih (n / 128) hdiv_lt false rest (.inr hdiv_pos)]
          have hre : n % 128 + 128 - 128 + 128 * (n / 128) = n := by omega
          rw [hre]

theorem readNatAux_written : ∀ (bs : List Nat) (first : Bool) (n : Nat) (rest : List Nat),
    readNatAux first bs = some (n, rest) →
    (first = true ∨ 0 < n) ∧ bs = writeNat n ++ rest
  | [], _, _, _, h => by simp [readNatAux] at h
  | b :: bs, first, n, rest, h => by
      simp only [readNatAux] at h
      split at h
      · next hlt =>
          split at h
          · next hok =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨hok, ?_⟩
              unfold writeNat
              simp [hlt]
          · simp at h
      · next hge =>
          split at h
          · next hbyte =>
              cases hrec : readNatAux false bs with
              | none => simp [hrec] at h
              | some pair =>
                  obtain ⟨hi, tail⟩ := pair
                  simp only [hrec, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨hpos, hbs⟩ := readNatAux_written bs false hi tail hrec
                  have hhi_pos : 0 < hi := by
                    rcases hpos with hfalse | hpos
                    · cases hfalse
                    · exact hpos
                  have hnot_small : ¬ (b - 128 + 128 * hi < 128) := by omega
                  refine ⟨.inr (by omega), ?_⟩
                  conv => rhs; rw [writeNat]
                  simp only [hnot_small, ↓reduceIte, List.cons_append]
                  have hmod : (b - 128 + 128 * hi) % 128 + 128 = b := by omega
                  have hdiv : (b - 128 + 128 * hi) / 128 = hi := by omega
                  rw [hmod, hdiv, hbs]
          · simp at h

/-- Canonical format for `nat`: shortest-form unsigned LEB128. -/
def formatNat : Format Nat where
  write := writeNat
  read := readNatAux true

theorem formatNat_lawful : formatNat.Lawful (fun _ => True) where
  bytes a _ b hb := writeNat_bytes a b hb
  reads a rest _ := readNatAux_writeNat a true rest (.inl rfl)
  written bs a rest h := ⟨trivial, (readNatAux_written bs true a rest h).2⟩

/-! ## Combinators: sequences, pairs, choices -/

/-- Write a list of items by concatenating their encodings in order. -/
def writeCanonicalMany {A : Type} (write : A → List Nat) : List A → List Nat
  | [] => []
  | a :: as => write a ++ writeCanonicalMany write as

/-- Read exactly `count` items in order. -/
def readCanonicalMany {A : Type} (read : List Nat → Option (A × List Nat)) :
    Nat → List Nat → Option (List A × List Nat)
  | 0, bs => some ([], bs)
  | count + 1, bs =>
      match read bs with
      | some (a, mid) =>
          match readCanonicalMany read count mid with
          | some (as, rest) => some (a :: as, rest)
          | none => none
      | none => none

theorem writeCanonicalMany_bytes {A : Type} {valid : A → Prop} {f : Format A}
    (hf : f.Lawful valid) : ∀ (xs : List A), (∀ x, x ∈ xs → valid x) →
    ∀ b, b ∈ writeCanonicalMany f.write xs → b < 256
  | [], _, _, h => nomatch h
  | x :: xs, hv, b, hb => by
      simp only [writeCanonicalMany, List.mem_append] at hb
      rcases hb with hb | hb
      · exact hf.bytes x (hv x (List.mem_cons_self ..)) b hb
      · exact writeCanonicalMany_bytes hf xs (fun y hy => hv y (List.mem_cons_of_mem _ hy)) b hb

theorem readCanonicalMany_writeCanonicalMany {A : Type} {valid : A → Prop} {f : Format A}
    (hf : f.Lawful valid) : ∀ (xs : List A) (rest : List Nat),
    (∀ x, x ∈ xs → valid x) →
    readCanonicalMany f.read xs.length (writeCanonicalMany f.write xs ++ rest) = some (xs, rest)
  | [], rest, _ => rfl
  | x :: xs, rest, hv => by
      simp only [List.length_cons, writeCanonicalMany, List.append_assoc, readCanonicalMany]
      rw [hf.reads x (writeCanonicalMany f.write xs ++ rest) (hv x (List.mem_cons_self ..))]
      dsimp only
      rw [readCanonicalMany_writeCanonicalMany hf xs rest (fun y hy => hv y (List.mem_cons_of_mem _ hy))]

theorem readCanonicalMany_written {A : Type} {valid : A → Prop} {f : Format A}
    (hf : f.Lawful valid) : ∀ (count : Nat) (bs : List Nat) (xs : List A) (rest : List Nat),
    readCanonicalMany f.read count bs = some (xs, rest) →
    (∀ x, x ∈ xs → valid x) ∧ xs.length = count ∧ bs = writeCanonicalMany f.write xs ++ rest
  | 0, bs, xs, rest, h => by
      simp only [readCanonicalMany, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨(fun _ hx => nomatch hx), rfl, rfl⟩
  | count + 1, bs, xs, rest, h => by
      simp only [readCanonicalMany] at h
      cases h1 : f.read bs with
      | none => simp [h1] at h
      | some p1 =>
          obtain ⟨a, mid⟩ := p1
          simp only [h1] at h
          cases h2 : readCanonicalMany f.read count mid with
          | none => simp [h2] at h
          | some p2 =>
              obtain ⟨tail, final⟩ := p2
              simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hva, hbs⟩ := hf.written bs a mid h1
              obtain ⟨hvt, hlen, hmid⟩ := readCanonicalMany_written hf count mid tail final h2
              refine ⟨?_, by simp [hlen], ?_⟩
              · intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact hva
                · exact hvt x hx
              · rw [hbs, hmid, writeCanonicalMany, List.append_assoc]

/-- Canonical format for a sequence of fixed length `count`: elements concatenated. -/
def formatSeqSized {A : Type} (f : Format A) (count : Nat) : Format (List A) where
  write := writeCanonicalMany f.write
  read := readCanonicalMany f.read count

theorem formatSeqSized_lawful {A : Type} {valid : A → Prop} {f : Format A}
    (hf : f.Lawful valid) (count : Nat) :
    (formatSeqSized f count).Lawful
      (fun xs => (∀ x, x ∈ xs → valid x) ∧ xs.length = count) where
  bytes xs hv b hb := writeCanonicalMany_bytes hf xs hv.1 b hb
  reads xs rest hv := by
    simp only [formatSeqSized]
    rw [← hv.2]
    exact readCanonicalMany_writeCanonicalMany hf xs rest hv.1
  written bs xs rest h := by
    obtain ⟨hvs, hlen, hbs⟩ := readCanonicalMany_written hf count bs xs rest h
    exact ⟨⟨hvs, hlen⟩, hbs⟩

/-- Canonical format for an unsized sequence: LEB128 length followed by elements. -/
def formatSeqUnsized {A : Type} (f : Format A) : Format (List A) where
  write xs := formatNat.write xs.length ++ writeCanonicalMany f.write xs
  read bs :=
    match formatNat.read bs with
    | some (len, mid) => readCanonicalMany f.read len mid
    | none => none

theorem formatSeqUnsized_lawful {A : Type} {valid : A → Prop} {f : Format A}
    (hf : f.Lawful valid) :
    (formatSeqUnsized f).Lawful (fun xs => ∀ x, x ∈ xs → valid x) where
  bytes xs hv b hb := by
    simp only [formatSeqUnsized, List.mem_append] at hb
    rcases hb with hb | hb
    · exact formatNat_lawful.bytes xs.length trivial b hb
    · exact writeCanonicalMany_bytes hf xs hv b hb
  reads xs rest hv := by
    simp only [formatSeqUnsized, List.append_assoc]
    rw [formatNat_lawful.reads xs.length (writeCanonicalMany f.write xs ++ rest) trivial]
    exact readCanonicalMany_writeCanonicalMany hf xs rest hv
  written bs xs rest h := by
    simp only [formatSeqUnsized] at h
    cases hlen : formatNat.read bs with
    | none => simp [hlen] at h
    | some p =>
        obtain ⟨n, mid⟩ := p
        simp only [hlen] at h
        obtain ⟨_, hbs⟩ := formatNat_lawful.written bs n mid hlen
        obtain ⟨hvs, hxs, hmid⟩ := readCanonicalMany_written hf n mid xs rest h
        subst hxs
        exact ⟨hvs, by simp only [formatSeqUnsized]; rw [hbs, hmid, List.append_assoc]⟩

/-- Canonical format for `Unit` (empty tuple / empty record): zero bytes. -/
def formatUnit : Format Unit where
  write _ := []
  read bs := some ((), bs)

theorem formatUnit_lawful : formatUnit.Lawful (fun _ => True) where
  bytes _ _ _ h := nomatch h
  reads a rest _ := by cases a; rfl
  written bs a rest h := by
    cases a
    simp only [formatUnit, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨trivial, h.2⟩

/-- Canonical format for a product: left component followed by right component. -/
def formatPair {A B : Type} (fa : Format A) (fb : Format B) : Format (A × B) where
  write p := fa.write p.1 ++ fb.write p.2
  read bs :=
    match fa.read bs with
    | some (a, mid) =>
        match fb.read mid with
        | some (b, rest) => some ((a, b), rest)
        | none => none
    | none => none

theorem formatPair_lawful {A B : Type} {va : A → Prop} {vb : B → Prop}
    {fa : Format A} {fb : Format B} (ha : fa.Lawful va) (hb : fb.Lawful vb) :
    (formatPair fa fb).Lawful (fun p => va p.1 ∧ vb p.2) where
  bytes p hp byte hbyte := by
    simp only [formatPair, List.mem_append] at hbyte
    rcases hbyte with hbyte | hbyte
    · exact ha.bytes p.1 hp.1 byte hbyte
    · exact hb.bytes p.2 hp.2 byte hbyte
  reads p rest hp := by
    obtain ⟨a, b⟩ := p
    simp only [formatPair, List.append_assoc]
    rw [ha.reads a (fb.write b ++ rest) hp.1]
    dsimp only
    rw [hb.reads b rest hp.2]
  written bs p rest h := by
    obtain ⟨a, b⟩ := p
    simp only [formatPair] at h
    cases h1 : fa.read bs with
    | none => simp [h1] at h
    | some p1 =>
        obtain ⟨a', mid⟩ := p1
        simp only [h1] at h
        cases h2 : fb.read mid with
        | none => simp [h2] at h
        | some p2 =>
            obtain ⟨b', tail⟩ := p2
            simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hva, hbs⟩ := ha.written bs a' mid h1
            obtain ⟨hvb, hmid⟩ := hb.written mid b' tail h2
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            exact ⟨⟨hva, hvb⟩, by simp only [formatPair]; rw [hbs, hmid, List.append_assoc]⟩

/-! ## Canonical format for all core types -/

/-- Number of alternatives in a `Tys` list. -/
def Tys.length {K : Type} : Tys K → Nat
  | .nil => 0
  | .cons _ rest => 1 + rest.length

section
variable {V : Vocabulary} (M : Model V) (codecs : Codecs M)

mutual
  /-- The canonical format of any core type. -/
  def canonicalFormat : (τ : V.Ty) → Format (M.Val τ)
    | .bool => formatBool
    | .nat => formatNat
    | .fin bound => formatFin bound
    | .seq item (some count) => formatSeqSized (canonicalFormat item) count
    | .seq item none => formatSeqUnsized (canonicalFormat item)
    | .tuple items => canonicalFormatTys items
    | .record _ _ fields => canonicalFormatTys fields
    | .variant _ alts =>
        { write := fun choice =>
            let (tag, payload) := writeChoice alts choice
            (formatFin alts.length).write tag ++ payload
          read := fun bs =>
            match (formatFin alts.length).read bs with
            | some (tag, mid) => readChoice alts tag mid
            | none => none }
    | .nominal key => codecs.format key

  /-- The canonical format of a `Tys` product (tuples and records). -/
  def canonicalFormatTys : (τs : Tys V.TypeKey) → Format (τs.Val M.toCarriers)
    | .nil => formatUnit
    | .cons head rest => formatPair (canonicalFormat head) (canonicalFormatTys rest)

  /-- Encode a variant choice into its zero-based tag and encoded payload bytes. -/
  def writeChoice : (alts : Tys V.TypeKey) → alts.Choice M.toCarriers → Nat × List Nat
    | .nil, v => nomatch v
    | .cons head _, .inl v => (0, (canonicalFormat head).write v)
    | .cons _ rest, .inr v =>
        let (tag, payload) := writeChoice rest v
        (tag + 1, payload)

  /-- Decode a variant choice given its zero-based tag. -/
  def readChoice : (alts : Tys V.TypeKey) → Nat → List Nat →
      Option (alts.Choice M.toCarriers × List Nat)
    | .nil, _, _ => none
    | .cons head _, 0, bs =>
        match (canonicalFormat head).read bs with
        | some (v, rest) => some (.inl v, rest)
        | none => none
    | .cons _ rest, tag + 1, bs =>
        match readChoice rest tag bs with
        | some (v, tail) => some (.inr v, tail)
        | none => none
end

mutual
  theorem canonicalFormat_lawful : (τ : V.Ty) →
      (canonicalFormat M codecs τ).Lawful (M.Valid τ)
    | .bool => formatBool_lawful
    | .nat => formatNat_lawful
    | .fin bound => formatFin_lawful bound
    | .seq item (some count) => by
        have h := formatSeqSized_lawful (canonicalFormat_lawful item) count
        refine ⟨fun xs hv => h.bytes xs ⟨hv.1, hv.2 count rfl⟩,
          fun xs rest hv => h.reads xs rest ⟨hv.1, hv.2 count rfl⟩,
          fun bs xs rest hr => ?_⟩
        obtain ⟨⟨hvs, hlen⟩, hbs⟩ := h.written bs xs rest hr
        exact ⟨⟨hvs, fun n hn => by cases hn; exact hlen⟩, hbs⟩
    | .seq item none => by
        have h := formatSeqUnsized_lawful (canonicalFormat_lawful item)
        refine ⟨fun xs hv => h.bytes xs hv.1,
          fun xs rest hv => h.reads xs rest hv.1,
          fun bs xs rest hr => ?_⟩
        obtain ⟨hvs, hbs⟩ := h.written bs xs rest hr
        exact ⟨⟨hvs, fun _ hn => nomatch hn⟩, hbs⟩
    | .tuple items => canonicalFormatTys_lawful items
    | .record _ _ fields => canonicalFormatTys_lawful fields
    | .variant _ alts => by
        refine ⟨?_, ?_, ?_⟩
        · intro c hc b hb
          simp only [canonicalFormat, List.mem_append] at hb
          have htag := writeChoice_tag alts c
          rcases hb with hb | hb
          · exact (formatFin_lawful alts.length).bytes (writeChoice M codecs alts c).1 htag b hb
          · exact writeChoice_bytes alts c hc b hb
        · intro c rest hc
          simp only [canonicalFormat, List.append_assoc]
          have htag := writeChoice_tag alts c
          rw [(formatFin_lawful alts.length).reads (writeChoice M codecs alts c).1 _ htag]
          exact readChoice_writeChoice alts c rest hc
        · intro bs c rest hr
          simp only [canonicalFormat] at hr
          cases htag : (formatFin alts.length).read bs with
          | none => simp [htag] at hr
          | some p =>
              obtain ⟨tag, mid⟩ := p
              simp only [htag] at hr
              obtain ⟨_, hbs⟩ := (formatFin_lawful alts.length).written bs tag mid htag
              obtain ⟨hvc, htagEq, hmid⟩ := readChoice_written alts tag mid c rest hr
              refine ⟨hvc, ?_⟩
              simp only [canonicalFormat]
              rw [hbs, hmid, ← htagEq, List.append_assoc]
    | .nominal key => codecs.lawful key

  theorem canonicalFormatTys_lawful : (τs : Tys V.TypeKey) →
      (canonicalFormatTys M codecs τs).Lawful (Tys.Valid M.toCarriers τs)
    | .nil => formatUnit_lawful
    | .cons head rest =>
        formatPair_lawful (canonicalFormat_lawful head) (canonicalFormatTys_lawful rest)

  theorem writeChoice_tag : (alts : Tys V.TypeKey) → (c : alts.Choice M.toCarriers) →
      (writeChoice M codecs alts c).1 < alts.length
    | .nil, c => nomatch c
    | .cons _ _, .inl _ => by
        simp only [writeChoice, Tys.length]
        omega
    | .cons _ rest, .inr c => by
        have hrec := writeChoice_tag rest c
        simp only [writeChoice, Tys.length]
        omega

  theorem writeChoice_bytes : (alts : Tys V.TypeKey) → (c : alts.Choice M.toCarriers) →
      alts.ValidChoice M.toCarriers c →
      ∀ b, b ∈ (writeChoice M codecs alts c).2 → b < 256
    | .nil, c, _ => nomatch c
    | .cons head _, .inl v, hv => (canonicalFormat_lawful head).bytes v hv
    | .cons _ rest, .inr c, hv => writeChoice_bytes rest c hv

  theorem readChoice_writeChoice : (alts : Tys V.TypeKey) → (c : alts.Choice M.toCarriers) →
      (rest : List Nat) → alts.ValidChoice M.toCarriers c →
      readChoice M codecs alts (writeChoice M codecs alts c).1
        ((writeChoice M codecs alts c).2 ++ rest) = some (c, rest)
    | .nil, c, _, _ => nomatch c
    | .cons head _, .inl v, rest, hv => by
        simp only [writeChoice, readChoice]
        rw [(canonicalFormat_lawful head).reads v rest hv]
    | .cons _ restAlts, .inr c, rest, hv => by
        simp only [writeChoice, readChoice]
        rw [readChoice_writeChoice restAlts c rest hv]

  theorem readChoice_written : (alts : Tys V.TypeKey) → (tag : Nat) → (bs : List Nat) →
      (c : alts.Choice M.toCarriers) → (rest : List Nat) →
      readChoice M codecs alts tag bs = some (c, rest) →
      alts.ValidChoice M.toCarriers c ∧
        (writeChoice M codecs alts c).1 = tag ∧
        bs = (writeChoice M codecs alts c).2 ++ rest
    | .nil, _, _, _, _, h => by simp [readChoice] at h
    | .cons head _, 0, bs, c, rest, h => by
        simp only [readChoice] at h
        cases h1 : (canonicalFormat M codecs head).read bs with
        | none => simp [h1] at h
        | some p =>
            obtain ⟨v, tail⟩ := p
            simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hv, hbs⟩ := (canonicalFormat_lawful head).written bs v tail h1
            exact ⟨hv, rfl, hbs⟩
    | .cons _ restAlts, tag + 1, bs, c, rest, h => by
        simp only [readChoice] at h
        cases h1 : readChoice M codecs restAlts tag bs with
        | none => simp [h1] at h
        | some p =>
            obtain ⟨v, tail⟩ := p
            simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hv, htag, hbs⟩ := readChoice_written restAlts tag bs v tail h1
            refine ⟨hv, ?_, hbs⟩
            simp only [writeChoice, htag]
end

/-! ## Canonical format for heterogeneous lists of values -/

/-- Encode a heterogeneous list of values in order. -/
def writeHList : {tys : List V.Ty} → HList M.Val tys → List Nat
  | [], .nil => []
  | τ :: _, .cons v rest => (canonicalFormat M codecs τ).write v ++ writeHList rest

/-- Decode a heterogeneous list of values in order. -/
def readHList : (tys : List V.Ty) → List Nat → Option (HList M.Val tys × List Nat)
  | [], bs => some (.nil, bs)
  | τ :: rest, bs =>
      match (canonicalFormat M codecs τ).read bs with
      | some (v, mid) =>
          match readHList rest mid with
          | some (vs, tail) => some (.cons v vs, tail)
          | none => none
      | none => none

/-- Canonical format for an `HList M.Val tys`. -/
def formatHList (tys : List V.Ty) : Format (HList M.Val tys) where
  write := writeHList M codecs
  read := readHList M codecs tys

theorem formatHList_lawful : (tys : List V.Ty) →
    (formatHList M codecs tys).Lawful (HList.All M.Valid)
  | [] =>
      { bytes := fun .nil _ _ h => nomatch h
        reads := fun .nil _ _ => rfl
        written := fun bs .nil rest h => by
          simp only [formatHList, readHList, Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨trivial, h.2⟩ }
  | τ :: rest =>
      { bytes := fun (.cons v vs) hv b hb => by
          simp only [formatHList, writeHList, List.mem_append] at hb
          rcases hb with hb | hb
          · exact (canonicalFormat_lawful M codecs τ).bytes v hv.1 b hb
          · exact (formatHList_lawful rest).bytes vs hv.2 b hb
        reads := fun (.cons v vs) tail hv => by
          simp only [formatHList, writeHList, readHList, List.append_assoc]
          rw [(canonicalFormat_lawful M codecs τ).reads v _ hv.1]
          dsimp only
          have hrest : readHList M codecs rest (writeHList M codecs vs ++ tail) = some (vs, tail) :=
            (formatHList_lawful rest).reads vs tail hv.2
          rw [hrest]
        written := fun bs (.cons v vs) tail hr => by
          simp only [formatHList, readHList] at hr
          cases h1 : (canonicalFormat M codecs τ).read bs with
          | none => simp [h1] at hr
          | some p1 =>
              obtain ⟨v', mid⟩ := p1
              simp only [h1] at hr
              cases h2 : readHList M codecs rest mid with
              | none => simp [h2] at hr
              | some p2 =>
                  obtain ⟨vs', fin⟩ := p2
                  simp only [h2, Option.some.injEq, Prod.mk.injEq] at hr
                  obtain ⟨hv, hbs⟩ := (canonicalFormat_lawful M codecs τ).written bs v' mid h1
                  obtain ⟨hvs, hmid⟩ := (formatHList_lawful rest).written mid vs' fin h2
                  dsimp only [formatHList] at hmid
                  obtain ⟨hcons, rfl⟩ := hr
                  cases hcons
                  exact ⟨⟨hv, hvs⟩, by
                    change bs =
                      ((canonicalFormat M codecs τ).write v ++ writeHList M codecs vs) ++ fin
                    rw [hbs, hmid, List.append_assoc]⟩ }

end

end Zkc.Core
