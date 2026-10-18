module

public import Zkc.Construction.Participant

@[expose] public section

/-! The canonical encoding of native occurrences.

A native transcript operation absorbs its occurrence under the suite's `origin`
label as the canonical logical encoding of the tree
`["zkc.native-origin/0", entry, [step, ...], [iteration_decimal, ...], event]`
([native occurrence encoding](../../../docs/spec/ir/construction.md#native-occurrence-encoding)):
a string is tag 0, its UTF-8 byte count as eight little-endian bytes and its
bytes; a list is tag 1, its element count likewise and its encoded elements. The
exported static template uses the tag `zkc.native-origin-template/0` and an
empty coordinate list.

`occurrence_inj` proves that the encoding is injective and prefix-free in the
template and the iteration coordinates, for trees whose counts fit their
eight-byte fields: distinct occurrences absorb distinct bytes, and no
occurrence's bytes extend another's. The construction bridge checks in the
kernel that `templateTree` encodes every exported template to exactly its
native bytes.
-/

set_option autoImplicit false

namespace Zkc.Construction

/-- The canonical logical trees of native occurrence encodings. -/
inductive Tree where
  | text (value : String)
  | list (items : List Tree)
  deriving Repr

/-- Eight little-endian bytes. -/
def le64 (value : Nat) : List UInt8 :=
  (List.range 8).map fun index => UInt8.ofNat (value / 256 ^ index)

def ofLe64 (bytes : List UInt8) : Nat :=
  bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0

theorem ofLe64_le64 (value : Nat) (bound : value < 2 ^ 64) : ofLe64 (le64 value) = value := by
  simp [le64, ofLe64, List.range_succ]
  omega

theorem le64_length (value : Nat) : (le64 value).length = 8 := by simp [le64]

mutual
def Tree.encode : Tree → List UInt8
  | .text value => 0 :: le64 value.utf8ByteSize ++ value.toByteArray.data.toList
  | .list items => 1 :: le64 items.length ++ Tree.encodeList items
def Tree.encodeList : List Tree → List UInt8
  | [] => []
  | item :: rest => item.encode ++ Tree.encodeList rest
end

mutual
/-- Byte counts and element counts fit their u64 fields. -/
def Tree.Bounded : Tree → Prop
  | .text value => value.utf8ByteSize < 2 ^ 64
  | .list items => items.length < 2 ^ 64 ∧ Tree.BoundedList items
def Tree.BoundedList : List Tree → Prop
  | [] => True
  | item :: rest => item.Bounded ∧ Tree.BoundedList rest
end

mutual
/-- The encoding is injective and prefix-free on bounded trees. -/
theorem Tree.encode_append_inj : ∀ (a b : Tree) (r s : List UInt8), a.Bounded → b.Bounded →
    a.encode ++ r = b.encode ++ s → a = b ∧ r = s
  | .text x, .text y, r, s, ba, bb, equal => by
      simp only [Tree.encode, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at equal
      have lengths := List.append_inj equal (by simp [le64_length])
      have sizes : x.utf8ByteSize = y.utf8ByteSize := by
        have := congrArg ofLe64 lengths.1
        rwa [ofLe64_le64 _ ba, ofLe64_le64 _ bb] at this
      have bytes := List.append_inj lengths.2 (by simp [sizes])
      refine ⟨?_, bytes.2⟩
      have dataEq : x.toByteArray.data = y.toByteArray.data := Array.ext' bytes.1
      have utf8 : x.toByteArray = y.toByteArray := by
        cases hx : x.toByteArray; cases hy : y.toByteArray; simp_all
      have strings : x = y := String.toByteArray_inj.mp utf8
      rw [strings]
  | .text _, .list _, r, s, _, _, equal => by simp [Tree.encode] at equal
  | .list _, .text _, r, s, _, _, equal => by simp [Tree.encode] at equal
  | .list xs, .list ys, r, s, ba, bb, equal => by
      simp only [Tree.encode, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at equal
      have counts := List.append_inj equal (by simp [le64_length])
      have lengths : xs.length = ys.length := by
        have := congrArg ofLe64 counts.1
        rwa [ofLe64_le64 _ ba.1, ofLe64_le64 _ bb.1] at this
      obtain ⟨same, rest⟩ := Tree.encodeList_append_inj xs ys r s lengths ba.2 bb.2 counts.2
      exact ⟨by rw [same], rest⟩
theorem Tree.encodeList_append_inj : ∀ (xs ys : List Tree) (r s : List UInt8), xs.length = ys.length →
    Tree.BoundedList xs → Tree.BoundedList ys → Tree.encodeList xs ++ r = Tree.encodeList ys ++ s → xs = ys ∧ r = s
  | [], [], r, s, _, _, _, equal => ⟨rfl, by simpa [Tree.encodeList] using equal⟩
  | x :: xs, y :: ys, r, s, lengths, bx, bys, equal => by
      simp only [Tree.encodeList, List.append_assoc] at equal
      obtain ⟨same, rest⟩ := Tree.encode_append_inj x y _ _ bx.1 bys.1 equal
      obtain ⟨sameRest, tail⟩ := Tree.encodeList_append_inj xs ys r s (by simpa using lengths) bx.2 bys.2 rest
      exact ⟨by rw [same, sameRest], tail⟩
  | [], _ :: _, _, _, lengths, _, _, _ => by simp at lengths
  | _ :: _, [], _, _, lengths, _, _, _ => by simp at lengths
end

/-- The encoding is injective on bounded trees. -/
theorem Tree.encode_inj {a b : Tree} (ba : a.Bounded) (bb : b.Bounded) (equal : a.encode = b.encode) : a = b :=
  (Tree.encode_append_inj a b [] [] ba bb (by simpa using equal)).1

theorem siteDigit_inj : ∀ a < 10, ∀ b < 10,
    Zkc.Source.Structured.protocolSiteDigit a = Zkc.Source.Structured.protocolSiteDigit b → a = b := by
  decide +kernel

theorem digitChar_inj (a : Nat) (ha : a < 10) (b : Nat) (hb : b < 10)
    (equal : Nat.digitChar a = Nat.digitChar b) : a = b := by
  rw [← Zkc.Source.Structured.protocolSiteDigit_eq a ha, ← Zkc.Source.Structured.protocolSiteDigit_eq b hb] at equal
  exact siteDigit_inj a ha b hb equal

theorem toDigits_inj : ∀ (a b : Nat), Nat.toDigits 10 a = Nat.toDigits 10 b → a = b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b equal
    rw [Nat.toDigits_eq_ite (by decide), Nat.toDigits_eq_ite (b := 10) (n := b) (by decide)] at equal
    by_cases small : a < 10 <;> by_cases small' : b < 10 <;> simp only [small, small', ↓reduceIte] at equal
    · exact digitChar_inj a small b small' (by simpa using equal)
    · have := congrArg List.length equal
      simp at this
    · have := congrArg List.length equal
      simp at this
    · obtain ⟨front, last⟩ := List.append_inj' equal rfl
      have quotient := ih (a / 10) (by omega) (b / 10) front
      have remainder := digitChar_inj (a % 10) (Nat.mod_lt _ (by decide)) (b % 10) (Nat.mod_lt _ (by decide))
        (by simpa using last)
      omega

/-- Decimal renderings of distinct naturals are distinct. -/
theorem decimal_inj {a b : Nat} (equal : toString a = toString b) : a = b := by
  rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits] at equal
  exact toDigits_inj a b (by simpa using congrArg String.toList equal)

/-- A step's canonical tree: `[kind, protocol, site]`. -/
def stepTree (step : Step) : Tree := .list [.text step.kind, .text step.protocol, .text step.site]

/-- The canonical tree of a native occurrence:
`["zkc.native-origin/0", entry, [step, ...], [iteration_decimal, ...], event]`. -/
def occurrenceTree (template : Template) (coordinates : List Nat) : Tree :=
  .list [.text "zkc.native-origin/0", .text template.entry, .list (template.steps.map stepTree),
    .list (coordinates.map fun index => .text (toString index)), .list (template.event.map .text)]

theorem map_injective_of {α β : Type} {f : α → β} (injective : ∀ x y, f x = f y → x = y) :
    ∀ {xs ys : List α}, xs.map f = ys.map f → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, equal => by
      simp only [List.map_cons, List.cons.injEq] at equal
      rw [injective x y equal.1, map_injective_of injective equal.2]
  | [], _ :: _, equal => by simp at equal
  | _ :: _, [], equal => by simp at equal

theorem stepTree_inj (x y : Step) (same : stepTree x = stepTree y) : x = y := by
  simp only [stepTree, Tree.list.injEq, List.cons.injEq, Tree.text.injEq, and_true] at same
  obtain ⟨kind, protocol, site⟩ := same
  cases x; cases y; simp_all

/-- Distinct native occurrences absorb distinct bytes, and no occurrence's
bytes extend another's: the canonical encoding is injective and prefix-free on
trees whose counts fit their fields. -/
theorem occurrence_inj {template template' : Template} {coordinates coordinates' : List Nat} (rest rest' : List UInt8)
    (bounded : (occurrenceTree template coordinates).Bounded)
    (bounded' : (occurrenceTree template' coordinates').Bounded)
    (equal : (occurrenceTree template coordinates).encode ++ rest =
      (occurrenceTree template' coordinates').encode ++ rest') :
    template = template' ∧ coordinates = coordinates' ∧ rest = rest' := by
  obtain ⟨same, restEq⟩ := Tree.encode_append_inj _ _ _ _ bounded bounded' equal
  simp only [occurrenceTree, Tree.list.injEq, List.cons.injEq, Tree.text.injEq, true_and, and_true] at same
  obtain ⟨entry, steps, coords, event⟩ := same
  refine ⟨?_, map_injective_of (fun x y same => decimal_inj (by simpa using same)) coords, restEq⟩
  cases template; cases template'
  simp only at entry steps event
  rw [entry, map_injective_of stepTree_inj steps, map_injective_of (fun x y same => by simpa using same) event]

/-- The canonical tree of an exported static template:
`["zkc.native-origin-template/0", entry, [step, ...], [], event]`. -/
def templateTree (template : Template) : Tree :=
  .list [.text "zkc.native-origin-template/0", .text template.entry, .list (template.steps.map stepTree),
    .list [], .list (template.event.map .text)]

mutual
/-- The templates of an instruction's observations and challenges, its own
before its body's. -/
def Instruction.templates : Instruction → List Template
  | ⟨operation, _, _, body⟩ =>
      (match operation with
       | .observe _ template => [template]
       | .challenge _ _ template => [template]
       | _ => []) ++ Instruction.templatesList body

/-- The templates of a program's instructions, in order. -/
def Instruction.templatesList : List Instruction → List Template
  | [] => []
  | instruction :: rest => instruction.templates ++ Instruction.templatesList rest
end

end Zkc.Construction
