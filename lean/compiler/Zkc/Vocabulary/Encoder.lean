module

public import Zkc.Core.Scheme.Identity
public import Zkc.Vocabulary.Project

@[expose] public section
set_option autoImplicit false

/-!
Canonical injective byte encoders (`Core.VocabEncoder`) for the standard vocabulary
(`Zkc.Vocabulary.standard`) and any project-linked vocabulary (`Project.Bindings.vocabulary`).

Every key encoding is prefix-free (`Core.PrefixFree`) and emits strictly canonical bytes (`< 256`),
establishing `Core.VocabEncoder.Injective` strictly within the package's two-axiom policy
(`propext`, `Quot.sound`) with zero `partial` definitions.
-/

namespace Zkc.Vocabulary

open Zkc.Core

/-! ## Small prefix-free combinators -/

private theorem tag_prefixFree {A : Type} {f : A → List Nat} {t : Nat}
    (hf : PrefixFree f) : PrefixFree (fun a => t :: f a) := by
  intro a b r₁ r₂ h
  simp only [List.cons_append, List.cons.injEq] at h
  exact hf a b r₁ r₂ h.2

private theorem pair_prefixFree {A B : Type} {f : A → List Nat} {g : B → List Nat}
    (hf : PrefixFree f) (hg : PrefixFree g) :
    PrefixFree (fun p : A × B => f p.1 ++ g p.2) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ r₁ r₂ h
  simp only [List.append_assoc] at h
  obtain ⟨ha, hrest⟩ := hf a₁ a₂ _ _ h
  obtain ⟨hb, hr⟩ := hg b₁ b₂ r₁ r₂ hrest
  exact ⟨by rw [ha, hb], hr⟩

private theorem singleton_tag_bytes (t : Nat) (ht : t < 256) :
    ∀ b, b ∈ [t] → b < 256 := by
  intro b hb
  simp only [List.mem_singleton] at hb
  omega

private theorem cons_tag_bytes {t : Nat} (ht : t < 256) {xs : List Nat}
    (hxs : ∀ b, b ∈ xs → b < 256) : ∀ b, b ∈ t :: xs → b < 256 := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hmem
  · exact ht
  · exact hxs b hmem

private theorem append_bytes {xs ys : List Nat}
    (hxs : ∀ b, b ∈ xs → b < 256) (hys : ∀ b, b ∈ ys → b < 256) :
    ∀ b, b ∈ xs ++ ys → b < 256 := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact hxs b h
  · exact hys b h

/-! ## Standard vocabulary encoders -/

def encodeField : Field → List Nat
  | .koalaBear => [0]
  | .koalaBear4 => [1]
  | .bls12381Fr => [2]

theorem encodeField_bytes (f : Field) : ∀ b, b ∈ encodeField f → b < 256 := by
  cases f <;> exact singleton_tag_bytes _ (by decide)

theorem encodeField_prefixFree : PrefixFree encodeField := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeField, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
    first | exact ⟨rfl, h.2⟩ | (cases h.1)

def encodeCurveGroup : CurveGroup → List Nat
  | .g1 => [0]
  | .g2 => [1]
  | .gt => [2]

theorem encodeCurveGroup_bytes (g : CurveGroup) : ∀ b, b ∈ encodeCurveGroup g → b < 256 := by
  cases g <;> exact singleton_tag_bytes _ (by decide)

theorem encodeCurveGroup_prefixFree : PrefixFree encodeCurveGroup := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeCurveGroup, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
    first | exact ⟨rfl, h.2⟩ | (cases h.1)

def encodeTypeKey : TypeKey → List Nat
  | .field f => 0 :: encodeField f
  | .nonzero f => 1 :: encodeField f
  | .group g => 2 :: encodeCurveGroup g

theorem encodeTypeKey_bytes : ∀ k b, b ∈ encodeTypeKey k → b < 256
  | .field f, b, h => cons_tag_bytes (by decide) (encodeField_bytes f) b h
  | .nonzero f, b, h => cons_tag_bytes (by decide) (encodeField_bytes f) b h
  | .group g, b, h => cons_tag_bytes (by decide) (encodeCurveGroup_bytes g) b h

theorem encodeTypeKey_prefixFree : PrefixFree encodeTypeKey := by
  intro a b r₁ r₂ h
  cases a with
  | field f₁ =>
      cases b with
      | field f₂ =>
          simp only [encodeTypeKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hf, hr⟩ := encodeField_prefixFree f₁ f₂ r₁ r₂ h.2
          exact ⟨congrArg TypeKey.field hf, hr⟩
      | nonzero _ => simp [encodeTypeKey] at h
      | group _ => simp [encodeTypeKey] at h
  | nonzero f₁ =>
      cases b with
      | field _ => simp [encodeTypeKey] at h
      | nonzero f₂ =>
          simp only [encodeTypeKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hf, hr⟩ := encodeField_prefixFree f₁ f₂ r₁ r₂ h.2
          exact ⟨congrArg TypeKey.nonzero hf, hr⟩
      | group _ => simp [encodeTypeKey] at h
  | group g₁ =>
      cases b with
      | field _ => simp [encodeTypeKey] at h
      | nonzero _ => simp [encodeTypeKey] at h
      | group g₂ =>
          simp only [encodeTypeKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hg, hr⟩ := encodeCurveGroup_prefixFree g₁ g₂ r₁ r₂ h.2
          exact ⟨congrArg TypeKey.group hg, hr⟩

def encodeAtom : Atom → List Nat
  | .field f => 0 :: encodeField f
  | .group g => 1 :: encodeCurveGroup g

theorem encodeAtom_bytes : ∀ a b, b ∈ encodeAtom a → b < 256
  | .field f, b, h => cons_tag_bytes (by decide) (encodeField_bytes f) b h
  | .group g, b, h => cons_tag_bytes (by decide) (encodeCurveGroup_bytes g) b h

theorem encodeAtom_prefixFree : PrefixFree encodeAtom := by
  intro a b r₁ r₂ h
  cases a with
  | field f₁ =>
      cases b with
      | field f₂ =>
          simp only [encodeAtom, List.cons_append, List.cons.injEq] at h
          obtain ⟨hf, hr⟩ := encodeField_prefixFree f₁ f₂ r₁ r₂ h.2
          exact ⟨congrArg Atom.field hf, hr⟩
      | group _ => simp [encodeAtom] at h
  | group g₁ =>
      cases b with
      | field _ => simp [encodeAtom] at h
      | group g₂ =>
          simp only [encodeAtom, List.cons_append, List.cons.injEq] at h
          obtain ⟨hg, hr⟩ := encodeCurveGroup_prefixFree g₁ g₂ r₁ r₂ h.2
          exact ⟨congrArg Atom.group hg, hr⟩

def encodeElement : Element → List Nat
  | .atom a => 0 :: encodeAtom a
  | .sized item size => 1 :: encodeElement item ++ encodeNat size

theorem encodeElement_bytes : ∀ e b, b ∈ encodeElement e → b < 256
  | .atom a, b, h => cons_tag_bytes (by decide) (encodeAtom_bytes a) b h
  | .sized item size, b, h =>
      cons_tag_bytes (by decide)
        (append_bytes (encodeElement_bytes item) (encodeNat_bytes size)) b h

theorem encodeElement_prefixFree : PrefixFree encodeElement := by
  intro a
  induction a with
  | atom a₁ =>
      intro b r₁ r₂ h
      cases b with
      | atom a₂ =>
          simp only [encodeElement, List.cons_append, List.cons.injEq] at h
          obtain ⟨ha, hr⟩ := encodeAtom_prefixFree a₁ a₂ r₁ r₂ h.2
          exact ⟨congrArg Element.atom ha, hr⟩
      | sized _ _ => simp [encodeElement] at h
  | sized item₁ size₁ ih =>
      intro b r₁ r₂ h
      cases b with
      | atom _ => simp [encodeElement] at h
      | sized item₂ size₂ =>
          simp only [encodeElement, List.cons_append, List.append_assoc, List.cons.injEq] at h
          obtain ⟨hitem, hrest⟩ := ih item₂ _ _ h.2
          obtain ⟨hsize, hr⟩ := encodeNat_prefixFree size₁ size₂ r₁ r₂ hrest
          exact ⟨by rw [hitem, hsize], hr⟩

def encodeAmong : Among → List Nat
  | .all => [0]
  | .nonzero => [1]

theorem encodeAmong_bytes (a : Among) : ∀ b, b ∈ encodeAmong a → b < 256 := by
  cases a <;> exact singleton_tag_bytes _ (by decide)

theorem encodeAmong_prefixFree : PrefixFree encodeAmong := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeAmong, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
    first | exact ⟨rfl, h.2⟩ | (cases h.1)

def encodeFieldRow : FieldRow → List Nat
  | .add => [0]
  | .sub => [1]
  | .mul => [2]
  | .neg => [3]
  | .inverse => [4]
  | .pow => [5]
  | .equal => [6]
  | .isNonzero => [7]
  | .nonzero => [8]
  | .fromNonzero => [9]
  | .fromNat => [10]
  | .toNat => [11]
  | .components => [12]
  | .fromComponents => [13]
  | .embed => [14]
  | .coefficients => [15]
  | .fromCoefficients => [16]
  | .root => [17]

theorem encodeFieldRow_bytes (r : FieldRow) : ∀ b, b ∈ encodeFieldRow r → b < 256 := by
  cases r <;> exact singleton_tag_bytes _ (by decide)

theorem encodeFieldRow_prefixFree : PrefixFree encodeFieldRow := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeFieldRow, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
    first | exact ⟨rfl, h.2⟩ | (cases h.1)

def encodeGroupRow : GroupRow → List Nat
  | .zero => [0]
  | .add => [1]
  | .sub => [2]
  | .neg => [3]
  | .scale => [4]
  | .equal => [5]
  | .generator => [6]

theorem encodeGroupRow_bytes (r : GroupRow) : ∀ b, b ∈ encodeGroupRow r → b < 256 := by
  cases r <;> exact singleton_tag_bytes _ (by decide)

theorem encodeGroupRow_prefixFree : PrefixFree encodeGroupRow := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeGroupRow, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
    first | exact ⟨rfl, h.2⟩ | (cases h.1)

def encodeSeqRow : SeqRow → List Nat
  | .add => [0]
  | .sub => [1]
  | .scale => [2]
  | .sum => [3]
  | .product => [4]
  | .inner => [5]
  | .equal => [6]

theorem encodeSeqRow_bytes (r : SeqRow) : ∀ b, b ∈ encodeSeqRow r → b < 256 := by
  cases r <;> exact singleton_tag_bytes _ (by decide)

theorem encodeSeqRow_prefixFree : PrefixFree encodeSeqRow := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeSeqRow, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
    first | exact ⟨rfl, h.2⟩ | (cases h.1)

def encodeHash : Hash → List Nat
  | .sha256 => [0]
  | .keccak256 => [1]
  | .shake128 count => 2 :: encodeNat count
  | .shake256 count => 3 :: encodeNat count

theorem encodeHash_bytes : ∀ h b, b ∈ encodeHash h → b < 256
  | .sha256, b, hb => singleton_tag_bytes 0 (by decide) b hb
  | .keccak256, b, hb => singleton_tag_bytes 1 (by decide) b hb
  | .shake128 n, b, hb => cons_tag_bytes (by decide) (encodeNat_bytes n) b hb
  | .shake256 n, b, hb => cons_tag_bytes (by decide) (encodeNat_bytes n) b hb

theorem encodeHash_prefixFree : PrefixFree encodeHash := by
  intro a b r₁ r₂ h
  cases a with
  | sha256 =>
      cases b <;> simp only [encodeHash, List.cons_append, List.nil_append, List.cons.injEq] at h
      · exact ⟨rfl, h.2⟩
      · cases h.1
      · cases h.1
      · cases h.1
  | keccak256 =>
      cases b <;> simp only [encodeHash, List.cons_append, List.nil_append, List.cons.injEq] at h
      · cases h.1
      · exact ⟨rfl, h.2⟩
      · cases h.1
      · cases h.1
  | shake128 n₁ =>
      cases b with
      | shake128 n₂ =>
          simp only [encodeHash, List.cons_append, List.cons.injEq] at h
          obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ h.2
          exact ⟨congrArg Hash.shake128 hn, hr⟩
      | sha256 => simp [encodeHash] at h
      | keccak256 => simp [encodeHash] at h
      | shake256 _ => simp [encodeHash] at h
  | shake256 n₁ =>
      cases b with
      | shake256 n₂ =>
          simp only [encodeHash, List.cons_append, List.cons.injEq] at h
          obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ h.2
          exact ⟨congrArg Hash.shake256 hn, hr⟩
      | sha256 => simp [encodeHash] at h
      | keccak256 => simp [encodeHash] at h
      | shake128 _ => simp [encodeHash] at h

def encodeRowKey : RowKey → List Nat
  | .field row field among => 0 :: encodeFieldRow row ++ encodeField field ++ encodeAmong among
  | .group row atom => 1 :: encodeGroupRow row ++ encodeAtom atom
  | .seq row item size => 2 :: encodeSeqRow row ++ encodeElement item ++ encodeOption encodeNat size
  | .hash hash => 3 :: encodeHash hash
  | .pair => [4]

theorem encodeRowKey_bytes : ∀ k b, b ∈ encodeRowKey k → b < 256
  | .field r f a, b, h =>
      cons_tag_bytes (by decide)
        (append_bytes (append_bytes (encodeFieldRow_bytes r) (encodeField_bytes f))
          (encodeAmong_bytes a)) b h
  | .group r a, b, h =>
      cons_tag_bytes (by decide) (append_bytes (encodeGroupRow_bytes r) (encodeAtom_bytes a)) b h
  | .seq r e s, b, h =>
      cons_tag_bytes (by decide)
        (append_bytes (append_bytes (encodeSeqRow_bytes r) (encodeElement_bytes e))
          (encodeOption_bytes encodeNat encodeNat_bytes s)) b h
  | .hash h, b, hb => cons_tag_bytes (by decide) (encodeHash_bytes h) b hb
  | .pair, b, hb => singleton_tag_bytes 4 (by decide) b hb

theorem encodeRowKey_prefixFree : PrefixFree encodeRowKey := by
  intro a b r₁ r₂ h
  cases a with
  | field row₁ field₁ among₁ =>
      cases b with
      | field row₂ field₂ among₂ =>
          simp only [encodeRowKey, List.cons_append, List.append_assoc, List.cons.injEq] at h
          obtain ⟨hrow, hrest1⟩ := encodeFieldRow_prefixFree row₁ row₂ _ _ h.2
          obtain ⟨hf, hrest2⟩ := encodeField_prefixFree field₁ field₂ _ _ hrest1
          obtain ⟨ha, hr⟩ := encodeAmong_prefixFree among₁ among₂ r₁ r₂ hrest2
          exact ⟨by rw [hrow, hf, ha], hr⟩
      | group _ _ => simp [encodeRowKey] at h
      | seq _ _ _ => simp [encodeRowKey] at h
      | hash _ => simp [encodeRowKey] at h
      | pair => simp [encodeRowKey] at h
  | group row₁ atom₁ =>
      cases b with
      | field _ _ _ => simp [encodeRowKey] at h
      | group row₂ atom₂ =>
          simp only [encodeRowKey, List.cons_append, List.append_assoc, List.cons.injEq] at h
          obtain ⟨hrow, hrest⟩ := encodeGroupRow_prefixFree row₁ row₂ _ _ h.2
          obtain ⟨ha, hr⟩ := encodeAtom_prefixFree atom₁ atom₂ r₁ r₂ hrest
          exact ⟨by rw [hrow, ha], hr⟩
      | seq _ _ _ => simp [encodeRowKey] at h
      | hash _ => simp [encodeRowKey] at h
      | pair => simp [encodeRowKey] at h
  | seq row₁ item₁ size₁ =>
      cases b with
      | field _ _ _ => simp [encodeRowKey] at h
      | group _ _ => simp [encodeRowKey] at h
      | seq row₂ item₂ size₂ =>
          simp only [encodeRowKey, List.cons_append, List.append_assoc, List.cons.injEq] at h
          obtain ⟨hrow, hrest1⟩ := encodeSeqRow_prefixFree row₁ row₂ _ _ h.2
          obtain ⟨hitem, hrest2⟩ := encodeElement_prefixFree item₁ item₂ _ _ hrest1
          obtain ⟨hsize, hr⟩ := encodeOption_prefixFree encodeNat_prefixFree size₁ size₂ r₁ r₂ hrest2
          exact ⟨by rw [hrow, hitem, hsize], hr⟩
      | hash _ => simp [encodeRowKey] at h
      | pair => simp [encodeRowKey] at h
  | hash hash₁ =>
      cases b with
      | field _ _ _ => simp [encodeRowKey] at h
      | group _ _ => simp [encodeRowKey] at h
      | seq _ _ _ => simp [encodeRowKey] at h
      | hash hash₂ =>
          simp only [encodeRowKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hh, hr⟩ := encodeHash_prefixFree hash₁ hash₂ r₁ r₂ h.2
          exact ⟨congrArg RowKey.hash hh, hr⟩
      | pair => simp [encodeRowKey] at h
  | pair =>
      cases b with
      | field _ _ _ => simp [encodeRowKey] at h
      | group _ _ => simp [encodeRowKey] at h
      | seq _ _ _ => simp [encodeRowKey] at h
      | hash _ => simp [encodeRowKey] at h
      | pair =>
          simp only [encodeRowKey, List.cons_append, List.nil_append, List.cons.injEq] at h
          exact ⟨rfl, h.2⟩

mutual
  /-- Prefix-free canonical byte encoding of a `Core.Ty K` parameterized by a key encoder `encKey`. -/
  def encodeTyWith {K : Type} (encKey : K → List Nat) : Core.Ty K → List Nat
    | .bool => [0]
    | .nat => [1]
    | .fin bound => 2 :: encodeNat bound
    | .seq item size => 3 :: encodeTyWith encKey item ++ encodeOption encodeNat size
    | .tuple items => 4 :: encodeTysWith encKey items
    | .record key linear fields =>
        5 :: encodeNat key.number ++ (if linear then [1] else [0]) ++ encodeTysWith encKey fields
    | .variant key alts => 6 :: encodeNat key.number ++ encodeTysWith encKey alts
    | .nominal key => 7 :: encKey key

  /-- Prefix-free canonical byte encoding of a `Core.Tys K` parameterized by a key encoder `encKey`. -/
  def encodeTysWith {K : Type} (encKey : K → List Nat) : Core.Tys K → List Nat
    | .nil => [0]
    | .cons head rest => 1 :: encodeTyWith encKey head ++ encodeTysWith encKey rest
end

private theorem encodeBoolFlag_bytes (b : Bool) : ∀ c, c ∈ (if b then [1] else [0]) → c < 256 := by
  cases b <;> exact singleton_tag_bytes _ (by decide)

private theorem encodeBoolFlag_prefixFree : PrefixFree (fun b : Bool => if b then [1] else [0]) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [↓reduceIte, Bool.false_eq_true, List.cons_append, List.nil_append,
    List.cons.injEq] at h <;> first | exact ⟨rfl, h.2⟩ | (cases h.1)

mutual
  theorem encodeTyWith_bytes {K : Type} {encKey : K → List Nat}
      (hKey : ∀ k b, b ∈ encKey k → b < 256) :
      ∀ (τ : Core.Ty K) b, b ∈ encodeTyWith encKey τ → b < 256
    | .bool, b, h => singleton_tag_bytes 0 (by decide) b h
    | .nat, b, h => singleton_tag_bytes 1 (by decide) b h
    | .fin n, b, h => cons_tag_bytes (by decide) (encodeNat_bytes n) b h
    | .seq item size, b, h =>
        cons_tag_bytes (by decide)
          (append_bytes (encodeTyWith_bytes hKey item) (encodeOption_bytes encodeNat encodeNat_bytes size)) b h
    | .tuple items, b, h => cons_tag_bytes (by decide) (encodeTysWith_bytes hKey items) b h
    | .record key linear fields, b, h =>
        cons_tag_bytes (by decide)
          (append_bytes (append_bytes (encodeNat_bytes key.number) (encodeBoolFlag_bytes linear))
            (encodeTysWith_bytes hKey fields)) b h
    | .variant key alts, b, h =>
        cons_tag_bytes (by decide)
          (append_bytes (encodeNat_bytes key.number) (encodeTysWith_bytes hKey alts)) b h
    | .nominal key, b, h => cons_tag_bytes (by decide) (hKey key) b h

  theorem encodeTysWith_bytes {K : Type} {encKey : K → List Nat}
      (hKey : ∀ k b, b ∈ encKey k → b < 256) :
      ∀ (ts : Core.Tys K) b, b ∈ encodeTysWith encKey ts → b < 256
    | .nil, b, h => singleton_tag_bytes 0 (by decide) b h
    | .cons head rest, b, h =>
        cons_tag_bytes (by decide)
          (append_bytes (encodeTyWith_bytes hKey head) (encodeTysWith_bytes hKey rest)) b h
end

mutual
  theorem encodeTyWith_prefixFree {K : Type} {encKey : K → List Nat}
      (hKey : PrefixFree encKey) : ∀ (a b : Core.Ty K) (r₁ r₂ : List Nat),
      encodeTyWith encKey a ++ r₁ = encodeTyWith encKey b ++ r₂ → a = b ∧ r₁ = r₂
    | .bool, .bool, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.nil_append, List.cons.injEq] at h
        exact ⟨rfl, h.2⟩
    | .nat, .nat, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.nil_append, List.cons.injEq] at h
        exact ⟨rfl, h.2⟩
    | .fin n₁, .fin n₂, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.cons.injEq] at h
        obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ h.2
        exact ⟨congrArg Ty.fin hn, hr⟩
    | .seq i₁ s₁, .seq i₂ s₂, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.append_assoc, List.cons.injEq] at h
        obtain ⟨hi, hrest⟩ := encodeTyWith_prefixFree hKey i₁ i₂ _ _ h.2
        obtain ⟨hs, hr⟩ := encodeOption_prefixFree encodeNat_prefixFree s₁ s₂ r₁ r₂ hrest
        exact ⟨by rw [hi, hs], hr⟩
    | .tuple ts₁, .tuple ts₂, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.cons.injEq] at h
        obtain ⟨ht, hr⟩ := encodeTysWith_prefixFree hKey ts₁ ts₂ r₁ r₂ h.2
        exact ⟨congrArg Ty.tuple ht, hr⟩
    | .record k₁ l₁ fs₁, .record k₂ l₂ fs₂, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.append_assoc, List.cons.injEq] at h
        obtain ⟨hk, hrest1⟩ := encodeNat_prefixFree k₁.number k₂.number _ _ h.2
        obtain ⟨hl, hrest2⟩ := encodeBoolFlag_prefixFree l₁ l₂ _ _ hrest1
        obtain ⟨hfs, hr⟩ := encodeTysWith_prefixFree hKey fs₁ fs₂ r₁ r₂ hrest2
        have hkey : k₁ = k₂ := by cases k₁; cases k₂; exact congrArg Key.mk hk
        exact ⟨by rw [hkey, hl, hfs], hr⟩
    | .variant k₁ as₁, .variant k₂ as₂, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.append_assoc, List.cons.injEq] at h
        obtain ⟨hk, hrest⟩ := encodeNat_prefixFree k₁.number k₂.number _ _ h.2
        obtain ⟨has, hr⟩ := encodeTysWith_prefixFree hKey as₁ as₂ r₁ r₂ hrest
        have hkey : k₁ = k₂ := by cases k₁; cases k₂; exact congrArg Key.mk hk
        exact ⟨by rw [hkey, has], hr⟩
    | .nominal k₁, .nominal k₂, r₁, r₂, h => by
        simp only [encodeTyWith, List.cons_append, List.cons.injEq] at h
        obtain ⟨hk, hr⟩ := hKey k₁ k₂ r₁ r₂ h.2
        exact ⟨congrArg Ty.nominal hk, hr⟩
    | .bool, .nat, _, _, h | .bool, .fin _, _, _, h | .bool, .seq _ _, _, _, h
    | .bool, .tuple _, _, _, h | .bool, .record _ _ _, _, _, h | .bool, .variant _ _, _, _, h
    | .bool, .nominal _, _, _, h
    | .nat, .bool, _, _, h | .nat, .fin _, _, _, h | .nat, .seq _ _, _, _, h
    | .nat, .tuple _, _, _, h | .nat, .record _ _ _, _, _, h | .nat, .variant _ _, _, _, h
    | .nat, .nominal _, _, _, h
    | .fin _, .bool, _, _, h | .fin _, .nat, _, _, h | .fin _, .seq _ _, _, _, h
    | .fin _, .tuple _, _, _, h | .fin _, .record _ _ _, _, _, h | .fin _, .variant _ _, _, _, h
    | .fin _, .nominal _, _, _, h
    | .seq _ _, .bool, _, _, h | .seq _ _, .nat, _, _, h | .seq _ _, .fin _, _, _, h
    | .seq _ _, .tuple _, _, _, h | .seq _ _, .record _ _ _, _, _, h | .seq _ _, .variant _ _, _, _, h
    | .seq _ _, .nominal _, _, _, h
    | .tuple _, .bool, _, _, h | .tuple _, .nat, _, _, h | .tuple _, .fin _, _, _, h
    | .tuple _, .seq _ _, _, _, h | .tuple _, .record _ _ _, _, _, h | .tuple _, .variant _ _, _, _, h
    | .tuple _, .nominal _, _, _, h
    | .record _ _ _, .bool, _, _, h | .record _ _ _, .nat, _, _, h | .record _ _ _, .fin _, _, _, h
    | .record _ _ _, .seq _ _, _, _, h | .record _ _ _, .tuple _, _, _, h | .record _ _ _, .variant _ _, _, _, h
    | .record _ _ _, .nominal _, _, _, h
    | .variant _ _, .bool, _, _, h | .variant _ _, .nat, _, _, h | .variant _ _, .fin _, _, _, h
    | .variant _ _, .seq _ _, _, _, h | .variant _ _, .tuple _, _, _, h | .variant _ _, .record _ _ _, _, _, h
    | .variant _ _, .nominal _, _, _, h
    | .nominal _, .bool, _, _, h | .nominal _, .nat, _, _, h | .nominal _, .fin _, _, _, h
    | .nominal _, .seq _ _, _, _, h | .nominal _, .tuple _, _, _, h | .nominal _, .record _ _ _, _, _, h
    | .nominal _, .variant _ _, _, _, h => by simp [encodeTyWith] at h

  theorem encodeTysWith_prefixFree {K : Type} {encKey : K → List Nat}
      (hKey : PrefixFree encKey) : ∀ (a b : Core.Tys K) (r₁ r₂ : List Nat),
      encodeTysWith encKey a ++ r₁ = encodeTysWith encKey b ++ r₂ → a = b ∧ r₁ = r₂
    | .nil, .nil, r₁, r₂, h => by
        simp only [encodeTysWith, List.cons_append, List.nil_append, List.cons.injEq] at h
        exact ⟨rfl, h.2⟩
    | .cons h₁ t₁, .cons h₂ t₂, r₁, r₂, h => by
        simp only [encodeTysWith, List.cons_append, List.append_assoc, List.cons.injEq] at h
        obtain ⟨hh, hrest⟩ := encodeTyWith_prefixFree hKey h₁ h₂ _ _ h.2
        obtain ⟨ht, hr⟩ := encodeTysWith_prefixFree hKey t₁ t₂ r₁ r₂ hrest
        exact ⟨by rw [hh, ht], hr⟩
    | .nil, .cons _ _, _, _, h => by simp [encodeTysWith] at h
    | .cons _ _, .nil, _, _, h => by simp [encodeTysWith] at h
end

/-- Prefix-free canonical byte encoding of a `Core.Ty TypeKey` over `Zkc.Vocabulary.standard`. -/
def encodeStandardTy : Core.Ty TypeKey → List Nat := encodeTyWith encodeTypeKey

/-- Prefix-free canonical byte encoding of a `Core.Tys TypeKey` over `Zkc.Vocabulary.standard`. -/
def encodeStandardTys : Core.Tys TypeKey → List Nat := encodeTysWith encodeTypeKey

theorem encodeStandardTy_bytes (τ : Core.Ty TypeKey) : ∀ b, b ∈ encodeStandardTy τ → b < 256 :=
  encodeTyWith_bytes encodeTypeKey_bytes τ

theorem encodeStandardTys_bytes (ts : Core.Tys TypeKey) : ∀ b, b ∈ encodeStandardTys ts → b < 256 :=
  encodeTysWith_bytes encodeTypeKey_bytes ts

theorem encodeStandardTy_prefixFree : PrefixFree encodeStandardTy :=
  encodeTyWith_prefixFree encodeTypeKey_prefixFree

theorem encodeStandardTys_prefixFree : PrefixFree encodeStandardTys :=
  encodeTysWith_prefixFree encodeTypeKey_prefixFree

def encodeLawKey : LawKey → List Nat
  | .uniform τ => 0 :: encodeStandardTy τ

theorem encodeLawKey_bytes : ∀ k b, b ∈ encodeLawKey k → b < 256
  | .uniform τ, b, h => cons_tag_bytes (by decide) (encodeStandardTy_bytes τ) b h

theorem encodeLawKey_prefixFree : PrefixFree encodeLawKey := by
  intro a b r₁ r₂ h
  cases a with
  | uniform τ₁ =>
      cases b with
      | uniform τ₂ =>
          simp only [encodeLawKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hτ, hr⟩ := encodeStandardTy_prefixFree τ₁ τ₂ r₁ r₂ h.2
          exact ⟨congrArg LawKey.uniform hτ, hr⟩

/-- Canonical injective vocabulary encoder for `Zkc.Vocabulary.standard`. -/
def standardEncoder : VocabEncoder standard where
  typeKey := encodeTypeKey
  rowKey := encodeRowKey
  lawKey := encodeLawKey

theorem standardEncoder_injective : standardEncoder.Injective := by
  refine ⟨?_, ?_, ?_⟩
  · intro k₁ k₂ h
    exact (encodeTypeKey_prefixFree k₁ k₂ [] [] (by simpa [standardEncoder] using h)).1
  · intro k₁ k₂ h
    exact (encodeRowKey_prefixFree k₁ k₂ [] [] (by simpa [standardEncoder] using h)).1
  · intro k₁ k₂ h
    exact (encodeLawKey_prefixFree k₁ k₂ [] [] (by simpa [standardEncoder] using h)).1

theorem standardEncoder_bytes :
    (∀ k b, b ∈ standardEncoder.typeKey k → b < 256) ∧
    (∀ k b, b ∈ standardEncoder.rowKey k → b < 256) ∧
    (∀ k b, b ∈ standardEncoder.lawKey k → b < 256) :=
  ⟨encodeTypeKey_bytes, encodeRowKey_bytes, encodeLawKey_bytes⟩

/-! ## Project-linked vocabulary encoders (`Project.Bindings.vocabulary`) -/

/-- Canonical length-prefixed UTF-8 byte encoding of a string (strictly axiom-clean: avoids
`String.toList`). -/
def encodeString (s : String) : List Nat :=
  encodeList encodeNat (s.toByteArray.data.toList.map UInt8.toNat)

theorem encodeString_bytes (s : String) : ∀ b, b ∈ encodeString s → b < 256 :=
  encodeList_bytes encodeNat encodeNat_bytes (s.toByteArray.data.toList.map UInt8.toNat)

private theorem list_map_uint8_toNat_inj : ∀ {xs ys : List UInt8},
    xs.map UInt8.toNat = ys.map UInt8.toNat → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      have hxy : x = y := by
        cases x with
        | ofBitVec bx =>
            cases y with
            | ofBitVec by_ =>
                exact congrArg UInt8.ofBitVec (BitVec.eq_of_toNat_eq h.1)
      rw [hxy, list_map_uint8_toNat_inj h.2]

theorem encodeString_prefixFree : PrefixFree encodeString := by
  intro s₁ s₂ r₁ r₂ h
  obtain ⟨hlist, hr⟩ := encodeList_prefixFree encodeNat_prefixFree
    (s₁.toByteArray.data.toList.map UInt8.toNat) (s₂.toByteArray.data.toList.map UInt8.toNat) r₁ r₂ h
  have hbytes : s₁.toByteArray.data.toList = s₂.toByteArray.data.toList :=
    list_map_uint8_toNat_inj hlist
  have hba : s₁.toByteArray = s₂.toByteArray := by
    cases h₁ : s₁.toByteArray with
    | mk d₁ =>
        cases h₂ : s₂.toByteArray with
        | mk d₂ =>
            rw [h₁, h₂] at hbytes
            exact congrArg ByteArray.mk (Array.toList_inj.mp hbytes)
  have hs : s₁ = s₂ := by
    cases s₁ with
    | ofByteArray ba₁ _ =>
        cases s₂ with
        | ofByteArray ba₂ _ =>
            dsimp only at hba
            subst hba
            rfl
  exact ⟨hs, hr⟩

namespace Project

def encodeTypeHead : TypeHead → List Nat
  | .bool => [0]
  | .nat => [1]
  | .rational => [2]
  | .index bound => 3 :: encodeNat bound
  | .nonzero => [4]
  | .seq size => 5 :: encodeOption encodeNat size
  | .tuple => [6]
  | .nominal row => 7 :: encodeString row
  | .record inst => 8 :: encodeNat inst
  | .variant inst => 9 :: encodeNat inst
  | .specification inst => 10 :: encodeNat inst
  | .opaqueMember inst member => 11 :: encodeNat inst ++ encodeString member

theorem encodeTypeHead_bytes : ∀ h b, b ∈ encodeTypeHead h → b < 256
  | .bool, b, hb => singleton_tag_bytes 0 (by decide) b hb
  | .nat, b, hb => singleton_tag_bytes 1 (by decide) b hb
  | .rational, b, hb => singleton_tag_bytes 2 (by decide) b hb
  | .index n, b, hb => cons_tag_bytes (by decide) (encodeNat_bytes n) b hb
  | .nonzero, b, hb => singleton_tag_bytes 4 (by decide) b hb
  | .seq s, b, hb => cons_tag_bytes (by decide) (encodeOption_bytes encodeNat encodeNat_bytes s) b hb
  | .tuple, b, hb => singleton_tag_bytes 6 (by decide) b hb
  | .nominal s, b, hb => cons_tag_bytes (by decide) (encodeString_bytes s) b hb
  | .record n, b, hb => cons_tag_bytes (by decide) (encodeNat_bytes n) b hb
  | .variant n, b, hb => cons_tag_bytes (by decide) (encodeNat_bytes n) b hb
  | .specification n, b, hb => cons_tag_bytes (by decide) (encodeNat_bytes n) b hb
  | .opaqueMember n s, b, hb =>
      cons_tag_bytes (by decide) (append_bytes (encodeNat_bytes n) (encodeString_bytes s)) b hb

theorem encodeTypeHead_prefixFree : PrefixFree encodeTypeHead := by
  intro a b r₁ r₂ h
  cases a with
  | bool =>
      cases b <;> simp only [encodeTypeHead, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
        first | exact ⟨rfl, h.2⟩ | (cases h.1)
  | nat =>
      cases b <;> simp only [encodeTypeHead, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
        first | exact ⟨rfl, h.2⟩ | (cases h.1)
  | rational =>
      cases b <;> simp only [encodeTypeHead, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
        first | exact ⟨rfl, h.2⟩ | (cases h.1)
  | index n₁ =>
      cases b with
      | index n₂ =>
          simp only [encodeTypeHead, List.cons_append, List.cons.injEq] at h
          obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ h.2
          exact ⟨congrArg TypeHead.index hn, hr⟩
      | _ => simp [encodeTypeHead] at h
  | nonzero =>
      cases b <;> simp only [encodeTypeHead, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
        first | exact ⟨rfl, h.2⟩ | (cases h.1)
  | seq s₁ =>
      cases b with
      | seq s₂ =>
          simp only [encodeTypeHead, List.cons_append, List.cons.injEq] at h
          obtain ⟨hs, hr⟩ := encodeOption_prefixFree encodeNat_prefixFree s₁ s₂ r₁ r₂ h.2
          exact ⟨congrArg TypeHead.seq hs, hr⟩
      | _ => simp [encodeTypeHead] at h
  | tuple =>
      cases b <;> simp only [encodeTypeHead, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
        first | exact ⟨rfl, h.2⟩ | (cases h.1)
  | nominal s₁ =>
      cases b with
      | nominal s₂ =>
          simp only [encodeTypeHead, List.cons_append, List.cons.injEq] at h
          obtain ⟨hs, hr⟩ := encodeString_prefixFree s₁ s₂ r₁ r₂ h.2
          exact ⟨congrArg TypeHead.nominal hs, hr⟩
      | _ => simp [encodeTypeHead] at h
  | record n₁ =>
      cases b with
      | record n₂ =>
          simp only [encodeTypeHead, List.cons_append, List.cons.injEq] at h
          obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ h.2
          exact ⟨congrArg TypeHead.record hn, hr⟩
      | _ => simp [encodeTypeHead] at h
  | variant n₁ =>
      cases b with
      | variant n₂ =>
          simp only [encodeTypeHead, List.cons_append, List.cons.injEq] at h
          obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ h.2
          exact ⟨congrArg TypeHead.variant hn, hr⟩
      | _ => simp [encodeTypeHead] at h
  | specification n₁ =>
      cases b with
      | specification n₂ =>
          simp only [encodeTypeHead, List.cons_append, List.cons.injEq] at h
          obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ h.2
          exact ⟨congrArg TypeHead.specification hn, hr⟩
      | _ => simp [encodeTypeHead] at h
  | opaqueMember n₁ m₁ =>
      cases b with
      | opaqueMember n₂ m₂ =>
          simp only [encodeTypeHead, List.cons_append, List.append_assoc, List.cons.injEq] at h
          obtain ⟨hn, hrest⟩ := encodeNat_prefixFree n₁ n₂ _ _ h.2
          obtain ⟨hm, hr⟩ := encodeString_prefixFree m₁ m₂ r₁ r₂ hrest
          exact ⟨by rw [hn, hm], hr⟩
      | _ => simp [encodeTypeHead] at h

mutual
  def encodeParameter : Parameter → List Nat
    | .natural v => 0 :: encodeNat v
    | .moduleRef inst => 1 :: encodeNat inst
    | .type head args => 2 :: encodeTypeHead head ++ encodeParameters args

  def encodeParameters : Parameters → List Nat
    | .nil => [0]
    | .cons head tail => 1 :: encodeParameter head ++ encodeParameters tail
end

mutual
  theorem encodeParameter_bytes : ∀ p b, b ∈ encodeParameter p → b < 256
    | .natural v, b, h => cons_tag_bytes (by decide) (encodeNat_bytes v) b h
    | .moduleRef inst, b, h => cons_tag_bytes (by decide) (encodeNat_bytes inst) b h
    | .type head args, b, h =>
        cons_tag_bytes (by decide)
          (append_bytes (encodeTypeHead_bytes head) (encodeParameters_bytes args)) b h

  theorem encodeParameters_bytes : ∀ ps b, b ∈ encodeParameters ps → b < 256
    | .nil, b, h => singleton_tag_bytes 0 (by decide) b h
    | .cons head tail, b, h =>
        cons_tag_bytes (by decide)
          (append_bytes (encodeParameter_bytes head) (encodeParameters_bytes tail)) b h
end

mutual
  theorem encodeParameter_prefixFree : ∀ (a b : Parameter) (r₁ r₂ : List Nat),
      encodeParameter a ++ r₁ = encodeParameter b ++ r₂ → a = b ∧ r₁ = r₂
    | .natural v₁, .natural v₂, r₁, r₂, h => by
        simp only [encodeParameter, List.cons_append, List.cons.injEq] at h
        obtain ⟨hv, hr⟩ := encodeNat_prefixFree v₁ v₂ r₁ r₂ h.2
        exact ⟨congrArg Parameter.natural hv, hr⟩
    | .moduleRef i₁, .moduleRef i₂, r₁, r₂, h => by
        simp only [encodeParameter, List.cons_append, List.cons.injEq] at h
        obtain ⟨hi, hr⟩ := encodeNat_prefixFree i₁ i₂ r₁ r₂ h.2
        exact ⟨congrArg Parameter.moduleRef hi, hr⟩
    | .type h₁ a₁, .type h₂ a₂, r₁, r₂, h => by
        simp only [encodeParameter, List.cons_append, List.append_assoc, List.cons.injEq] at h
        obtain ⟨hh, hrest⟩ := encodeTypeHead_prefixFree h₁ h₂ _ _ h.2
        obtain ⟨ha, hr⟩ := encodeParameters_prefixFree a₁ a₂ r₁ r₂ hrest
        exact ⟨by rw [hh, ha], hr⟩
    | .natural _, .moduleRef _, _, _, h => by simp [encodeParameter] at h
    | .natural _, .type _ _, _, _, h => by simp [encodeParameter] at h
    | .moduleRef _, .natural _, _, _, h => by simp [encodeParameter] at h
    | .moduleRef _, .type _ _, _, _, h => by simp [encodeParameter] at h
    | .type _ _, .natural _, _, _, h => by simp [encodeParameter] at h
    | .type _ _, .moduleRef _, _, _, h => by simp [encodeParameter] at h

  theorem encodeParameters_prefixFree : ∀ (a b : Parameters) (r₁ r₂ : List Nat),
      encodeParameters a ++ r₁ = encodeParameters b ++ r₂ → a = b ∧ r₁ = r₂
    | .nil, .nil, r₁, r₂, h => by
        simp only [encodeParameters, List.cons_append, List.nil_append, List.cons.injEq] at h
        exact ⟨rfl, h.2⟩
    | .cons h₁ t₁, .cons h₂ t₂, r₁, r₂, h => by
        simp only [encodeParameters, List.cons_append, List.append_assoc, List.cons.injEq] at h
        obtain ⟨hh, hrest⟩ := encodeParameter_prefixFree h₁ h₂ _ _ h.2
        obtain ⟨ht, hr⟩ := encodeParameters_prefixFree t₁ t₂ r₁ r₂ hrest
        exact ⟨by rw [hh, ht], hr⟩
    | .nil, .cons _ _, _, _, h => by simp [encodeParameters] at h
    | .cons _ _, .nil, _, _, h => by simp [encodeParameters] at h
end

def encodePrimitiveName (p : PrimitiveName) : List Nat :=
  encodeString p.name ++ encodeParameters p.arguments

theorem encodePrimitiveName_bytes (p : PrimitiveName) :
    ∀ b, b ∈ encodePrimitiveName p → b < 256 :=
  append_bytes (encodeString_bytes p.name) (encodeParameters_bytes p.arguments)

theorem encodePrimitiveName_prefixFree : PrefixFree encodePrimitiveName := by
  intro ⟨n₁, a₁⟩ ⟨n₂, a₂⟩ r₁ r₂ h
  simp only [encodePrimitiveName, List.append_assoc] at h
  obtain ⟨hn, hrest⟩ := encodeString_prefixFree n₁ n₂ _ _ h
  obtain ⟨ha, hr⟩ := encodeParameters_prefixFree a₁ a₂ r₁ r₂ hrest
  exact ⟨by rw [hn, ha], hr⟩

def encodeLinkedTypeKey : Sum TypeKey Parameter → List Nat
  | .inl k => 0 :: encodeTypeKey k
  | .inr p => 1 :: encodeParameter p

theorem encodeLinkedTypeKey_bytes : ∀ k b, b ∈ encodeLinkedTypeKey k → b < 256
  | .inl k, b, h => cons_tag_bytes (by decide) (encodeTypeKey_bytes k) b h
  | .inr p, b, h => cons_tag_bytes (by decide) (encodeParameter_bytes p) b h

theorem encodeLinkedTypeKey_prefixFree : PrefixFree encodeLinkedTypeKey := by
  intro a b r₁ r₂ h
  cases a with
  | inl k₁ =>
      cases b with
      | inl k₂ =>
          simp only [encodeLinkedTypeKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hk, hr⟩ := encodeTypeKey_prefixFree k₁ k₂ r₁ r₂ h.2
          exact ⟨congrArg Sum.inl hk, hr⟩
      | inr _ => simp [encodeLinkedTypeKey] at h
  | inr p₁ =>
      cases b with
      | inl _ => simp [encodeLinkedTypeKey] at h
      | inr p₂ =>
          simp only [encodeLinkedTypeKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hp, hr⟩ := encodeParameter_prefixFree p₁ p₂ r₁ r₂ h.2
          exact ⟨congrArg Sum.inr hp, hr⟩

/-- Prefix-free canonical byte encoding of a `LinkedType`. -/
def encodeLinkedTy : LinkedType → List Nat := encodeTyWith encodeLinkedTypeKey

theorem encodeLinkedTy_bytes (τ : LinkedType) : ∀ c, c ∈ encodeLinkedTy τ → c < 256 :=
  encodeTyWith_bytes encodeLinkedTypeKey_bytes τ

theorem encodeLinkedTy_prefixFree : PrefixFree encodeLinkedTy :=
  encodeTyWith_prefixFree encodeLinkedTypeKey_prefixFree

/-- Prefix-free canonical byte encoding of a project `PrimitiveSignature` (`inputs` and `outputs`). -/
def encodePrimitiveSignature (sig : PrimitiveSignature) : List Nat :=
  encodeList encodeLinkedTy sig.inputs ++ encodeList encodeLinkedTy sig.outputs

theorem encodePrimitiveSignature_bytes (sig : PrimitiveSignature) :
    ∀ c, c ∈ encodePrimitiveSignature sig → c < 256 :=
  append_bytes
    (encodeList_bytes encodeLinkedTy encodeLinkedTy_bytes sig.inputs)
    (encodeList_bytes encodeLinkedTy encodeLinkedTy_bytes sig.outputs)

theorem encodePrimitiveSignature_prefixFree : PrefixFree encodePrimitiveSignature := by
  intro ⟨in₁, out₁⟩ ⟨in₂, out₂⟩ r₁ r₂ h
  simp only [encodePrimitiveSignature, List.append_assoc] at h
  obtain ⟨hin, hrest⟩ := encodeList_prefixFree encodeLinkedTy_prefixFree in₁ in₂ _ _ h
  obtain ⟨hout, hr⟩ := encodeList_prefixFree encodeLinkedTy_prefixFree out₁ out₂ r₁ r₂ hrest
  exact ⟨by rw [hin, hout], hr⟩

/-- Prefix-free canonical byte encoding of a linked row key, binding both the `PrimitiveName`
and its bound `PrimitiveSignature` in `b` so two projects binding the same primitive spelling
to different signatures never share a canonical row encoding. -/
def encodeLinkedRowKey (b : Bindings) : Sum RowKey PrimitiveName → List Nat
  | .inl k => 0 :: encodeRowKey k
  | .inr p => 1 :: encodePrimitiveName p ++ encodeOption encodePrimitiveSignature (b.signature p)

theorem encodeLinkedRowKey_bytes (b : Bindings) :
    ∀ k c, c ∈ encodeLinkedRowKey b k → c < 256
  | .inl k, c, h => cons_tag_bytes (by decide) (encodeRowKey_bytes k) c h
  | .inr p, c, h =>
      cons_tag_bytes (by decide)
        (append_bytes (encodePrimitiveName_bytes p)
          (encodeOption_bytes encodePrimitiveSignature encodePrimitiveSignature_bytes (b.signature p))) c h

theorem encodeLinkedRowKey_prefixFree (b : Bindings) : PrefixFree (encodeLinkedRowKey b) := by
  intro a c r₁ r₂ h
  cases a with
  | inl k₁ =>
      cases c with
      | inl k₂ =>
          simp only [encodeLinkedRowKey, List.cons_append, List.cons.injEq] at h
          obtain ⟨hk, hr⟩ := encodeRowKey_prefixFree k₁ k₂ r₁ r₂ h.2
          exact ⟨congrArg Sum.inl hk, hr⟩
      | inr _ => simp [encodeLinkedRowKey] at h
  | inr p₁ =>
      cases c with
      | inl _ => simp [encodeLinkedRowKey] at h
      | inr p₂ =>
          simp only [encodeLinkedRowKey, List.cons_append, List.append_assoc, List.cons.injEq] at h
          obtain ⟨hp, hrest⟩ := encodePrimitiveName_prefixFree p₁ p₂ _ _ h.2
          obtain ⟨_, hr⟩ := encodeOption_prefixFree encodePrimitiveSignature_prefixFree
            (b.signature p₁) (b.signature p₂) r₁ r₂ hrest
          exact ⟨congrArg Sum.inr hp, hr⟩

/-- Canonical injective vocabulary encoder for any project-linked vocabulary `b.vocabulary`.
Commits every project row's bound `PrimitiveSignature` in `b` alongside its `PrimitiveName`. -/
def linkedEncoder (b : Bindings) : VocabEncoder b.vocabulary where
  typeKey := encodeLinkedTypeKey
  rowKey := encodeLinkedRowKey b
  lawKey := encodeLawKey

theorem linkedEncoder_injective (b : Bindings) : (linkedEncoder b).Injective := by
  refine ⟨?_, ?_, ?_⟩
  · intro k₁ k₂ h
    exact (encodeLinkedTypeKey_prefixFree k₁ k₂ [] [] (by simpa [linkedEncoder] using h)).1
  · intro k₁ k₂ h
    exact (encodeLinkedRowKey_prefixFree b k₁ k₂ [] [] (by simpa [linkedEncoder] using h)).1
  · intro k₁ k₂ h
    exact (encodeLawKey_prefixFree k₁ k₂ [] [] (by simpa [linkedEncoder] using h)).1

/-- Two project bindings assigning different signatures to the same `PrimitiveName` always
receive distinct canonical row encodings under `linkedEncoder`. -/
theorem linkedEncoder_signature_distinguishes (b₁ b₂ : Bindings) (p : PrimitiveName)
    (hEq : (linkedEncoder b₁).rowKey (.inr p) = (linkedEncoder b₂).rowKey (.inr p)) :
    b₁.signature p = b₂.signature p := by
  have h : encodeLinkedRowKey b₁ (.inr p) ++ [] = encodeLinkedRowKey b₂ (.inr p) ++ [] := by
    simpa [linkedEncoder] using hEq
  simp only [encodeLinkedRowKey, List.cons_append, List.append_assoc, List.cons.injEq] at h
  obtain ⟨_, hrest⟩ := encodePrimitiveName_prefixFree p p _ _ h.2
  exact (encodeOption_prefixFree encodePrimitiveSignature_prefixFree
    (b₁.signature p) (b₂.signature p) [] [] hrest).1

theorem linkedEncoder_bytes (b : Bindings) :
    (∀ k c, c ∈ (linkedEncoder b).typeKey k → c < 256) ∧
    (∀ k c, c ∈ (linkedEncoder b).rowKey k → c < 256) ∧
    (∀ k c, c ∈ (linkedEncoder b).lawKey k → c < 256) :=
  ⟨encodeLinkedTypeKey_bytes, encodeLinkedRowKey_bytes b, encodeLawKey_bytes⟩

end Project

end Zkc.Vocabulary
