import Mathlib.Data.List.TakeDrop

/-!
# Immutable buffer publication

A reference model for the native buffer boundary. Packed offsets and separate
logical buffers have the same observations after publication; old aliases are
framed by a bounds invariant. The segmented runtime may place several buffers
in one reservation segment. This model forgets that placement and capacity.
It does not verify Rust allocation, issuer uniqueness, pointers or reservation.
-/

namespace Examples.BufferStorage

variable {α : Type}

structure Span where
  start : Nat
  size : Nat

def Span.Valid (span : Span) (cells : List α) : Prop :=
  span.start + span.size ≤ cells.length

def Span.read (span : Span) (cells : List α) : List α :=
  (cells.drop span.start).take span.size

/-- In-bounds old buffers cannot read newly appended cells. Without the bounds
hypothesis, list slicing can silently expose cells from a later publication. -/
theorem Span.read_append (span : Span) (cells extra : List α)
    (h : span.Valid cells) : span.read (cells ++ extra) = span.read cells := by
  unfold Span.Valid at h
  unfold Span.read
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
  simp only [List.length_drop]
  omega

structure Packed (α : Type) where
  cells : List α
  spans : List Span

def Packed.Valid (store : Packed α) : Prop :=
  ∀ span ∈ store.spans, span.Valid store.cells

def Packed.read (store : Packed α) (reference : Nat) : Option (List α) :=
  store.spans[reference]?.map (fun span => span.read store.cells)

def Packed.publish (store : Packed α) (values : List α) : Packed α :=
  ⟨store.cells ++ values, store.spans ++ [⟨store.cells.length, values.length⟩]⟩

theorem Packed.publish_valid (store : Packed α) (values : List α) (h : store.Valid) :
    (store.publish values).Valid := by
  intro span hs
  simp only [Packed.publish, List.mem_append, List.mem_singleton] at hs
  rcases hs with hs | rfl
  · have bound := h span hs
    simp only [Span.Valid, Packed.publish, List.length_append] at *
    omega
  · simp [Span.Valid, Packed.publish]

theorem Packed.read_publish_old (store : Packed α) (values : List α)
    (h : store.Valid) (i : Nat) (hi : i < store.spans.length) :
    (store.publish values).read i = store.read i := by
  simp only [Packed.read, Packed.publish, List.getElem?_append_left hi,
    List.getElem?_eq_getElem hi, Option.map_some]
  exact congrArg some (Span.read_append _ _ _ (h _ (List.getElem_mem hi)))

theorem Packed.read_publish_new (store : Packed α) (values : List α) :
    (store.publish values).read store.spans.length = some values := by
  simp [Packed.read, Packed.publish, Span.read]

/-- Equality of all reads, including missing references, and the next issued
reference. `buffers` forgets packing while preserving every complete buffer. -/
def Represents (store : Packed α) (buffers : List (List α)) : Prop :=
  store.Valid ∧ store.spans.length = buffers.length ∧ ∀ i, store.read i = buffers[i]?

theorem empty_represents : Represents (Packed.mk [] [] : Packed α) [] := by
  simp [Represents, Packed.Valid, Packed.read]

theorem publish_represents (store : Packed α) (buffers : List (List α))
    (h : Represents store buffers) (values : List α) :
    Represents (store.publish values) (buffers ++ [values]) := by
  have hlength := h.2.1
  refine ⟨store.publish_valid values h.1, by simpa [Packed.publish] using h.2.1, ?_⟩
  intro i
  by_cases hi : i < store.spans.length
  · rw [store.read_publish_old values h.1 i hi, h.2.2 i,
      List.getElem?_append_left (by omega)]
  · by_cases heq : i = store.spans.length
    · subst i
      rw [store.read_publish_new]
      simp [h.2.1]
    · have hp : (store.publish values).spans.length ≤ i := by
        simp only [Packed.publish, List.length_append, List.length_singleton]
        omega
      have hb : (buffers ++ [values]).length ≤ i := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp [Packed.read, List.getElem?_eq_none hp, List.getElem?_eq_none hb]

/-- Repeated publication preserves correspondence for arbitrary payloads and
all references, not just the newly returned buffer or a fixed finite corpus. -/
theorem publish_many_represents (store : Packed α) (buffers batches : List (List α))
    (h : Represents store buffers) :
    Represents (batches.foldl Packed.publish store) (buffers ++ batches) := by
  induction batches generalizing store buffers with
  | nil => simpa using h
  | cons values rest ih =>
    simpa [List.foldl, List.append_assoc] using
      ih (store.publish values) (buffers ++ [values]) (publish_represents store buffers h values)

end Examples.BufferStorage
