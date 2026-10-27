module

public import Zkc.Polynomial.Multilinear.Embedding
public import ZkcSecurity.Families.Sumcheck.TableComponentPrefix

@[expose] public section

/-! A base table with an extension-field challenge prefix. The verifier's
runtime need only carry a scalar, prefix and handle; `original` is a logical
readback, not permission to inspect the prover's table. Exact shape is part of
this dimension-indexed family. Raw roots must reject malformed inputs. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.EmbeddingPrefix
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {B E Frame : Type} [Field B] [Field E]

@[ext] structure State (B E Frame : Type) (remaining : Nat) where
  original : List B
  point : List E
  scalar : E
  frame : Frame
  shape : original.length = 2 ^ (remaining + point.length)

namespace State

def toPrefix (embedding : B →+* E) {n : Nat} (state : State B E Frame n) :
    TableComponent.PrefixState E Frame n :=
  ⟨state.original.map embedding, state.point, state.scalar, state.frame,
    by simpa only [List.length_map] using state.shape⟩

def entries (embedding : B →+* E) {n : Nat} (state : State B E Frame n) : List E :=
  (state.toPrefix embedding).entries

theorem entries_shape (embedding : B →+* E) {n : Nat} (state : State B E Frame n) :
    (state.entries embedding).length = 2 ^ n := (state.toPrefix embedding).entries_shape

noncomputable def advance {n : Nat} (state : State B E Frame (n + 1))
    (message : E × E) (challenge : E) : State B E Frame n where
  original := state.original
  point := state.point ++ [challenge]
  scalar := (Message.endpoints E).evaluate message challenge
  frame := state.frame
  shape := by
    rw [List.length_append, List.length_singleton,
      show n + (state.point.length + 1) = n + 1 + state.point.length by omega]
    exact state.shape

theorem toPrefix_advance (embedding : B →+* E) {n : Nat} (state : State B E Frame (n + 1))
    (message : E × E) (challenge : E) :
    (state.advance message challenge).toPrefix embedding =
      (state.toPrefix embedding).advance message challenge := rfl

omit [Field B] in
/-- An affine source result and its returned coin determine the complete
logical update. No endpoint values need to be recovered from the result. -/
theorem readback_advance {n : Nat} (state : State B E Frame (n + 1))
    (low high challenge : E) :
    { state.advance (0, 0) challenge with scalar := low + (high - low) * challenge } =
      state.advance (low, high) challenge := by
  apply State.ext <;> try rfl
  change low + (high - low) * challenge = (1 - challenge) * low + challenge * high
  ring

/-- This update square holds for every received message and every extension
challenge. Initial pointwise agreement would not suffice. -/
theorem advance_entries (embedding : B →+* E) {n : Nat} (state : State B E Frame (n + 1))
    (message : E × E) (challenge : E) :
    (state.advance message challenge).entries embedding =
      restrictValues (state.entries embedding) challenge :=
  (state.toPrefix embedding).advance_entries message challenge

def initial (original : List B) (n : Nat) (scalar : E) (frame : Frame)
    (shape : original.length = 2 ^ n) : State B E Frame n :=
  ⟨original, [], scalar, frame, by simpa using shape⟩

theorem initial_sum (embedding : B →+* E) (original : List B) (n : Nat) (scalar : E)
    (frame : Frame) (shape : original.length = 2 ^ n) :
    ((initial original n scalar frame shape).entries embedding).sum = embedding original.sum := by
  change (original.map embedding).sum = embedding original.sum
  exact (map_list_sum embedding original).symm

/-- The readback really evaluates the embedded base table at the extension
point, rather than a coerced base-field evaluation at nonexistent base coins. -/
theorem terminal_total (embedding : B →+* E) (state : State B E Frame 0)
    (table : Table B (0 + state.point.length))
    (decoded : ofList? (0 + state.point.length) state.original = some table) :
    (state.entries embedding).sum =
      extension (0 + state.point.length) (Embedding.table embedding table)
        (coordinates (0 + state.point.length) state.point) :=
  (state.toPrefix embedding).terminal_total _ (Embedding.ofList? embedding _ _ decoded)

end State
end ZkcSecurity.Families.Sumcheck.EmbeddingPrefix
