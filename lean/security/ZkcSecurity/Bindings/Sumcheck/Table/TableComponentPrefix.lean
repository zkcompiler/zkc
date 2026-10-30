module

public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponent

@[expose] public section

/-! Prefix representation shared by actual table callers.

The immutable original table, ordered challenge prefix, current scalar and
arbitrary caller frame are retained together. The exact shape is independent
of the scalar claim. Restriction is the existing core list operation; it does
not use a second table evaluator or assume honest received endpoints.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F Frame : Type} [Field F]

structure PrefixState (F Frame : Type) [Field F] (remaining : Nat) where
  original : List F
  point : List F
  scalar : F
  frame : Frame
  shape : original.length = 2 ^ (remaining + point.length)

namespace PrefixState

def entries {n : Nat} (state : PrefixState F Frame n) : List F :=
  restrictPrefixValues state.original state.point

theorem entries_shape {n : Nat} (state : PrefixState F Frame n) :
    state.entries.length = 2 ^ n :=
  restrictPrefixValues_length state.original state.point state.shape

/-- Every field challenge and every received endpoint pair has a defined
representation update, regardless of whether its boundary passes. -/
noncomputable def advance {n : Nat} (state : PrefixState F Frame (n + 1))
    (message : F × F) (challenge : F) : PrefixState F Frame n where
  original := state.original
  point := state.point ++ [challenge]
  scalar := (Message.endpoints F).evaluate message challenge
  frame := state.frame
  shape := by
    rw [List.length_append, List.length_singleton,
      show n + (state.point.length + 1) = n + 1 + state.point.length by omega]
    exact state.shape

theorem advance_entries {n : Nat} (state : PrefixState F Frame (n + 1))
    (message : F × F) (challenge : F) :
    (state.advance message challenge).entries = restrictValues state.entries challenge := by
  exact restrictPrefixValues_append state.original state.point [challenge]

theorem advance_frame {n : Nat} (state : PrefixState F Frame (n + 1))
    (message : F × F) (challenge : F) :
    (state.advance message challenge).frame = state.frame := rfl

theorem advance_point {n : Nat} (state : PrefixState F Frame (n + 1))
    (message : F × F) (challenge : F) :
    (state.advance message challenge).point = state.point ++ [challenge] := rfl

def initial (original : List F) (count : Nat) (scalar : F) (frame : Frame)
    (shape : original.length = 2 ^ count) : PrefixState F Frame count :=
  ⟨original, [], scalar, frame, by simpa using shape⟩

theorem initial_entries (original : List F) (count : Nat) (scalar : F) (frame : Frame)
    (shape : original.length = 2 ^ count) :
    (initial original count scalar frame shape).entries = original := rfl

/-- The terminal comparison is the original table's MLE at the actual complete
challenge prefix. This is separate from successful producer execution. -/
theorem terminal_total (state : PrefixState F Frame 0)
    (table : Table F (0 + state.point.length))
    (decoded : ofList? (0 + state.point.length) state.original = some table) :
    state.entries.sum =
      extension (0 + state.point.length) table (coordinates (0 + state.point.length) state.point) :=
  complete_prefix_sum state.original state.point table decoded

end PrefixState
end ZkcSecurity.Families.Sumcheck.TableComponent
