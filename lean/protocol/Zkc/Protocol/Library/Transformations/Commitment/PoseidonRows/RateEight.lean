module

public import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.DirectExtraction

@[expose] public section

/-! # Rate-eight coordinates and the untagged one-call specialization

The native instance uses sixteen base coordinates, split rate/capacity in ascending order.
Extension rows flatten each element's ascending basis coordinates before the next element.
These equations fix representation; they do not prove the Rust codec or field implementation.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {F : Type}

def flattenState (state : State F 8) : Fin 16 → F := fun i ↦
  if below : i.val < 8 then state.1 ⟨i.val, below⟩
  else state.2 ⟨i.val - 8, by omega⟩

def splitState (state : Fin 16 → F) : State F 8 :=
  (fun i ↦ state ⟨i.val, by omega⟩, fun i ↦ state ⟨i.val + 8, by omega⟩)

theorem split_flatten (state : State F 8) : splitState (flattenState state) = state := by
  apply Prod.ext <;> funext i
  · simp [splitState, flattenState]
  · simp [splitState, flattenState]

theorem flatten_split (state : Fin 16 → F) : flattenState (splitState state) = state := by
  funext i
  unfold flattenState
  split
  · rfl
  · simp only [splitState]
    congr 1
    apply Fin.ext
    change i.val - 8 + 8 = i.val
    omega

/-- Each extension element is flattened before the next row element. -/
def flattenExtensions {degree : ℕ} (row : List (Fin degree → F)) : List F :=
  row.flatMap List.ofFn

theorem flattenExtensions_length {degree : ℕ} (row : List (Fin degree → F)) :
    (flattenExtensions row).length = row.length * degree := by
  induction row with
  | nil => simp [flattenExtensions]
  | cons head tail ih =>
      simp only [flattenExtensions] at ih
      simp [flattenExtensions, ih, Nat.add_mul, Nat.add_comm]

variable [Zero F] [DecidableEq F]

/-- Untagged primitive-input model for any fixed one-call row width up to the rate. -/
def singleHashing (width : ℕ) (bound : width ≤ 8) :
    LeafHashing (Fin width → F) (State F 8) (Digest F 8) where
  leaf := fun row ↦ ((fun i ↦ if below : i.val < width then row ⟨i.val, below⟩ else 0), 0)
  node := fun left right ↦ (left, right)
  leafRow := fun input ↦
    if input.2 = 0 ∧ ∀ i : Fin 8, width ≤ i.val → input.1 i = 0 then
      some (fun i ↦ input.1 ⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩)
    else none
  children := some
  leafRow_leaf := by
    intro row
    have suffix : ∀ i : Fin 8, width ≤ i.val →
        (if below : i.val < width then row ⟨i.val, below⟩ else 0) = 0 := by
      intro i hi
      simp [Nat.not_lt.mpr hi]
    rw [ite_eq_left ⟨rfl, suffix⟩]
    congr 1
    funext i
    simp [i.isLt]
  children_node := fun _ _ ↦ rfl

/-- At width eight, a leaf and a node with zero right child are the same primitive query. -/
theorem width_eight_alias (row : Digest F 8) :
    (singleHashing 8 (by omega)).leaf row = (singleHashing 8 (by omega)).node row 0 := by
  apply Prod.ext
  · funext i
    simp [singleHashing]
  · rfl

omit [Zero F] [DecidableEq F] in
/-- The rate-eight partial overwrite retains every untouched coordinate of the full state. -/
theorem flatten_overwrite (state : State F 8) (count : ℕ) (bound : count ≤ 8)
    (block : Digest F 8) (i : Fin 16) :
    flattenState (overwrite state count block) i =
      if below : i.val < count then block ⟨i.val, Nat.lt_of_lt_of_le below bound⟩
      else flattenState state i := by
  unfold flattenState overwrite
  split
  · split <;> simp_all
  · have outside : ¬ i.val < count := by omega
    simp [outside]

end ZkcSecurity.Commitment.PoseidonRows
