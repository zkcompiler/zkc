module

public import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.BatchAdapter
public meta import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.DirectExtraction
public meta import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.Checkpoint

@[expose] public section

/-! # Focused deterministic permutation-record controls

All concrete checks are kernel reductions (`decide`), not native decision procedures. Natural
coordinates make the examples readable; no probability or concrete Poseidon security is tested.
-/

set_option autoImplicit false

namespace TestsSecurity.PoseidonRows

open ZkcSecurity.Commitment ZkcSecurity.Commitment.PoseidonRows

def vector (start : ℕ) : Digest ℕ 8 := fun i ↦ start + i.val

def first (tail : ℕ) : Exposure ℕ 8 :=
  ⟨true, overwrite (0, 0) tail (vector 1), (vector 20, vector 40)⟩

def second (tail : ℕ) : Exposure ℕ 8 :=
  ⟨true, overwrite (first 8).output tail (vector 9), (vector 60, vector 80)⟩

def width (length : ℕ) (positive : 0 < length) : Width 8 :=
  Width.ofLength (by omega) length positive

def request (length : ℕ) (positive : 0 < length) : Request 8 :=
  ⟨width length positive, 1, 0, by omega, by decide⟩

theorem width_one : (width 1 (by omega)).full = 0 ∧ (width 1 (by omega)).tail = 1 := by decide
theorem width_eight : (width 8 (by omega)).full = 0 ∧ (width 8 (by omega)).tail = 8 := by decide
theorem width_nine : (width 9 (by omega)).full = 1 ∧ (width 9 (by omega)).tail = 1 := by decide
theorem width_sixteen :
    (width 16 (by omega)).full = 1 ∧ (width 16 (by omega)).tail = 8 := by decide

theorem single_one : directExtract (request 1 (by omega)) [first 1] (vector 20) 0 =
    some [1] := by decide
theorem single_two : directExtract (request 2 (by omega)) [first 2] (vector 20) 0 =
    some [1, 2] := by decide
theorem single_four : directExtract (request 4 (by omega)) [first 4] (vector 20) 0 =
    some [1, 2, 3, 4] := by decide
theorem single_eight : directExtract (request 8 (by omega)) [first 8] (vector 20) 0 =
    some [1, 2, 3, 4, 5, 6, 7, 8] := by decide

theorem multiblock_nine : directExtract (request 9 (by omega)) [first 8, second 1] (vector 60) 0 =
    some [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
theorem multiblock_sixteen :
    directExtract (request 16 (by omega)) [first 8, second 8] (vector 60) 0 =
      some [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by decide

theorem nine_good : Good [first 8, second 1] := by decide
theorem sixteen_good : Good [first 8, second 8] := by decide

theorem nine_trace : SpongeTrace [first 8, second 1] 1 1 (second 1)
    [1, 2, 3, 4, 5, 6, 7, 8, 9] :=
  .next (vector 9) (.single (vector 1) (by simp) rfl) (by simp) rfl

theorem retained_tail : (second 1).input.1 ⟨1, by omega⟩ = 21 := by decide

def wronglyPadded : Exposure ℕ 8 :=
  ⟨true, ((fun i ↦ if i.val = 0 then 9 else 0), vector 40), (vector 60, vector 80)⟩

theorem wrong_partial_padding_refused :
    directExtract (request 9 (by omega)) [first 8, wronglyPadded] (vector 60) 0 = none := by decide
theorem missing_intermediate_refused :
    directExtract (request 9 (by omega)) [second 1] (vector 60) 0 = none := by decide
theorem absent_trace_refused :
    directExtract (request 9 (by omega)) [] (vector 60) 0 = none := by decide
theorem wrong_initial_capacity_refused :
    recover [second 1] 0 1 (second 1) = none := by decide
theorem wrong_single_suffix_refused : recover [first 8] 0 1 (first 8) = none := by decide
theorem no_zero_width : ¬ ∃ w : Width 8, w.length = 0 := by
  rintro ⟨w, equal⟩
  have positive := w.positive
  simp only [Width.length] at equal
  omega

theorem exact_boundary_has_two_blocks : (width 16 (by omega)).full + 1 = 2 := by decide
theorem aliases_same_input :
    (singleHashing (F := ℕ) 8 (by omega)).leaf (vector 1) =
      (singleHashing 8 (by omega)).node (vector 1) 0 := width_eight_alias _

theorem node_and_leaf_same_label :
    (⟨.node (second 1).input.1 (second 1).input.2, vector 60⟩ :
      (_ : MacroQuery ℕ 8) × Digest ℕ 8) ∈ macroLog [first 8, second 1] (width 9 (by omega)) ∧
    (⟨.leaf [1, 2, 3, 4, 5, 6, 7, 8, 9], vector 60⟩ :
      (_ : MacroQuery ℕ 8) × Digest ℕ 8) ∈ macroLog [first 8, second 1] (width 9 (by omega)) := by
  exact ⟨node_mem (by simp) rfl, leaf_mem (width := width 9 (by omega)) nine_good nine_trace⟩

theorem suffix_first_bad : ¬ Good [second 1, first 8] := by decide
theorem late_capacity_changes_root :
    directExtract (request 9 (by omega)) [second 1] (vector 60) 0 = none ∧
    directExtract (request 9 (by omega)) [second 1, first 8] (vector 60) 0 =
      some [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
theorem late_capacity_no_rate_target_hit :
    (first 8).output.1 ≠ vector 60 ∧ (first 8).output.1 ≠ (second 1).input.1 ∧
      (first 8).output.1 ≠ (second 1).input.2 := by decide
theorem late_capacity_flag : ¬ CapacitySafe [second 1] (first 8) := by decide

def inverseFirst : Exposure ℕ 8 := { first 8 with forward := false }
def inverseSecond : Exposure ℕ 8 := { second 1 with forward := false }

theorem inverse_birth_not_relabelled :
    normalize [inverseFirst, first 8, first 8] = [inverseFirst] := by decide
theorem repeated_forward_memoized : normalize [first 8, first 8, second 1] = [first 8, second 1] :=
  by decide
theorem inverse_zero_flag : ¬ Good [inverseFirst] := by decide
theorem inverse_later_capacity_flag : ¬ Good [first 8, inverseSecond] := by decide
theorem inverse_earlier_capacity_flag : ¬ Good [inverseSecond, first 8] := by decide
theorem inverse_ignored :
    directExtract (request 8 (by omega)) [inverseFirst] (vector 20) 0 = none := by decide

def inverseA : Exposure ℕ 8 := ⟨false, (vector 100, vector 120), (vector 20, vector 40)⟩
def inverseB : Exposure ℕ 8 := ⟨false, (vector 140, vector 160), (vector 20, vector 80)⟩

/-- Selected inverse output-rate collisions are allowed, rather than treated as random outputs. -/
theorem inverse_selected_rate_collision_allowed :
    Good [inverseA, inverseB] ∧ inverseA.output.1 = inverseB.output.1 := by decide

def parent : Exposure ℕ 8 := ⟨true, (vector 60, vector 100), (vector 120, vector 140)⟩
def treeRequest : Request 8 := ⟨width 9 (by omega), 2, 1, by omega, by decide⟩

theorem node_climb_good : Good [first 8, second 1, parent] := by decide
theorem actual_node_descent : directExtract treeRequest [first 8, second 1, parent]
    (vector 120) 0 = some [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
theorem inverse_parent_left_flag : ¬ Good [first 8, second 1, { parent with forward := false }] :=
  by decide
theorem inverse_parent_right_flag :
    ¬ Good [first 8, second 1,
      ⟨false, (vector 100, vector 60), (vector 120, vector 140)⟩] := by decide
theorem actual_height_restricts : directExtract treeRequest [first 8, second 1, parent]
    (vector 120) 2 = none := by decide
theorem fixed_missing_completion :
    complete (request 9 (by omega)) [] (vector 60) 0 = List.replicate 9 0 := by decide

theorem flatten_ascending : flattenExtensions [vector 1, vector 9] =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by decide

theorem checkpoint_freezes_before_first :
    directCheckpoint (request 9 (by omega)) (7 : ℕ)
      [primitive (second 1), allocation 7 [vector 60], primitive (first 8)] (vector 60) 0 = none :=
  by decide
theorem late_capacity_full_table_differs :
    directExtract (request 9 (by omega))
      (normalize (calls ([primitive (second 1), allocation (7 : ℕ) [vector 60],
        primitive (first 8)] : History ℕ ℕ 8))) (vector 60) 0 =
          some [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide

/-- A duplicate request uses the same recorded row; the list does not truncate at a zip. -/
theorem ordered_duplicate_batch :
    ([0, 0] : List ℕ).map (directExtract (request 9 (by omega))
      (normalize [first 8, second 1]) (vector 60)) =
        ([[1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 2, 3, 4, 5, 6, 7, 8, 9]] : List (List ℕ)).map some := by
  apply raw_batch_agrees (raw := [first 8, second 1])
    (by have eq : normalize [first 8, second 1] = [first 8, second 1] := by decide
        rw [eq]; exact nine_good) (.root (vector 60))
  · intro entry member
    have equal : entry = (0, vector 60) := by simpa using member
    subst entry
    exact ⟨second 1, _, rfl, nine_trace⟩
  · exact .cons ⟨second 1, by simp [second], nine_trace⟩
      (.cons ⟨second 1, by simp [second], nine_trace⟩ .nil)
  · simp [request]

theorem forged_macro_refused :
    (⟨.leaf [99], vector 60⟩ : (_ : MacroQuery ℕ 8) × Digest ℕ 8) ∉
      macroLog [first 8, second 1] (width 9 (by omega)) := by decide

def conflictingCapacity : Exposure ℕ 8 :=
  ⟨true, (vector 100, vector 120), (vector 140, vector 40)⟩

theorem capacity_collision_without_rate_collision :
    ¬ Good [first 8, conflictingCapacity] ∧
      (first 8).output.1 ≠ conflictingCapacity.output.1 ∧
      (first 8).output.2 = conflictingCapacity.output.2 := by decide

theorem inverse_selected_rate_collision_ignored :
    directExtract (request 8 (by omega)) [inverseA, inverseB] (vector 20) 0 = none := by decide

theorem first_constituent_not_last_cache_hit :
    directCheckpoint (request 8 (by omega)) (7 : ℕ)
      [allocation 7 [vector 20], primitive (first 8), allocation 7 [vector 20]] (vector 20) 0 =
        none := by decide

theorem ascending_coordinate_order_matters :
    flattenExtensions [vector 1, vector 9] ≠ flattenExtensions [vector 9, vector 1] := by decide

/-- Public local evaluation can bypass a designated API log. The known map is an actual
permutation (`Equiv.swap`); no small-loss designated-API-only assumption can cover this model. -/
theorem public_permutation_outside_log :
    evaluateBlocks (Equiv.swap (first 8).input (first 8).output) [(8, vector 1)] =
      (first 8).output ∧ directExtract (request 8 (by omega)) [] (vector 20) 0 = none := by decide

theorem actual_height_three_uses_depth_two :
    (Request.ofHeight (width 8 (by omega)) 3 (by omega)).depth = 2 := by decide
theorem actual_height_three_excludes_padding :
    directExtract (Request.ofHeight (width 8 (by omega)) 3 (by omega)) [] (vector 20) 3 = none :=
  by decide
theorem direct_fixed_zero_completion :
    directComplete (request 9 (by omega)) [] (vector 60) 0 = List.replicate 9 0 := by decide

def otherLeaf : Exposure ℕ 8 :=
  ⟨true, overwrite (0, 0) 8 (vector 9), (vector 60, vector 80)⟩
def sharedParent : Exposure ℕ 8 := ⟨true, (vector 20, vector 60), (vector 100, vector 120)⟩
def binaryRequest : Request 8 := Request.ofHeight (width 8 (by omega)) 2 (by omega)

/-- Two active siblings consume one shared compression and no boundary sibling. The original
request order is right, left, right; the frontier order remains left, right. -/
theorem shared_frontier_ordered_batch :
    ([1, 0, 1] : List ℕ).map (directExtract binaryRequest
      (normalize [first 8, otherLeaf, sharedParent]) (vector 100)) =
        ([[9, 10, 11, 12, 13, 14, 15, 16], [1, 2, 3, 4, 5, 6, 7, 8],
          [9, 10, 11, 12, 13, 14, 15, 16]] : List (List ℕ)).map some := by
  let log := [first 8, otherLeaf, sharedParent]
  let frontier := [(0, vector 20), (1, vector 60)]
  have good : Good (normalize log) := by decide
  have traceA : SpongeTrace log 0 8 (first 8) [1, 2, 3, 4, 5, 6, 7, 8] :=
    .single (vector 1) (by simp [log]) rfl
  have traceB : SpongeTrace log 0 8 otherLeaf [9, 10, 11, 12, 13, 14, 15, 16] :=
    .single (vector 9) (by simp [log]) rfl
  have reduction : BatchOpening.Reduction compression (primitiveLog log) 1 frontier []
      (vector 100) := by
    apply BatchOpening.Reduction.step (above := [(0, vector 100)])
    · exact .shared (p := 0) (by simp)
        (List.mem_map.mpr ⟨sharedParent, by simp [log], rfl⟩) (.nil [])
    · exact .root _
  apply raw_batch_agrees (request := binaryRequest) good reduction
  · intro entry member
    simp only [frontier, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨first 8, _, rfl, traceA⟩
    · exact ⟨otherLeaf, _, rfl, traceB⟩
  · exact .cons ⟨otherLeaf, by simp [frontier, otherLeaf], traceB⟩
      (.cons ⟨first 8, by simp [frontier, first], traceA⟩
        (.cons ⟨otherLeaf, by simp [frontier, otherLeaf], traceB⟩ .nil))
  · simp [binaryRequest, Request.ofHeight]

-- Runtime executability evidence, separate from the kernel-checked propositions above.
#eval directExtract (request 9 (by omega)) [first 8, second 1] (vector 60) 0
#eval directExtract (request 16 (by omega)) [first 8, second 8] (vector 60) 0
#eval directCheckpoint (request 9 (by omega)) (7 : ℕ)
  [primitive (second 1), allocation 7 [vector 60], primitive (first 8)] (vector 60) 0

end TestsSecurity.PoseidonRows
