import Zkc.Protocol.Library.Transformations.Commitment.BatchOpening
import Zkc.Tools.Program.DeclarationAudit

/-! Kernel-checked controls for recorded batch authentication. Natural-number labels are a
deterministic proof fixture, not a cryptographic instance or native execution test. -/

set_option autoImplicit false

namespace TestsSecurity.BatchOpening

open ZkcSecurity.Commitment ZkcSecurity.Commitment.BatchOpening

abbrev Query := List ℕ ⊕ (ℕ × ℕ)

def model : LeafHashing (List ℕ) Query ℕ where
  leaf := Sum.inl
  node left right := .inr (left, right)
  leafRow
    | .inl row => some row
    | .inr _ => none
  children
    | .inl _ => none
    | .inr pair => some pair
  leafRow_leaf _ := rfl
  children_node _ _ := rfl

def row0 : List ℕ := [1, 2]
def row1 : List ℕ := [3, 4]
def row2 : List ℕ := [5, 6]

def log : HashLog Query ℕ :=
  [⟨.inl row0, 10⟩, ⟨.inl row1, 20⟩, ⟨.inl row2, 30⟩,
   ⟨.inr (10, 20), 40⟩, ⟨.inr (30, 0), 50⟩, ⟨.inr (40, 50), 60⟩]

def frontier : Frontier ℕ := [(0, 10), (1, 20), (2, 30)]

/-- Three active leaves use one boundary digest and three shared node calls. -/
theorem reduction : Reduction model log 2 frontier [0] 60 := by
  apply Reduction.step (above := [(0, 40), (1, 50)]) (tail := [])
  · apply Layer.shared (p := 0)
    · intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      decide
    · decide
    · exact Layer.left (p := 1) (by simp) (by decide) (.nil [])
  · exact .step (.shared (p := 0) (by simp) (by decide) (.nil [])) (.root 60)

theorem no_collision : MerkleTreeExtractor.ResponseInjectiveOn log := by
  intro first firstMem second secondMem same
  simp only [log, List.mem_cons, List.not_mem_nil, or_false] at firstMem secondMem
  rcases firstMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases secondMem with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- The requests are deliberately unsorted and position two occurs twice. -/
theorem original_rows : RowsRecorded model log frontier [2, 0, 2, 1]
    [row2, row0, row2, row1] := by
  exact .cons ⟨30, by decide, by decide⟩ (.cons ⟨10, by decide, by decide⟩
    (.cons ⟨30, by decide, by decide⟩ (.cons ⟨20, by decide, by decide⟩ .nil)))

theorem ordered_batch_agreement :
    [2, 0, 2, 1].map (model.extract log 2 60) = [row2, row0, row2, row1].map some :=
  batch_agrees reduction original_rows no_collision

theorem shared_path_for_position_two :
    2 < 2 ^ 2 ∧ ∃ path, path.length = 2 ∧ model.Climbs log 2 path 30 60 :=
  reduction.paths (by decide)

theorem boundary_count : proofCount 2 [0, 1, 2] = 1 := by decide

theorem short_proof_refused : ¬ Reduction model log 2 frontier [] 60 := by
  intro accepted
  have count := accepted.proof_length
  change 0 = 1 at count
  omega

theorem surplus_proof_refused : ¬ Reduction model log 2 frontier [0, 99] 60 := by
  intro accepted
  have count := accepted.proof_length
  change 2 = 1 at count
  omega

theorem wrong_depth_refused : ¬ Reduction model log 1 frontier [0] 60 := by
  intro accepted
  obtain ⟨bound, _⟩ := accepted.paths (index := 2) (label := 30) (by decide)
  norm_num at bound

theorem empty_frontier_refused : ¬ Reduction model log 2 [] [] 60 := by
  intro accepted
  exact accepted.nonempty rfl

theorem root_leftover_refused : ¬ Reduction model log 0 [(0, 60)] [99] 60 := by
  rw [Reduction.zero_iff]
  simp

theorem wrong_root_refused : ¬ Reduction model log 2 frontier [0] 61 := by
  intro accepted
  have agree := batch_agrees accepted original_rows no_collision
  have missing : model.extract log 2 61 2 = none := by decide
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at agree
  rw [missing] at agree
  cases agree.1

/-- Deduplicating authentication work cannot discard a changed row at a repeated position. -/
theorem inconsistent_repeat_refused :
    ¬ RowsRecorded model log frontier [2, 0, 2, 1] [row2, row0, row0, row1] := by
  intro recorded
  have agree := batch_agrees reduction recorded no_collision
  have good := ordered_batch_agreement.symm.trans agree
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Option.some.injEq] at good
  have different : row2 ≠ row0 := by decide
  exact different good.2.2.1

theorem reordered_rows_refused :
    ¬ RowsRecorded model log frontier [2, 0, 2, 1] [row0, row2, row2, row1] := by
  intro recorded
  have agree := ordered_batch_agreement.symm.trans (batch_agrees reduction recorded no_collision)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Option.some.injEq] at agree
  exact (by decide : row2 ≠ row0) agree.1

theorem truncated_row_list_refused :
    ¬ RowsRecorded model log frontier [2, 0, 2, 1] [row2, row0, row2] := by
  intro recorded
  have lengths := List.Forall₂.length_eq recorded
  simp at lengths

/-- A missing log call cannot be supplied by the proof alone. -/
theorem missing_leaf_call_refused :
    ¬ RowsRecorded model [] frontier [0] [row0] := by
  intro recorded
  cases recorded with
  | cons head _ => obtain ⟨_, _, impossible⟩ := head; simp at impossible

/-- Height, width and canonical framing are additional native admission obligations. -/
theorem padded_index_needs_height_gate : 3 < 2 ^ 2 ∧ ¬ 3 < 3 := by decide

theorem rows_have_exact_width : row0.length = 2 ∧ row1.length = 2 ∧ row2.length = 2 := by
  decide

theorem row_encoding_is_not_permutable : row0 ≠ row0.reverse := by decide

/-- The right-child boundary rule puts the supplied sibling on the left. -/
theorem right_boundary : Reduction model log 1 [(1, 20)] [10] 40 :=
  .step (.right (p := 0) (by simp) (by decide) (.nil [])) (.root 40)

theorem wrong_sibling_order_refused : ¬ Reduction model log 1 [(1, 20)] [20] 40 := by
  intro accepted
  cases accepted with
  | step layer next =>
      obtain ⟨rfl, rfl⟩ := Reduction.zero_iff.mp next
      generalize original : [(1, 20)] = below at layer
      cases layer <;> simp_all [log, model]

def collidingLog : HashLog Query ℕ := log ++ [⟨.inl [9, 9], 30⟩]

/-- A recorded collision is a valid alternative; the algebra assumes no collision resistance. -/
theorem collision_from_disagreement : Collision collidingLog := by
  have larger := reduction.mono (larger := collidingLog)
    (fun entry member ↦ List.mem_append_left _ member)
  have forged : RowsRecorded model collidingLog frontier [2] [[9, 9]] :=
    .cons ⟨30, by decide, by decide⟩ .nil
  apply disagreement_collision larger forged
  decide

theorem collision_invalidates_record_premise :
    ¬ MerkleTreeExtractor.ResponseInjectiveOn collidingLog := by
  rw [responseInjective_iff]
  exact not_not_intro collision_from_disagreement

/-- With both siblings active no boundary digest is needed. -/
theorem full_pair_empty_proof : Reduction model log 1 [(0, 10), (1, 20)] [] 40 :=
  .step (.shared (p := 0) (by simp) (by decide) (.nil [])) (.root 40)

theorem full_pair_surplus_refused :
    ¬ Reduction model log 1 [(0, 10), (1, 20)] [99] 40 := by
  intro accepted
  have count := accepted.proof_length
  change 1 = 0 at count
  omega

end TestsSecurity.BatchOpening

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Protocol.Library.Transformations.Commitment.BatchOpening] "BATCH-OPENING-AXIOMS-PASS"
run_cmd ZkcTools.DeclarationAudit.checkCurrent "BATCH-OPENING-CONTROLS-AXIOMS-PASS"
