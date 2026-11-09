module

public import Zkc.Protocol.Library.Transformations.Commitment.BatchVerification

@[expose] public section

/-! # Completeness of the decoded batch operation

The producer supplies a reduction over the hash answers actually used by the
verifier. The generic theorem discharges the verifier's independent shape,
representative, duplicate, proof-length, and row-admission checks. No collision
assumption is needed for completeness. Native proof construction and byte
framing remain separate correspondence obligations.
-/

set_option autoImplicit false
namespace ZkcSecurity.Commitment.BatchVerification
open OracleComp OracleSpec BatchOpening
variable {Row Query Y : Type}

/-- An answer-consistent reduction suffices for the entire decoded operation.
Its structure implies the required proof length; the caller does not prove an
acceptance equation or supply a second copy of the hash execution. -/
theorem verify_complete [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (root : Y) (proof : List Y) (selected : List (ℕ × Row)) (log : HashLog Query Y)
    (shape : ValidShape wordMax elementLimit width height)
    (nonempty : positions ≠ []) (bounded : ∀ index ∈ positions, index < height)
    (lengths : positions.length = rows.length) (allocation : positions.length * width ≤ wordMax)
    (duplicates : ∀ pair ∈ positions.zip rows,
      representative (positions.zip rows) pair.1 = some pair)
    (selection : select (positions.zip rows) (unique positions) = some selected)
    (widths : ∀ pair ∈ selected, validRow width pair.2 = true)
    (consistent : ∀ entry ∈ log, answer entry.1 = entry.2)
    (certificate : Reduction model log (Nat.clog 2 height)
      (selected.map fun pair ↦ (pair.1, answer (model.leaf pair.2))) proof root) :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) = .returned true := by
  have indices := (select_sound (unique positions) selection).1
  have proofLength := certificate.proof_length
  simp only [List.map_map] at proofLength
  change proof.length = proofCount (Nat.clog 2 height) (selected.map Prod.fst) at proofLength
  rw [indices] at proofLength
  have duplicateCheck : (positions.zip rows).all
      (fun pair ↦ representative (positions.zip rows) pair.1 == some pair) = true := by
    simpa only [List.all_eq_true, beq_iff_eq] using duplicates
  have widthCheck : selected.all (fun pair ↦ validRow width pair.2) = true :=
    List.all_eq_true.mpr widths
  have reduced := (reduce_complete model answer consistent certificate).1
  have admitted : ¬ (¬ ValidShape wordMax elementLimit width height ∨ positions = [] ∨
      ¬ ∀ index ∈ positions, index < height) := by tauto
  have sizes : ¬ (positions.length ≠ rows.length ∨ wordMax < positions.length * width) := by omega
  rw [verify, ite_eq_right admitted, ite_eq_right sizes]
  simp [duplicateCheck, proofLength, selection, widthCheck, evalWithAnswerFn_bind,
    hashRows_eval, reduced]

/-- Repeated queries of one fixed table have a single representative row. -/
theorem representative_table (table : ℕ → Row) (positions : List ℕ) (index : ℕ)
    (member : index ∈ positions) :
    representative (positions.map fun position ↦ (position, table position)) index =
      some (index, table index) := by
  induction positions with
  | nil => simp at member
  | cons head rest ih =>
      by_cases same : head = index
      · subst head
        simp [representative]
      · have later : index ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa [representative, same] using ih later

/-- Selecting a fixed table preserves the verifier's sorted, distinct index
order, independently of the order and multiplicity of the original requests. -/
theorem select_table (table : ℕ → Row) (positions indices : List ℕ)
    (included : ∀ index ∈ indices, index ∈ positions) :
    select (positions.map fun position ↦ (position, table position)) indices =
      some (indices.map fun position ↦ (position, table position)) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      have first := representative_table table positions index (included _ List.mem_cons_self)
      have tail := ih (fun index member ↦ included _ (List.mem_cons_of_mem _ member))
      simp only [select, first, tail, List.map_cons]
      rfl

/-- A fixed table discharges duplicate consistency and representative selection
uniformly for any request order. Only its actual tree reduction, public shape,
row validity, and allocation bound remain for the producer connection. -/
theorem verify_table_complete [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (table : ℕ → Row)
    (root : Y) (proof : List Y) (log : HashLog Query Y)
    (shape : ValidShape wordMax elementLimit width height)
    (nonempty : positions ≠ []) (bounded : ∀ index ∈ positions, index < height)
    (allocation : positions.length * width ≤ wordMax)
    (widths : ∀ index ∈ positions, validRow width (table index) = true)
    (consistent : ∀ entry ∈ log, answer entry.1 = entry.2)
    (certificate : Reduction model log (Nat.clog 2 height)
      ((unique positions).map fun index ↦ (index, answer (model.leaf (table index)))) proof root) :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow wordMax elementLimit width height positions (positions.map table)
        (.decoded root proof)) = .returned true := by
  have zipped : positions.zip (positions.map table) =
      positions.map (fun index ↦ (index, table index)) := by
    simpa using (List.zip_map' (f := id) (g := table) (l := positions))
  apply verify_complete model validRow answer wordMax elementLimit width height positions
    (positions.map table) root proof ((unique positions).map fun index ↦ (index, table index))
    log shape nonempty bounded (by simp) allocation
  · intro pair member
    rw [zipped] at member ⊢
    obtain ⟨index, belongs, same⟩ := List.mem_map.mp member
    subst pair
    exact representative_table table positions index belongs
  · rw [zipped]
    exact select_table table positions (unique positions) (fun _ member ↦ unique_mem.mp member)
  · intro pair member
    obtain ⟨index, belongs, same⟩ := List.mem_map.mp member
    subst pair
    exact widths index (unique_mem.mp belongs)
  · exact consistent
  · simpa only [List.map_map, Function.comp_def] using certificate

end ZkcSecurity.Commitment.BatchVerification
