import ZkcSecurity.Transformations.Commitment.BatchVerification

/-! Kernel-checked operation controls. These small natural-number fixtures are not native
execution evidence or a cryptographic instantiation. All outcomes and logs are computed by
the independent operation, rather than supplied batch certificates. -/

set_option autoImplicit false

namespace TestsSecurity.BatchVerification

open OracleComp OracleSpec ZkcSecurity.Commitment ZkcSecurity.Commitment.BatchOpening
open ZkcSecurity.Commitment.BatchVerification

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

def answer : Query → ℕ
  | .inl row => if row = row0 then 10 else if row = row1 then 20 else 30
  | .inr (left, right) =>
      if (left, right) = (10, 20) then 40
      else if (left, right) = (30, 0) then 50
      else if (left, right) = (40, 50) then 60 else 99

def validRow (width : ℕ) (row : List ℕ) : Bool := row.length == width

def operation (height : ℕ) (positions : List ℕ) (rows : List (List ℕ))
    (decoding : Decoding ℕ) : OracleComp (Query →ₒ ℕ) (PIR.Outcome Bool) :=
  verify model validRow (2 ^ 64 - 1) 128 2 height positions rows decoding

def evaluate (height : ℕ) (positions : List ℕ) (rows : List (List ℕ))
    (decoding : Decoding ℕ) : PIR.Outcome Bool :=
  evalWithAnswerFn (QueryImpl.ofFn answer) (operation height positions rows decoding)

def history (height : ℕ) (positions : List ℕ) (rows : List (List ℕ))
    (decoding : Decoding ℕ) : HashLog Query ℕ :=
  tableQueryLog (operation height positions rows decoding) answer

def requests : List ℕ := [2, 0, 2, 1]
def replies : List (List ℕ) := [row2, row0, row2, row1]

theorem unsorted_duplicates_accept : evaluate 3 requests replies (.decoded 60 [0]) =
    .returned true := by decide

theorem exact_history : history 3 requests replies (.decoded 60 [0]) =
    [⟨.inl row0, 10⟩, ⟨.inl row1, 20⟩, ⟨.inl row2, 30⟩,
      ⟨.inr (10, 20), 40⟩, ⟨.inr (30, 0), 50⟩, ⟨.inr (40, 50), 60⟩] := by decide

theorem exact_six_queries : (history 3 requests replies (.decoded 60 [0])).length = 6 := by decide

theorem successful_call_yields_actual_certificate :
    ∃ frontier,
      frontier.map Prod.fst = [0, 1, 2] ∧
      Reduction model (history 3 requests replies (.decoded 60 [0])) 2 frontier [0] 60 ∧
      RowsRecorded model (history 3 requests replies (.decoded 60 [0])) frontier requests
        replies := by
  obtain ⟨_, _, _, _, _, frontier, positions, reduction, rows, _⟩ :=
    verify_success model validRow answer (2 ^ 64 - 1) 128 2 3 requests replies 60 [0]
      unsorted_duplicates_accept
  exact ⟨frontier, positions, reduction, rows⟩

theorem empty_requests_refuse : evaluate 3 [] [] (.decoded 60 []) = .stopped .refused := by decide

theorem padding_request_refuses : evaluate 3 [3] [row0] (.decoded 60 [0, 0]) =
    .stopped .refused := by decide

theorem padding_refusal_has_no_hashes :
    history 3 [3] [row0] (.decoded 60 [0, 0]) = [] := by decide

theorem zero_height_refuses :
    evaluate 0 [0] [row0] (.decoded 10 []) = .stopped .refused := by decide

theorem zero_width_refuses :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow (2 ^ 64 - 1) 128 0 3 [0] [row0] (.decoded 10 [])) =
      .stopped .refused := by decide

theorem excessive_height_refuses : evaluate (2 ^ 24 + 1) [0] [row0] (.decoded 10 []) =
    .stopped .refused := by decide

theorem element_ceiling_refuses :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow (2 ^ 64 - 1) 5 2 3 [0] [row0] (.decoded 10 [])) =
      .stopped .refused := by decide

theorem shape_machine_overflow_refuses :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow 5 128 2 3 [0] [row0] (.decoded 10 [])) =
      .stopped .refused := by decide

theorem flat_count_machine_overflow_is_false :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow 6 128 2 3 [0, 0, 0, 0] [row0, row0, row0, row0]
        (.decoded 10 [])) = .returned false := by decide

theorem wrong_row_count_is_false : evaluate 3 requests [row0] (.decoded 60 [0]) =
    .returned false := by decide

theorem truncated_rows_do_not_hide_behind_zip :
    history 3 requests [row2, row0, row2] (.decoded 60 [0]) = [] := by decide

theorem malformed_decoding_is_false : evaluate 3 requests replies .invalid =
    .returned false := by decide

theorem decode_exhaustion_stops : evaluate 3 requests replies .exhausted =
    .stopped .exhausted := by decide

theorem decode_exhaustion_has_no_hashes : history 3 requests replies .exhausted = [] := by decide

theorem request_refusal_precedes_decoding : evaluate 3 [] [] .exhausted =
    .stopped .refused := by decide

theorem count_failure_precedes_decoding : evaluate 3 requests [] .exhausted =
    .returned false := by decide

theorem inconsistent_duplicates_are_false :
    evaluate 3 requests [row2, row0, row1, row1] (.decoded 60 [0]) = .returned false := by decide

theorem inconsistent_duplicates_have_no_hashes :
    history 3 requests [row2, row0, row1, row1] (.decoded 60 [0]) = [] := by decide

theorem duplicate_equality_is_unconditional :
    evalWithAnswerFn (QueryImpl.ofFn (fun _ : Query ↦ 7))
      (operation 3 requests [row2, row0, row1, row1] (.decoded 7 [0])) =
      .returned false := by decide

theorem short_proof_is_false : evaluate 3 requests replies (.decoded 60 []) =
    .returned false := by decide

theorem surplus_proof_is_false : evaluate 3 requests replies (.decoded 60 [0, 0]) =
    .returned false := by decide

theorem surplus_proof_has_no_hashes :
    history 3 requests replies (.decoded 60 [0, 0]) = [] := by decide

theorem row_width_failure_is_false : evaluate 3 [0] [[1]] (.decoded 60 [20, 50]) =
    .returned false := by decide

theorem row_width_failure_has_no_hashes :
    history 3 [0] [[1]] (.decoded 60 [20, 50]) = [] := by decide

theorem sparse_boundary_order_accepts : evaluate 3 [0, 2] [row0, row2] (.decoded 60 [20, 0]) =
    .returned true := by decide

theorem swapped_boundary_order_is_false : evaluate 3 [0, 2] [row0, row2] (.decoded 60 [0, 20]) =
    .returned false := by decide

theorem sparse_walk_uses_five_queries :
    (history 3 [0, 2] [row0, row2] (.decoded 60 [20, 0])).length = 5 := by decide

theorem right_child_orientation_accepts : evaluate 3 [1] [row1] (.decoded 60 [10, 50]) =
    .returned true := by decide

theorem wrong_sibling_is_false : evaluate 3 [1] [row1] (.decoded 60 [20, 50]) =
    .returned false := by decide

theorem wrong_root_keeps_all_queries : history 3 requests replies (.decoded 61 [0]) =
    history 3 requests replies (.decoded 60 [0]) := by decide

theorem wrong_root_is_false : evaluate 3 requests replies (.decoded 61 [0]) =
    .returned false := by decide

theorem depth_zero_hashes_one_distinct_leaf :
    evaluate 1 [0, 0] [row0, row0] (.decoded 10 []) = .returned true ∧
      history 1 [0, 0] [row0, row0] (.decoded 10 []) = [⟨.inl row0, 10⟩] := by decide

theorem depth_zero_surplus_is_false : evaluate 1 [0] [row0] (.decoded 10 [0]) =
    .returned false := by decide

theorem full_pair_needs_no_boundary : evaluate 2 [1, 0] [row1, row0] (.decoded 40 []) =
    .returned true := by decide

theorem full_pair_surplus_is_false : evaluate 2 [1, 0] [row1, row0] (.decoded 40 [0]) =
    .returned false := by decide

theorem identical_rows_at_distinct_positions_are_both_hashed :
    evaluate 2 [0, 1] [row0, row0] (.decoded 99 []) = .returned true ∧
      history 2 [0, 1] [row0, row0] (.decoded 99 []) =
        [⟨.inl row0, 10⟩, ⟨.inl row0, 10⟩, ⟨.inr (10, 10), 99⟩] := by decide

theorem arbitrary_colliding_answers_can_authenticate :
    evalWithAnswerFn (QueryImpl.ofFn (fun _ : Query ↦ 7))
      (operation 3 requests replies (.decoded 7 [0])) = .returned true := by decide

theorem compression_count_is_separate_from_boundary_count :
    compressionCount 2 [0, 1, 2] = 3 ∧ proofCount 2 [0, 1, 2] = 1 := by decide

theorem malformed_flat_frame_precedes_decode_exhaustion :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verifyFramed model validRow (2 ^ 64 - 1) 128 2 3 [0] none .exhausted) =
      .returned false := by decide

theorem malformed_flat_frame_has_no_hashes :
    tableQueryLog (verifyFramed model validRow (2 ^ 64 - 1) 128 2 3 [0] none
      (.decoded 60 [20, 50])) answer = [] := by decide

theorem request_refusal_precedes_malformed_frame :
    evalWithAnswerFn (QueryImpl.ofFn answer)
      (verifyFramed model validRow (2 ^ 64 - 1) 128 2 3 [] none .exhausted) =
      .stopped .refused := by decide

theorem framed_success_uses_the_same_history :
    tableQueryLog (verifyFramed model validRow (2 ^ 64 - 1) 128 2 3 requests (some replies)
      (.decoded 60 [0])) answer = history 3 requests replies (.decoded 60 [0]) := by
  rw [verifyFramed_some]
  rfl

end TestsSecurity.BatchVerification
