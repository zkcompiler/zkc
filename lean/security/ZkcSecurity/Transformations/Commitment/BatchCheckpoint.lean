module

public import ZkcSecurity.Transformations.Commitment.BatchVerification
public import ZkcSecurity.Transformations.Commitment.Record

@[expose] public section

/-! # Batch authentication at a transcript checkpoint

The batch operation contributes its actual shared-node hash calls to one joint record.
Outside the existing record's collision and extraction-drift event, its ordered rows
agree with the table extracted before the first query of the selected transcript key.
No scalar authentication calls are inserted or replayed. The source adapter remains
responsible for embedding the actual operation log and the committed root into this
joint experiment; these are explicit premises rather than inferred source facts.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.BatchVerification

open OracleComp OracleSpec BatchOpening

variable {Row Query Y E : Type} {Raw : E → Type}

/-- Accepted rows agree with any record with consistent leaf and node decoding containing the
operation's own hash calls, not only with its local suffix. -/
theorem verify_agrees_in_record_of_decoderConsistent [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (root : Y) (proof : List Y) (log : HashLog Query Y)
    (included : ∀ entry ∈ tableQueryLog
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) answer, entry ∈ log)
    (nodes : DecoderConsistent model.children log)
    (leaves : DecoderConsistent model.leafRow log)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) = .returned true) :
    positions.map (model.extract log (Nat.clog 2 height) root) = rows.map some := by
  obtain ⟨_, _, _, _, _, frontier, _, reduction, recorded, _⟩ :=
    verify_success model validRow answer wordMax elementLimit width height positions rows
      root proof accepted
  apply batch_agrees_of_decoderConsistent (reduction.mono included) _ nodes leaves
  exact List.Forall₂.imp (fun _ _ ⟨label, present, queried⟩ ↦
    ⟨label, present, included _ queried⟩) recorded

/-- Response injectivity is one sufficient way to establish the two decoder
laws. The actual operation and extractor remain the same. -/
theorem verify_agrees_in_record [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (root : Y) (proof : List Y) (log : HashLog Query Y)
    (included : ∀ entry ∈ tableQueryLog
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) answer, entry ∈ log)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) = .returned true) :
    positions.map (model.extract log (Nat.clog 2 height) root) = rows.map some :=
  verify_agrees_in_record_of_decoderConsistent model validRow answer wordMax elementLimit
    width height positions rows root proof log included
    (.of_responseInjective model.children injective)
    (.of_responseInjective model.leafRow injective) accepted

/-- The existing joint-record invariant fixes every authenticated ordered row at
its pre-challenge extraction checkpoint, including duplicates and cached queries.
The root-bound and exact key-membership premises are owned by the source consumer. -/
theorem verify_agrees_at_checkpoint [DecidableEq Row] [DecidableEq Y]
    [DecidableEq E] [DecidableEq Query]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool)
    (wordMax elementLimit width height rootBound : ℕ)
    (positions : List ℕ) (rows : List Row) (root : Y) (proof : List Y)
    (table : JointTable Raw ℕ Y Query) (keys : List (JointKey E ℕ Y Query))
    (transcript : TranscriptKey E ℕ Y)
    (member : (.inl transcript : JointKey E ℕ Y Query) ∈ keys)
    (rooted : root ∈ keyRoots rootBound transcript)
    (good : GoodFrom model.scheme rootBound table [] keys)
    (included : ∀ entry ∈ tableQueryLog
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) (fun query ↦ table (.inr query)),
      entry ∈ hashLog table keys)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn (fun query ↦ table (.inr query)))
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) = .returned true) :
    positions.map (model.extract
      (hashLog table (beforeFirstKey (.inl transcript) keys)) (Nat.clog 2 height) root) =
        rows.map some := by
  have injective : MerkleTreeExtractor.ResponseInjectiveOn (hashLog table keys) := by
    simpa only [List.nil_append] using
      responseInjective_of_good model.scheme rootBound table [] keys (by simp [hashLog, MerkleTreeExtractor.ResponseInjectiveOn]) good
  have stable := extract_checkpoint_eq model.scheme rootBound table keys good transcript
    member (Nat.clog 2 height) rooted
  change model.extract _ _ _ = model.extract _ _ _ at stable
  rw [stable]
  exact verify_agrees_in_record model validRow _ wordMax elementLimit width height
    positions rows root proof _ included injective accepted

end ZkcSecurity.Commitment.BatchVerification
