module

public import ZkcSecurity.Commitment.Extractable
public import ZkcSecurity.Commitment.TableLog
public import VCVio.CryptoFoundations.MerkleTree.ExtractionKernel
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Evolution
public import ToMathlib.Data.IndexedBinaryTree.Perfect

@[expose] public section

/-! # Merkle trees as extractable table commitments

A table of `2 ^ height` entries is committed by the root of a Merkle tree over the perfect binary
skeleton of that height, with raw leaves: entry `value` is the leaf label `leafLabel value`, and
`leafValue` reads it back. Internal nodes are hashed through VCVio's complete-query model
(`MerkleTreeExtractability.NodeQueryModel`), with the address of every internal position given
by the commitment's shape; positions are read from the most significant bit down
(`SkeletonLeafIndex.ofNat`).

* `authenticate` is VCVio's addressed opening verifier (`MerkleTreeExtractability.verifyOpening`);
  it rejects positions outside the table and paths of the wrong length.
* `extract` reads the table from VCVio's transcript extractor (`MerkleTreeExtractor.tree`): the
  entry at a position is the extracted leaf label, decoded.

`scheme` proves the two laws of `Extractable` from VCVio's deterministic extraction lemmas:
collision-free recovery along an authentication chain (`opening_eq_of_chainInLogAt`) and the
causal evolution of extraction (`tree_append_singleton_eq_of_mem`,
`tree_ne_append_singleton_implies_response_mem_targets`, `mem_targets_root_or_log_input`). A table
run of the verifier records its authentication chain (`chainInLogAt_putativeRoot`).

Leaves are raw: a scheme that hashes leaves with a separate function needs a leaf layer with its
own recovery step, which this module does not provide.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec BinaryTree InductiveMerkleTree

variable {Shape Value Query Address Y : Type}

/-- Merkle trees over perfect binary skeletons with raw leaves. -/
structure MerkleTrees (Shape Value Query Address Y : Type) where
  /-- The hash calls of internal nodes and their extraction view. -/
  model : MerkleTreeExtractability.NodeQueryModel Query Address Y
  /-- The tree height of a commitment of each shape; the table has `2 ^ height` entries. -/
  height : Shape → ℕ
  /-- The hash-call address of every internal position. -/
  address : (shape : Shape) → SkeletonInternalIndex (Skeleton.perfect (height shape)) → Address
  /-- The leaf label committing an entry. -/
  leafLabel : Value → Y
  /-- The entry a leaf label commits, if any. -/
  leafValue : Y → Option Value
  leafValue_leafLabel : ∀ value, leafValue (leafLabel value) = some value

namespace MerkleTrees

section Chain

/-- An authentication chain recorded in a log stays recorded in every larger log. -/
theorem chainInLogAt_mono (view : MerkleTreeExtractor.QueryView Query Address Y)
    {log larger : HashLog Query Y} (included : ∀ entry ∈ log, entry ∈ larger) (leaf : Y) :
    ∀ {s : Skeleton} (addressKey : SkeletonInternalIndex s → Address) (root : Y)
      (idx : SkeletonLeafIndex s) (proof : List.Vector Y idx.depth),
      MerkleTreeExtractor.ChainInLogAt view log leaf addressKey root idx proof →
        MerkleTreeExtractor.ChainInLogAt view larger leaf addressKey root idx proof := by
  intro s addressKey root idx
  induction idx generalizing root with
  | ofLeaf => intro proof chain; exact chain
  | ofLeft idx ih =>
      intro proof chain
      obtain ⟨query, ancestor, address, input, member, rest⟩ := chain
      exact ⟨query, ancestor, address, input, included _ member,
        ih (fun position => addressKey (.ofLeft position)) ancestor proof.tail rest⟩
  | ofRight idx ih =>
      intro proof chain
      obtain ⟨query, ancestor, address, input, member, rest⟩ := chain
      exact ⟨query, ancestor, address, input, included _ member,
        ih (fun position => addressKey (.ofRight position)) ancestor proof.tail rest⟩

/-- Recomputing a root against a complete answer table records an authentication chain from the
leaf to the recomputed root. -/
theorem chainInLogAt_putativeRoot [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) (answer : Query → Y) :
    ∀ {s : Skeleton} (addressKey : SkeletonInternalIndex s → Address)
      (idx : SkeletonLeafIndex s) (leaf : Y) (proof : List.Vector Y idx.depth),
      MerkleTreeExtractor.ChainInLogAt model.view
        (tableQueryLog (AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            (liftM ((Query →ₒ Y).query (model.mkQuery (addressKey position) (left, right))) :
              OracleComp (Query →ₒ Y) Y)) idx leaf proof) answer)
        leaf addressKey
        (evalWithAnswerFn (QueryImpl.ofFn answer) (AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            (liftM ((Query →ₒ Y).query (model.mkQuery (addressKey position) (left, right))) :
              OracleComp (Query →ₒ Y) Y)) idx leaf proof))
        idx proof := by
  intro s addressKey idx
  induction idx with
  | ofLeaf => intro leaf proof; rfl
  | @ofLeft left right idx ih =>
      intro leaf proof
      have inner := ih (fun position => addressKey (.ofLeft position)) leaf proof.tail
      simp only [AddressedMerkleTree.getPutativeRootAddressedM, tableQueryLog_bind,
        evalWithAnswerFn_bind, tableQueryLog_query, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply]
      refine ⟨_, _, model.address_mkQuery _ _, model.input_mkQuery _ _,
        List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      exact chainInLogAt_mono model.view (fun entry member => List.mem_append_left _ member)
        leaf _ _ idx proof.tail inner
  | @ofRight left right idx ih =>
      intro leaf proof
      have inner := ih (fun position => addressKey (.ofRight position)) leaf proof.tail
      simp only [AddressedMerkleTree.getPutativeRootAddressedM, tableQueryLog_bind,
        evalWithAnswerFn_bind, tableQueryLog_query, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply]
      refine ⟨_, _, model.address_mkQuery _ _, model.input_mkQuery _ _,
        List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      exact chainInLogAt_mono model.view (fun entry member => List.mem_append_left _ member)
        leaf _ _ idx proof.tail inner

end Chain

variable [DecidableEq Address] [DecidableEq Y] (trees : MerkleTrees Shape Value Query Address Y)

/-- The partial tree extracted for `root` from a record of hash calls. -/
def tree (log : HashLog Query Y) (shape : Shape) (root : Y) :
    FullData (Option Y) (Skeleton.perfect (trees.height shape)) :=
  MerkleTreeExtractor.tree trees.model.view (Skeleton.perfect (trees.height shape))
    (trees.address shape) log root

/-- The table extracted for `root`: the decoded leaf at every position of the tree. -/
def extract (log : HashLog Query Y) (shape : Shape) (root : Y) : Table Value := fun position =>
  if position < 2 ^ trees.height shape then
    ((trees.tree log shape root).get
      (SkeletonLeafIndex.ofNat (trees.height shape) position).toNodeIndex).bind trees.leafValue
  else none

/-- Authenticate an opening with VCVio's addressed opening verifier. -/
def authenticate (shape : Shape) (root : Y) (position : ℕ) (opening : Opening Value Y) :
    OracleComp (Query →ₒ Y) Bool :=
  if valid : position < 2 ^ trees.height shape ∧ opening.path.length = trees.height shape then
    MerkleTreeExtractability.verifyOpening trees.model (trees.address shape)
      (SkeletonLeafIndex.ofNat (trees.height shape) position) (trees.leafLabel opening.value) root
      ⟨opening.path, by rw [SkeletonLeafIndex.depth_ofNat]; exact valid.2⟩
  else pure false

/-- Equal extracted trees give equal extracted tables. -/
theorem extract_congr {log other : HashLog Query Y} {shape : Shape} {root : Y}
    (same : trees.tree log shape root = trees.tree other shape root) :
    trees.extract log shape root = trees.extract other shape root := by
  funext position
  simp only [extract, same]

theorem opening_agrees (answer : Query → Y) (log : HashLog Query Y) (shape : Shape) (root : Y)
    (position : ℕ) (opening : Opening Value Y)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log)
    (recorded : ∀ entry ∈ tableQueryLog (trees.authenticate shape root position opening) answer,
      entry ∈ log)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (trees.authenticate shape root position opening) = true) :
    trees.extract log shape root position = some opening.value := by
  unfold authenticate at recorded accepted
  split at accepted
  · rename_i valid
    simp only [valid, and_self, ↓reduceDIte] at recorded
    simp only [MerkleTreeExtractability.verifyOpening, tableQueryLog_bind, tableQueryLog_pure,
      List.append_nil, evalWithAnswerFn_bind, evalWithAnswerFn_pure, beq_iff_eq] at recorded accepted
    have chain := chainInLogAt_putativeRoot trees.model answer (trees.address shape)
      (SkeletonLeafIndex.ofNat (trees.height shape) position) (trees.leafLabel opening.value)
      ⟨opening.path, by rw [SkeletonLeafIndex.depth_ofNat]; exact valid.2⟩
    rw [accepted] at chain
    have recovered := (MerkleTreeExtractor.opening_eq_of_chainInLogAt trees.model.view log
      injective (trees.address shape) root (trees.leafLabel opening.value) _ _
      (chainInLogAt_mono trees.model.view recorded _ _ _ _ _ chain)).1
    simp only [extract, valid.1, ↓reduceIte]
    change (MerkleTreeExtractor.treeAt trees.model.view _ _ log root).get _ >>= _ = _ at *
    rw [recovered]
    exact trees.leafValue_leafLabel opening.value
  · simp at accepted

theorem extract_append (log : HashLog Query Y) (entry : (_ : Query) × Y) (shape : Shape)
    (root : Y) (changed : trees.extract (log ++ [entry]) shape root ≠ trees.extract log shape root) :
    entry ∉ log ∧ (entry.2 = root ∨ ∃ recorded ∈ log,
      entry.2 ∈ [(trees.model.view.input recorded.1).1, (trees.model.view.input recorded.1).2]) := by
  have treeChanged : trees.tree log shape root ≠ trees.tree (log ++ [entry]) shape root :=
    fun same => changed (trees.extract_congr same.symm)
  refine ⟨fun member => treeChanged
    (MerkleTreeMultiExtractability.tree_append_singleton_eq_of_mem trees.model.view _
      (trees.address shape) log root entry member).symm, ?_⟩
  have target := MerkleTreeMultiExtractability.tree_ne_append_singleton_implies_response_mem_targets
    trees.model.view _ (trees.address shape) log root entry.1 entry.2 treeChanged
  rcases MerkleTreeExtractor.mem_targets_root_or_log_input trees.model.view _ _ log root target with
    isRoot | ⟨recorded, member, isInput⟩
  · exact Or.inl isRoot
  · refine Or.inr ⟨recorded, member, ?_⟩
    rcases isInput with first | second
    · rw [first]; exact List.mem_cons_self
    · rw [second]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Merkle trees with raw leaves as an extractable table commitment. -/
def scheme : Extractable Shape Value Query Y where
  authenticate := trees.authenticate
  extract := trees.extract
  inputs query := [(trees.model.view.input query).1, (trees.model.view.input query).2]
  opening_agrees := trees.opening_agrees
  extract_append := trees.extract_append

/-- Every hash call exposes two input labels. -/
theorem scheme_inputs_length (query : Query) : (trees.scheme.inputs query).length = 2 := rfl

end MerkleTrees

end ZkcSecurity.Commitment
