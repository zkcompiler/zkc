module

public import ZkcSecurity.Transformations.Commitment.HashedLeaves

@[expose] public section

/-! # Recorded binary frontier reductions

This is a relation on hash-call records, not a second verifier. A `Layer` relates a sorted
frontier to its parents, consuming boundary siblings in ascending parent/child order. Two active
siblings share one recorded compression. `Reduction` repeats layers to a single root and requires
the entire supplied sibling sequence to be consumed. The tree depth and the requested positions
are parameters, never data read from the proof.

`Reduction.paths` recovers an existing `LeafHashing.Climbs` witness for every frontier member.
`batch_agrees_or_collision` covers the original ordered requests, including repeats, using one
shared reduction. It assumes neither an injective hash nor independent leaf and node hashes.
Its collision alternative concerns complete queries in the supplied log. Relating that log to
native Poseidon2 or Keccak calls and bounding its collision event are separate obligations.

The relation covers a binary tree over one row table. Native admission must additionally check
the positive width/height, the actual height bound (which can be smaller than `2 ^ depth`), exact
row framing, codecs, resource refusals and use of the authentication Boolean. No native execution,
sampling, checkpoint, stage simulation or application-security claim is made here.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.BatchOpening

variable {Row Query Y : Type}

/-- Layer-local positions and their labels, in ascending position order. -/
abbrev Frontier (Y : Type) := List (ℕ × Y)

/-- The next positions and boundary count of a sorted binary frontier, without any hashes.
Native correspondence must show that its sorted unique positions follow this same layout. -/
def layout : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | [index] => ([index / 2], 1)
  | index :: next :: rest =>
      if index / 2 = next / 2 then
        let upper := layout rest
        (index / 2 :: upper.1, upper.2)
      else
        let upper := layout (next :: rest)
        (index / 2 :: upper.1, upper.2 + 1)

/-- Required boundary digest count, determined solely by depth and the active positions. -/
def proofCount : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | depth + 1, positions => (layout positions).2 + proofCount depth (layout positions).1

/-- One binary layer of a recorded frontier reduction. The last list is the unconsumed proof.
`after` prevents a boundary rule from ignoring an active sibling or reordering parents. -/
inductive Layer (model : LeafHashing Row Query Y) (log : HashLog Query Y) :
    Frontier Y → List Y → Frontier Y → List Y → Prop
  | nil (proof : List Y) : Layer model log [] proof [] proof
  | shared {p : ℕ} {left right up : Y} {rest above : Frontier Y} {proof tail : List Y}
      (after : ∀ entry ∈ rest, 2 * p + 1 < entry.1)
      (recorded : (⟨model.node left right, up⟩ : (_ : Query) × Y) ∈ log)
      (next : Layer model log rest proof above tail) :
      Layer model log ((2 * p, left) :: (2 * p + 1, right) :: rest) proof
        ((p, up) :: above) tail
  | left {p : ℕ} {left right up : Y} {rest above : Frontier Y} {proof tail : List Y}
      (after : ∀ entry ∈ rest, 2 * p + 1 < entry.1)
      (recorded : (⟨model.node left right, up⟩ : (_ : Query) × Y) ∈ log)
      (next : Layer model log rest proof above tail) :
      Layer model log ((2 * p, left) :: rest) (right :: proof) ((p, up) :: above) tail
  | right {p : ℕ} {left right up : Y} {rest above : Frontier Y} {proof tail : List Y}
      (after : ∀ entry ∈ rest, 2 * p + 1 < entry.1)
      (recorded : (⟨model.node left right, up⟩ : (_ : Query) × Y) ∈ log)
      (next : Layer model log rest proof above tail) :
      Layer model log ((2 * p + 1, right) :: rest) (left :: proof) ((p, up) :: above) tail

namespace Layer

/-- A recorded layer remains recorded in a larger joint hash log. -/
theorem mono {model : LeafHashing Row Query Y} {log larger : HashLog Query Y}
    (included : ∀ entry ∈ log, entry ∈ larger)
    {below above : Frontier Y} {proof tail : List Y}
    (layer : Layer model log below proof above tail) :
    Layer model larger below proof above tail := by
  induction layer with
  | nil => exact .nil _
  | shared after recorded _ ih => exact .shared after (included _ recorded) ih
  | left after recorded _ ih => exact .left after (included _ recorded) ih
  | right after recorded _ ih => exact .right after (included _ recorded) ih

/-- Each active child has a recorded parent, whether its sibling was active or supplied. -/
theorem covers {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {below above : Frontier Y} {proof tail : List Y}
    (layer : Layer model log below proof above tail) {index : ℕ} {label : Y}
    (member : (index, label) ∈ below) :
    ∃ sibling up, (index / 2, up) ∈ above ∧
      (⟨model.parent index label sibling, up⟩ : (_ : Query) × Y) ∈ log := by
  induction layer with
  | nil => simp at member
  | @shared p left right up rest above proof tail after recorded next ih =>
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | member
      · exact ⟨right, up, by simp, by simpa [LeafHashing.parent] using recorded⟩
      · exact ⟨left, up, by simp [show (2 * p + 1) / 2 = p by omega],
          by simpa [LeafHashing.parent] using recorded⟩
      · obtain ⟨sibling, parent, inAbove, inLog⟩ := ih member
        exact ⟨sibling, parent, List.mem_cons_of_mem _ inAbove, inLog⟩
  | @left p left right up rest above proof tail after recorded next ih =>
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | member
      · exact ⟨right, up, by simp, by simpa [LeafHashing.parent] using recorded⟩
      · obtain ⟨sibling, parent, inAbove, inLog⟩ := ih member
        exact ⟨sibling, parent, List.mem_cons_of_mem _ inAbove, inLog⟩
  | @right p left right up rest above proof tail after recorded next ih =>
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | member
      · exact ⟨left, up, by simp [show (2 * p + 1) / 2 = p by omega],
          by simpa [LeafHashing.parent] using recorded⟩
      · obtain ⟨sibling, parent, inAbove, inLog⟩ := ih member
        exact ⟨sibling, parent, List.mem_cons_of_mem _ inAbove, inLog⟩

/-- A layer consumes a prefix; it cannot invent, permute or discard the remaining proof. -/
theorem proof_suffix {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {below above : Frontier Y} {proof tail : List Y}
    (layer : Layer model log below proof above tail) : ∃ used, proof = used ++ tail := by
  induction layer with
  | nil => exact ⟨[], rfl⟩
  | shared _ _ _ ih => exact ih
  | @left _ _ right _ _ _ _ _ _ _ _ ih =>
      obtain ⟨used, rfl⟩ := ih
      exact ⟨right :: used, rfl⟩
  | @right _ left _ _ _ _ _ _ _ _ _ ih =>
      obtain ⟨used, rfl⟩ := ih
      exact ⟨left :: used, rfl⟩

/-- Boundary digests are counted exactly: each parent has two children, supplied or active. -/
theorem length_balance {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {below above : Frontier Y} {proof tail : List Y}
    (layer : Layer model log below proof above tail) :
    proof.length + below.length = tail.length + 2 * above.length := by
  induction layer with
  | nil => simp
  | shared _ _ _ ih => simp only [List.length_cons] at *; omega
  | left _ _ _ ih => simp only [List.length_cons] at *; omega
  | right _ _ _ ih => simp only [List.length_cons] at *; omega

/-- Both the parent positions and the exact number of consumed siblings are shape determined. -/
theorem layout_eq {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {below above : Frontier Y} {proof tail : List Y}
    (layer : Layer model log below proof above tail) :
    (layout (below.map Prod.fst)).1 = above.map Prod.fst ∧
      proof.length = tail.length + (layout (below.map Prod.fst)).2 := by
  induction layer with
  | nil => simp [layout]
  | @shared p left right up rest above proof tail after recorded next ih =>
      have even : 2 * p / 2 = p := by omega
      have odd : (2 * p + 1) / 2 = p := by omega
      simp only [List.map_cons, layout, even, odd, ↓reduceIte]
      exact ⟨congrArg (List.cons p) ih.1, ih.2⟩
  | @left p left right up rest above proof tail after recorded next ih =>
      have even : 2 * p / 2 = p := by omega
      cases rest with
      | nil =>
          simp only [List.map_nil, layout, List.length_cons, even, List.map_cons] at *
          exact ⟨by rw [← ih.1], by omega⟩
      | cons entry rest =>
          simp only [List.map_cons] at ih
          have later := after entry List.mem_cons_self
          have different : p ≠ entry.1 / 2 := by omega
          simp only [List.map_cons, layout, even, different, ↓reduceIte, List.length_cons]
          exact ⟨congrArg (List.cons p) ih.1, by omega⟩
  | @right p left right up rest above proof tail after recorded next ih =>
      have odd : (2 * p + 1) / 2 = p := by omega
      cases rest with
      | nil =>
          simp only [List.map_nil, layout, List.length_cons, odd, List.map_cons] at *
          exact ⟨by rw [← ih.1], by omega⟩
      | cons entry rest =>
          simp only [List.map_cons] at ih
          have later := after entry List.mem_cons_self
          have different : p ≠ entry.1 / 2 := by omega
          simp only [List.map_cons, layout, odd, different, ↓reduceIte, List.length_cons]
          exact ⟨congrArg (List.cons p) ih.1, by omega⟩

end Layer

/-- Exactly `depth` recorded layers ending at the requested root, with no proof left over. -/
inductive Reduction (model : LeafHashing Row Query Y) (log : HashLog Query Y) :
    ℕ → Frontier Y → List Y → Y → Prop
  | root (root : Y) : Reduction model log 0 [(0, root)] [] root
  | step {depth : ℕ} {below above : Frontier Y} {proof tail : List Y} {root : Y}
      (layer : Layer model log below proof above tail)
      (next : Reduction model log depth above tail root) :
      Reduction model log (depth + 1) below proof root

namespace Reduction

/-- Shared authentication recorded locally can be placed in the full execution log. -/
theorem mono {model : LeafHashing Row Query Y} {log larger : HashLog Query Y}
    (included : ∀ entry ∈ log, entry ∈ larger)
    {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    (reduction : Reduction model log depth frontier proof root) :
    Reduction model larger depth frontier proof root := by
  induction reduction with
  | root => exact .root _
  | step layer _ ih => exact .step (layer.mono included) ih

/-- Ending at one root cannot authenticate an empty frontier. -/
theorem nonempty {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    (reduction : Reduction model log depth frontier proof root) : frontier ≠ [] := by
  induction reduction with
  | root => simp
  | step layer _ ih =>
      intro empty
      subst empty
      cases layer
      exact ih rfl

/-- Shared authentication work yields a complete recorded path for every active leaf.
The position bound follows from ending at root index zero after exactly `depth` layers. -/
theorem paths {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    (reduction : Reduction model log depth frontier proof root) {index : ℕ} {label : Y}
    (member : (index, label) ∈ frontier) :
    index < 2 ^ depth ∧ ∃ path, path.length = depth ∧
      model.Climbs log index path label root := by
  induction reduction generalizing index label with
  | root root =>
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact ⟨by decide, [], rfl, rfl⟩
  | @step depth below above proof tail root layer next ih =>
      obtain ⟨sibling, up, inAbove, inLog⟩ := layer.covers member
      obtain ⟨bound, path, length, climbs⟩ := ih inAbove
      refine ⟨?_, sibling :: path, by simp [length], up, inLog, climbs⟩
      rw [pow_succ]
      omega

/-- At depth zero only the exact singleton root and an empty proof can be admitted. -/
theorem zero_iff {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {frontier : Frontier Y} {proof : List Y} {root : Y} :
    Reduction model log 0 frontier proof root ↔ frontier = [(0, root)] ∧ proof = [] := by
  constructor
  · intro reduction
    cases reduction
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .root root

/-- Complete proof consumption has a fixed length; short and surplus proofs cannot reduce. -/
theorem proof_length {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    (reduction : Reduction model log depth frontier proof root) :
    proof.length = proofCount depth (frontier.map Prod.fst) := by
  induction reduction with
  | root => rfl
  | step layer next ih =>
      obtain ⟨positions, count⟩ := layer.layout_eq
      simp only [proofCount, positions]
      omega

end Reduction

/-- The original request list is covered by recorded leaf hashes in the shared frontier.
`Forall₂` retains exact lengths, order and every repeated request; no `zip` truncation occurs. -/
def RowsRecorded (model : LeafHashing Row Query Y) (log : HashLog Query Y)
    (frontier : Frontier Y) (positions : List ℕ) (rows : List Row) : Prop :=
  List.Forall₂ (fun index row ↦ ∃ label, (index, label) ∈ frontier ∧
    (⟨model.leaf row, label⟩ : (_ : Query) × Y) ∈ log) positions rows

/-- A concrete collision between distinct complete hash queries in the record. -/
def Collision (log : HashLog Query Y) : Prop :=
  ∃ first ∈ log, ∃ second ∈ log, first.1 ≠ second.1 ∧ first.2 = second.2

/-- The existing extractor's record premise is exactly exclusion of recorded collisions. -/
theorem responseInjective_iff {log : HashLog Query Y} :
    MerkleTreeExtractor.ResponseInjectiveOn log ↔ ¬ Collision log := by
  constructor
  · intro injective ⟨first, firstMem, second, secondMem, different, same⟩
    exact different (injective first firstMem second secondMem same)
  · intro noCollision first firstMem second secondMem same
    by_contra different
    exact noCollision ⟨first, firstMem, second, secondMem, different, same⟩

/-- One shared frontier reduction authenticates the exact ordered batch in the extracted table.
Each decoding role must be consistent; cross-role aliases are permitted. -/
theorem batch_agrees_of_decoderConsistent [DecidableEq Y] {model : LeafHashing Row Query Y}
    {log : HashLog Query Y} {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    {positions : List ℕ} {rows : List Row}
    (reduction : Reduction model log depth frontier proof root)
    (recorded : RowsRecorded model log frontier positions rows)
    (nodes : DecoderConsistent model.children log)
    (leaves : DecoderConsistent model.leafRow log) :
    positions.map (model.extract log depth root) = rows.map some := by
  induction recorded with
  | nil => rfl
  | @cons index row positions rows head rest ih =>
      obtain ⟨label, inFrontier, inLog⟩ := head
      obtain ⟨bound, path, length, climbs⟩ := reduction.paths inFrontier
      have recovered := model.extractLabel_of_climbs_of_decoderConsistent nodes depth index path label root
        length bound climbs
      have entry : model.extract log depth root index = some row := by
        simp only [LeafHashing.extract, bound, ↓reduceIte, recovered, Option.bind_some]
        exact model.findRow_of_mem_of_decoderConsistent leaves inLog (model.leafRow_leaf row)
      simp only [List.map_cons, entry, ih]

/-- Global response injectivity supplies both role-specific consistency laws. -/
theorem batch_agrees [DecidableEq Y] {model : LeafHashing Row Query Y}
    {log : HashLog Query Y} {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    {positions : List ℕ} {rows : List Row}
    (reduction : Reduction model log depth frontier proof root)
    (recorded : RowsRecorded model log frontier positions rows)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log) :
    positions.map (model.extract log depth root) = rows.map some :=
  batch_agrees_of_decoderConsistent reduction recorded
    (.of_responseInjective model.children injective)
    (.of_responseInjective model.leafRow injective)

/-- Deterministic batch consistency or an explicit collision in the shared record. -/
theorem batch_agrees_or_collision [DecidableEq Y] {model : LeafHashing Row Query Y}
    {log : HashLog Query Y} {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    {positions : List ℕ} {rows : List Row}
    (reduction : Reduction model log depth frontier proof root)
    (recorded : RowsRecorded model log frontier positions rows) :
    positions.map (model.extract log depth root) = rows.map some ∨ Collision log := by
  classical
  by_cases collision : Collision log
  · exact Or.inr collision
  · exact Or.inl (batch_agrees reduction recorded (responseInjective_iff.mpr collision))

/-- Any disagreement of the entire ordered batch with extraction witnesses a recorded collision. -/
theorem disagreement_collision [DecidableEq Y] {model : LeafHashing Row Query Y}
    {log : HashLog Query Y} {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    {positions : List ℕ} {rows : List Row}
    (reduction : Reduction model log depth frontier proof root)
    (recorded : RowsRecorded model log frontier positions rows)
    (different : positions.map (model.extract log depth root) ≠ rows.map some) : Collision log :=
  (batch_agrees_or_collision reduction recorded).resolve_left different

end ZkcSecurity.Commitment.BatchOpening
