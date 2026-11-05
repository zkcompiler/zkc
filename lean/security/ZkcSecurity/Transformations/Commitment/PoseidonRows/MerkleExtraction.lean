module

public import ZkcSecurity.Transformations.Commitment.PoseidonRows.OverwriteSponge
public import Mathlib.Data.Nat.Log

@[expose] public section

/-! # Merkle extraction from the shared permutation record

The two macro roles below are presentation syntax, not native domain separation. A final sponge
call also has a node interpretation, including the width-eight leaf/node alias. Only consistency
within each decoder role is proved or needed. Existing Merkle descent and batch proofs are reused.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {F : Type} {rate : ℕ} [Zero F] [DecidableEq F]

inductive MacroQuery (F : Type) (rate : ℕ) where
  | leaf (row : List F)
  | node (left right : Digest F rate)
  deriving DecidableEq

def hashing : LeafHashing (List F) (MacroQuery F rate) (Digest F rate) where
  leaf := .leaf
  node := .node
  leafRow := fun q ↦ match q with | .leaf row => some row | .node _ _ => none
  children := fun q ↦ match q with | .leaf _ => none | .node l r => some (l, r)
  leafRow_leaf := fun _ ↦ rfl
  children_node := fun _ _ ↦ rfl

/-- Emit a node and, only when the fixed backward reconstruction succeeds, a leaf. -/
def macrosAt (log : List (Exposure F rate)) (width : Width rate) (e : Exposure F rate) :
    HashLog (MacroQuery F rate) (Digest F rate) :=
  if e.forward then
    [⟨.node e.input.1 e.input.2, e.output.1⟩] ++
      match recover log width.full width.tail e with
      | none => []
      | some row => [⟨.leaf row, e.output.1⟩]
  else []

def macroLog (log : List (Exposure F rate)) (width : Width rate) :
    HashLog (MacroQuery F rate) (Digest F rate) := log.flatMap (macrosAt log width)

theorem mem_macrosAt {log : List (Exposure F rate)} {width : Width rate}
    {e : Exposure F rate} {entry : (_ : MacroQuery F rate) × Digest F rate} :
    entry ∈ macrosAt log width e ↔ e.forward = true ∧ entry.2 = e.output.1 ∧
      (entry.1 = .node e.input.1 e.input.2 ∨
        ∃ row, recover log width.full width.tail e = some row ∧ entry.1 = .leaf row) := by
  obtain ⟨query, answer⟩ := entry
  cases forward : e.forward <;> cases decoded : recover log width.full width.tail e <;>
    simp [macrosAt, forward, decoded, and_comm, or_and_right]

theorem macro_source {log : List (Exposure F rate)} {width : Width rate}
    {entry : (_ : MacroQuery F rate) × Digest F rate}
    (member : entry ∈ macroLog log width) :
    ∃ e ∈ log, e.forward = true ∧ entry.2 = e.output.1 ∧
      (entry.1 = .node e.input.1 e.input.2 ∨
        ∃ row, recover log width.full width.tail e = some row ∧ entry.1 = .leaf row) := by
  obtain ⟨e, member, atEndpoint⟩ := List.mem_flatMap.mp member
  exact ⟨e, member, mem_macrosAt.mp atEndpoint⟩

theorem node_mem {log : List (Exposure F rate)} {width : Width rate} {e : Exposure F rate}
    (member : e ∈ log) (forward : e.forward = true) :
    (⟨.node e.input.1 e.input.2, e.output.1⟩ : (_ : MacroQuery F rate) × Digest F rate) ∈
      macroLog log width := by
  exact List.mem_flatMap.mpr ⟨e, member, mem_macrosAt.mpr ⟨forward, rfl, Or.inl rfl⟩⟩

theorem leaf_mem {log : List (Exposure F rate)} {width : Width rate} {e : Exposure F rate}
    {row : List F} (good : Good log) (trace : SpongeTrace log width.full width.tail e row) :
    (⟨.leaf row, e.output.1⟩ : (_ : MacroQuery F rate) × Digest F rate) ∈
      macroLog log width := by
  exact List.mem_flatMap.mpr ⟨e, trace.member, mem_macrosAt.mpr
    ⟨trace.forward good, rfl, Or.inr ⟨row, trace.recover good width.bounded, rfl⟩⟩⟩

/-- Equal labels identify the same primitive endpoint, while allowing different macro roles. -/
theorem decoder_consistent {log : List (Exposure F rate)} (good : Good log)
    (width : Width rate) :
    DecoderConsistent (hashing (F := F) (rate := rate)).children (macroLog log width) ∧
      DecoderConsistent (hashing (F := F) (rate := rate)).leafRow (macroLog log width) := by
  constructor
  · intro first fm second sm fv sv fd sd same
    obtain ⟨a, am, af, ay, aq⟩ := macro_source fm
    obtain ⟨b, bm, bf, byLabel, bq⟩ := macro_source sm
    have equal := good.rate_unique am bm af bf (ay.symm.trans (same.trans byLabel))
    subst b
    rcases aq with aq | ⟨row, _, aq⟩
    · rcases bq with bq | ⟨row, _, bq⟩
      · simp only [aq, hashing, Option.some.injEq] at fd
        simp only [bq, hashing, Option.some.injEq] at sd
        exact fd.symm.trans sd
      · simp [bq, hashing] at sd
    · simp [aq, hashing] at fd
  · intro first fm second sm fv sv fd sd same
    obtain ⟨a, am, af, ay, aq⟩ := macro_source fm
    obtain ⟨b, bm, bf, byLabel, bq⟩ := macro_source sm
    have equal := good.rate_unique am bm af bf (ay.symm.trans (same.trans byLabel))
    subst b
    rcases aq with aq | ⟨row, recovered, aq⟩
    · simp [aq, hashing] at fd
    · rcases bq with bq | ⟨other, recoveredOther, bq⟩
      · simp [bq, hashing] at sd
      · have rows : row = other := Option.some.inj (recovered.symm.trans recoveredOther)
        simp only [aq, hashing, Option.some.injEq] at fd
        simp only [bq, hashing, Option.some.injEq] at sd
        exact fd.symm.trans (rows.trans sd)

/-- The request's depth and actual height are fixed before extraction. -/
structure Request (rate : ℕ) where
  width : Width rate
  height : ℕ
  depth : ℕ
  heightPositive : 0 < height
  heightBound : height ≤ 2 ^ depth

/-- The actual-height constructor selects the minimal binary depth, not a padded height. -/
def Request.ofHeight (width : Width rate) (height : ℕ) (positive : 0 < height) : Request rate where
  width := width
  height := height
  depth := Nat.clog 2 height
  heightPositive := positive
  heightBound := Nat.le_pow_clog (by omega) height

/-- Straight-line total table extraction, restricted to actual height, with no oracle calls. -/
def extract (request : Request rate) (log : List (Exposure F rate)) (root : Digest F rate) :
    Table (List F) := fun i ↦
  if i < request.height then hashing.extract (macroLog log request.width) request.depth root i
  else none

/-- Each absent entry has the same fixed zero completion; other entries remain intact. -/
def complete (request : Request rate) (log : List (Exposure F rate)) (root : Digest F rate)
    (i : ℕ) : List F := (extract request log root i).getD (List.replicate request.width.length 0)

theorem complete_present {request : Request rate} {log : List (Exposure F rate)}
    {root : Digest F rate} {i : ℕ} {row : List F} (found : extract request log root i = some row) :
    complete request log root i = row := by simp [complete, found]

theorem complete_absent {request : Request rate} {log : List (Exposure F rate)}
    {root : Digest F rate} {i : ℕ} (absent : extract request log root i = none) :
    complete request log root i = List.replicate request.width.length 0 := by
  simp [complete, absent]

/-- Actual recorded node climbs. Siblings may be opaque; only the active branch is needed. -/
inductive NodeClimb (log : List (Exposure F rate)) :
    ℕ → List (Digest F rate) → Exposure F rate → Digest F rate → Prop
  | nil {index : ℕ} {e : Exposure F rate} : NodeClimb log index [] e e.output.1
  | step {index : ℕ} {siblings : List (Digest F rate)} {child parent : Exposure F rate}
      (sibling : Digest F rate) (member : parent ∈ log)
      (input : parent.input = if index % 2 = 0 then (child.output.1, sibling)
        else (sibling, child.output.1))
      {root : Digest F rate} (rest : NodeClimb log (index / 2) siblings parent root) :
      NodeClimb log index (sibling :: siblings) child root

theorem NodeClimb.recorded {log : List (Exposure F rate)} (good : Good log) (width : Width rate)
    {index : ℕ} {siblings : List (Digest F rate)} {e : Exposure F rate} {root : Digest F rate}
    (member : e ∈ log) (forward : e.forward = true)
    (climb : NodeClimb log index siblings e root) :
    LeafHashing.Climbs hashing (macroLog log width) index siblings e.output.1 root := by
  induction climb with
  | nil => rfl
  | @step index siblings child parent sibling pm input root rest ih =>
      have link : parent.input.1 = child.output.1 ∨ parent.input.2 = child.output.1 := by
        rw [input]
        split <;> simp
      have pf := good.parent_forward member pm forward link
      refine ⟨parent.output.1, ?_, ih pm pf⟩
      have mem := node_mem (width := width) pm pf
      by_cases bit : index % 2 = 0 <;>
        simpa [LeafHashing.parent, hashing, input, bit] using mem

/-- Deterministic single-opening agreement, derived from actual primitive sponge and node data. -/
theorem opening_agrees {request : Request rate} {log : List (Exposure F rate)}
    (good : Good log) {e : Exposure F rate} {row : List F} {index : ℕ}
    {siblings : List (Digest F rate)} {root : Digest F rate}
    (trace : SpongeTrace log request.width.full request.width.tail e row)
    (climb : NodeClimb log index siblings e root) (length : siblings.length = request.depth)
    (range : index < request.height) : extract request log root index = some row := by
  have roles := decoder_consistent good request.width
  have recorded := climb.recorded good request.width trace.member (trace.forward good)
  have below : index < 2 ^ request.depth := Nat.lt_of_lt_of_le range request.heightBound
  have descended := hashing.extractLabel_of_climbs_of_decoderConsistent roles.1
    request.depth index siblings e.output.1 root length below recorded
  simp only [extract, range, ↓reduceIte, LeafHashing.extract, below, descended, Option.bind_some]
  exact hashing.findRow_of_mem_of_decoderConsistent roles.2 (leaf_mem good trace) rfl

/-- Reuse the existing shared-frontier proof with role-specific consistency and actual height.
The operational producer must still supply its exact Reduction/RowsRecorded correspondence. -/
theorem batch_agrees {request : Request rate} {log : List (Exposure F rate)} (good : Good log)
    {frontier : BatchOpening.Frontier (Digest F rate)} {proof : List (Digest F rate)}
    {root : Digest F rate} {positions : List ℕ} {rows : List (List F)}
    (reduction : BatchOpening.Reduction hashing (macroLog log request.width)
      request.depth frontier proof root)
    (recorded : BatchOpening.RowsRecorded hashing (macroLog log request.width)
      frontier positions rows)
    (range : ∀ i ∈ positions, i < request.height) :
    positions.map (extract request log root) = rows.map some := by
  have roles := decoder_consistent good request.width
  rw [← BatchOpening.batch_agrees_of_decoderConsistent reduction recorded roles.1 roles.2]
  apply List.map_congr_left
  intro i member
  simp [extract, range i member]

end ZkcSecurity.Commitment.PoseidonRows
