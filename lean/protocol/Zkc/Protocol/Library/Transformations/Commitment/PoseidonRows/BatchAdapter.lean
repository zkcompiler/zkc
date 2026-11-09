module

public import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.RateEight

@[expose] public section

/-! # Shared-frontier transport from primitive records

The existing frontier relation is reused over full primitive input states, then transported to
derived macros. Every active leaf must have an actual recorded sponge trace. Opaque boundary
siblings need no preimage. No new verifier or protocol evaluator is introduced.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {F : Type} {rate : ℕ} [Zero F] [DecidableEq F]

/-- A structural use of the existing frontier relation over full compression inputs. -/
def compression : LeafHashing (State F rate) (State F rate) (Digest F rate) where
  leaf := id
  node := fun left right ↦ (left, right)
  leafRow := some
  children := some
  leafRow_leaf := fun _ ↦ rfl
  children_node := fun _ _ ↦ rfl

def primitiveLog (log : List (Exposure F rate)) : HashLog (State F rate) (Digest F rate) :=
  log.map fun e ↦ ⟨e.input, e.output.1⟩

def Active (log : List (Exposure F rate)) (frontier : BatchOpening.Frontier (Digest F rate)) :
    Prop := ∀ entry ∈ frontier, ∃ e ∈ log, e.forward = true ∧ e.output.1 = entry.2

omit [Zero F] [DecidableEq F] in
theorem Active.tail {log : List (Exposure F rate)} {head : ℕ × Digest F rate}
    {rest : BatchOpening.Frontier (Digest F rate)} (active : Active log (head :: rest)) :
    Active log rest := fun entry member ↦ active entry (List.mem_cons_of_mem _ member)

omit [Zero F] [DecidableEq F] in
theorem active_cons {log : List (Exposure F rate)} {head : ℕ × Digest F rate}
    {rest : BatchOpening.Frontier (Digest F rate)}
    (first : ∃ e ∈ log, e.forward = true ∧ e.output.1 = head.2) (active : Active log rest) :
    Active log (head :: rest) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · exact first
  · exact active entry member

omit [Zero F] [DecidableEq F] in
theorem primitive_member {log : List (Exposure F rate)} {input : State F rate}
    {label : Digest F rate}
    (member : (⟨input, label⟩ : (_ : State F rate) × Digest F rate) ∈ primitiveLog log) :
    ∃ e ∈ log, e.input = input ∧ e.output.1 = label := by
  obtain ⟨e, em, equal⟩ := List.mem_map.mp member
  cases equal
  exact ⟨e, em, rfl, rfl⟩

theorem node_from_active {log : List (Exposure F rate)} (good : Good log) (width : Width rate)
    {left right up : Digest F rate}
    (recorded : (⟨(left, right), up⟩ : (_ : State F rate) × Digest F rate) ∈ primitiveLog log)
    (active : ∃ child ∈ log, child.forward = true ∧
      (child.output.1 = left ∨ child.output.1 = right)) :
    (∃ e ∈ log, e.forward = true ∧ e.output.1 = up) ∧
      (⟨MacroQuery.node left right, up⟩ : (_ : MacroQuery F rate) × Digest F rate) ∈
        macroLog log width := by
  obtain ⟨child, cm, cf, link⟩ := active
  obtain ⟨parent, pm, input, output⟩ := primitive_member recorded
  have pf := good.parent_forward cm pm cf (by simpa [input, eq_comm] using link)
  exact ⟨⟨parent, pm, pf, output⟩,
    by simpa [input, output] using node_mem (width := width) pm pf⟩

/-- Transport each shared parent once, deriving forward relevance from one active child. -/
theorem layer_to_macros {log : List (Exposure F rate)} (good : Good log) (width : Width rate)
    {below above : BatchOpening.Frontier (Digest F rate)} {proof tail : List (Digest F rate)}
    (layer : BatchOpening.Layer compression (primitiveLog log) below proof above tail) :
    Active log below →
      BatchOpening.Layer hashing (macroLog log width) below proof above tail ∧ Active log above := by
  induction layer with
  | nil => exact fun _ ↦ ⟨.nil _, by simp [Active]⟩
  | @shared p left right up rest above proof tail after recorded next ih =>
      intro active
      obtain ⟨child, cm, cf, output⟩ := active (2 * p, left) (by simp)
      have node := node_from_active good width recorded ⟨child, cm, cf, Or.inl output⟩
      have remainder := ih active.tail.tail
      exact ⟨.shared after node.2 remainder.1, active_cons node.1 remainder.2⟩
  | @left p left right up rest above proof tail after recorded next ih =>
      intro active
      obtain ⟨child, cm, cf, output⟩ := active (2 * p, left) (by simp)
      have node := node_from_active good width recorded ⟨child, cm, cf, Or.inl output⟩
      have remainder := ih active.tail
      exact ⟨.left after node.2 remainder.1, active_cons node.1 remainder.2⟩
  | @right p left right up rest above proof tail after recorded next ih =>
      intro active
      obtain ⟨child, cm, cf, output⟩ := active (2 * p + 1, right) (by simp)
      have node := node_from_active good width recorded ⟨child, cm, cf, Or.inr output⟩
      have remainder := ih active.tail
      exact ⟨.right after node.2 remainder.1, active_cons node.1 remainder.2⟩

theorem reduction_to_macros {log : List (Exposure F rate)} (good : Good log) (width : Width rate)
    {depth : ℕ} {frontier : BatchOpening.Frontier (Digest F rate)}
    {proof : List (Digest F rate)} {root : Digest F rate}
    (reduction : BatchOpening.Reduction compression (primitiveLog log) depth frontier proof root) :
    Active log frontier →
      BatchOpening.Reduction hashing (macroLog log width) depth frontier proof root := by
  induction reduction with
  | root => exact fun _ ↦ .root _
  | step layer rest ih =>
      intro active
      have converted := layer_to_macros good width layer active
      exact .step converted.1 (ih converted.2)

omit [Zero F] in
theorem primitiveLog_normalized (raw : List (Exposure F rate)) :
    ∀ entry ∈ primitiveLog raw, entry ∈ primitiveLog (normalize raw) := by
  intro entry member
  obtain ⟨e, em, equal⟩ := List.mem_map.mp member
  obtain ⟨born, bm, same⟩ := pair_covered em
  apply List.mem_map.mpr
  exact ⟨born, bm, by simpa [same.1, same.2] using equal⟩

/-- Exact row order and duplicates, expressed using raw sponge calls rather than macro claims. -/
def PrimitiveRows (log : List (Exposure F rate)) (width : Width rate)
    (frontier : BatchOpening.Frontier (Digest F rate)) (positions : List ℕ)
    (rows : List (List F)) : Prop :=
  List.Forall₂ (fun i row ↦ ∃ e, (i, e.output.1) ∈ frontier ∧
    SpongeTrace log width.full width.tail e row) positions rows

/-- A primitive shared-frontier reduction and actual row traces determine the ordered batch. -/
theorem raw_batch_agrees {request : Request rate} {raw : List (Exposure F rate)}
    (good : Good (normalize raw)) {frontier : BatchOpening.Frontier (Digest F rate)}
    {proof : List (Digest F rate)} {root : Digest F rate} {positions : List ℕ}
    {rows : List (List F)}
    (reduction : BatchOpening.Reduction compression (primitiveLog raw)
      request.depth frontier proof root)
    (coverage : ∀ entry ∈ frontier, ∃ e row, e.output.1 = entry.2 ∧
      SpongeTrace raw request.width.full request.width.tail e row)
    (recorded : PrimitiveRows raw request.width frontier positions rows)
    (range : ∀ i ∈ positions, i < request.height) :
    positions.map (directExtract request (normalize raw) root) = rows.map some := by
  have active : Active (normalize raw) frontier := by
    intro entry member
    obtain ⟨e, row, output, trace⟩ := coverage entry member
    obtain ⟨born, bm, same, trace⟩ := trace.transport (fun _ em ↦ pair_covered em)
    exact ⟨born, bm, trace.forward good, (congrArg Prod.fst same.2).trans output⟩
  have derived := reduction_to_macros good request.width
    (reduction.mono (primitiveLog_normalized raw)) active
  have rowsRecorded : BatchOpening.RowsRecorded hashing (macroLog (normalize raw) request.width)
      frontier positions rows := by
    clear range
    induction recorded with
    | nil => exact .nil
    | cons head rest ih =>
        obtain ⟨e, member, trace⟩ := head
        obtain ⟨born, _, same, trace⟩ := trace.transport (fun _ em ↦ pair_covered em)
        have label : born.output.1 = e.output.1 := congrArg Prod.fst same.2
        exact .cons ⟨born.output.1, by simpa [label] using member, leaf_mem good trace⟩ ih
  rw [directExtract_eq good]
  exact batch_agrees good derived rowsRecorded range

/-- Ordered, duplicate-preserving batch agreement with the frozen direct extraction table. -/
theorem checkpoint_batch_agrees {Key : Type} [DecidableEq Key] {request : Request rate}
    {key : Key} {history : History Key F rate} {root : Digest F rate}
    (good : GoodHistory history) {roots : List (Digest F rate)} {later : History Key F rate}
    (marker : history = beforeFirst (some key) history ++ allocation key roots :: later)
    (registered : root ∈ roots) {frontier : BatchOpening.Frontier (Digest F rate)}
    {proof : List (Digest F rate)} {positions : List ℕ} {rows : List (List F)}
    (reduction : BatchOpening.Reduction compression (primitiveLog (calls history))
      request.depth frontier proof root)
    (coverage : ∀ entry ∈ frontier, ∃ e row, e.output.1 = entry.2 ∧
      SpongeTrace (calls history) request.width.full request.width.tail e row)
    (recorded : PrimitiveRows (calls history) request.width frontier positions rows)
    (range : ∀ i ∈ positions, i < request.height) :
    positions.map (directCheckpoint request key history root) = rows.map some := by
  rw [direct_checkpoint_agrees good marker registered]
  exact raw_batch_agrees good.1 reduction coverage recorded range

end ZkcSecurity.Commitment.PoseidonRows
