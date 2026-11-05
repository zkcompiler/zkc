module

public import ZkcSecurity.Transformations.Commitment.PoseidonRows.Checkpoint

@[expose] public section

/-! # Raw call coverage and recorded-opening consequences

Calls in an actual computation may be cache hits whose direction differs from the first exposure.
Transport uses only full oriented pair equality. No primitive trace is inferred from a claimed
macro query; the producer must supply the calls and exact overwrite/climb equations.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

variable {F : Type} {rate : ℕ} [Zero F] [DecidableEq F]

omit [DecidableEq F] in
theorem SpongeTrace.transport {log larger : List (Exposure F rate)}
    (covered : ∀ e ∈ log, ∃ other ∈ larger, SamePair other e)
    {full tail : ℕ} {e : Exposure F rate} {row : List F}
    (trace : SpongeTrace log full tail e row) :
    ∃ other ∈ larger, SamePair other e ∧ SpongeTrace larger full tail other row := by
  induction trace with
  | single block member input =>
      obtain ⟨other, om, same⟩ := covered _ member
      exact ⟨other, om, same, .single block om (same.1.trans input)⟩
  | next block prior member input ih =>
      obtain ⟨previous, pm, previousSame, previousTrace⟩ := ih
      obtain ⟨other, om, same⟩ := covered _ member
      refine ⟨other, om, same, .next block previousTrace om ?_⟩
      rw [same.1, input, previousSame.2]

omit [DecidableEq F] [Zero F] in
theorem NodeClimb.transport {log larger : List (Exposure F rate)}
    (covered : ∀ e ∈ log, ∃ other ∈ larger, SamePair other e)
    {index : ℕ} {siblings : List (Digest F rate)} {e : Exposure F rate} {root : Digest F rate}
    (climb : NodeClimb log index siblings e root) :
    ∀ other, SamePair other e → NodeClimb larger index siblings other root := by
  induction climb with
  | nil =>
      intro other same
      simpa [same.2] using (NodeClimb.nil (log := larger) (e := other))
  | @step index siblings child parent sibling member input root rest ih =>
      intro other same
      obtain ⟨above, am, aboveSame⟩ := covered _ member
      apply NodeClimb.step sibling am _ (ih above aboveSame)
      rw [aboveSame.1, input, same.2]

/-- Raw recorded positive-width overwrite calls plus a raw recorded node climb suffice.
First-exposure normalization and forward-born relevance are proved, not supplied annotations. -/
theorem raw_opening_agrees {request : Request rate} {raw : List (Exposure F rate)}
    (good : Good (normalize raw)) {e : Exposure F rate} {row : List F} {index : ℕ}
    {siblings : List (Digest F rate)} {root : Digest F rate}
    (trace : SpongeTrace raw request.width.full request.width.tail e row)
    (climb : NodeClimb raw index siblings e root) (length : siblings.length = request.depth)
    (range : index < request.height) : extract request (normalize raw) root index = some row := by
  obtain ⟨born, _, same, normalizedTrace⟩ := trace.transport (fun _ member ↦ pair_covered member)
  exact opening_agrees good normalizedTrace
    (climb.transport (fun _ member ↦ pair_covered member) born same) length range

/-- Frozen-table agreement for any actual recorded opening after its registered allocation. -/
theorem checkpoint_opening_agrees {Key : Type} [DecidableEq Key] {request : Request rate}
    {key : Key} {history : History Key F rate} {root : Digest F rate}
    (good : GoodHistory history) {roots : List (Digest F rate)} {later : History Key F rate}
    (marker : history = beforeFirst (some key) history ++ allocation key roots :: later)
    (registered : root ∈ roots) {e : Exposure F rate} {row : List F} {index : ℕ}
    {siblings : List (Digest F rate)}
    (trace : SpongeTrace (calls history) request.width.full request.width.tail e row)
    (climb : NodeClimb (calls history) index siblings e root)
    (length : siblings.length = request.depth) (range : index < request.height) :
    checkpoint request key history root index = some row := by
  rw [checkpoint_agrees good marker registered]
  exact raw_opening_agrees good.1 trace climb length range

end ZkcSecurity.Commitment.PoseidonRows
