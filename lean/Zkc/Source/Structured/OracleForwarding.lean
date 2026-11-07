module

public import Zkc.Source.Structured.OracleLaws

@[expose] public section

/-! A receiver can forward logical handles without reading their contents. The
actual store and bounds decide admission. Successful forwarding preserves the
exact ordered sequence, including duplicate handles. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

namespace OracleStore

theorem find_anchor {entries : OracleEntries model snapshot domains math} {row : Ty}
    {anchor : OracleAnchor} {table : OracleStoredTable model snapshot domains math row}
    (found : find entries row anchor = some table) : table.anchor = anchor := by
  induction entries with
  | nil => cases found
  | cons entry rest ih =>
    rcases entry with ⟨storedRow, head⟩
    by_cases typed : storedRow = row
    · subst storedRow
      by_cases matched : head.anchor = anchor
      · simp [find, matched] at found
        cases found
        exact matched
      · exact ih (by simpa [find, matched] using found)
    · exact ih (by simpa [find, typed] using found)

end OracleStore

namespace OracleExecution
variable (state : OracleRuntimeState model snapshot domains math S)

private theorem singletonView_anchor (kind : OracleKind) (holder : Nat) (receivers : List Nat)
    (bounds : List (String × Nat)) (anchor : OracleAnchor) (view : OracleDataView (.singleton kind))
    (checked : singletonView state kind holder receivers bounds anchor = some view) :
    view.references.anchor = anchor := by
  cases found : OracleStore.find state.entries kind.answer anchor with
  | none => simp [singletonView, found] at checked
  | some table =>
    simp only [singletonView, found, bind, Option.bind] at checked
    split at checked
    · contradiction
    · cases checked
      exact OracleStore.find_anchor found

private theorem sequenceReferences_anchors (kind : OracleKind) (holder : Nat) (receivers : List Nat)
    (bounds : List (String × Nat)) (anchors : List OracleAnchor) (refs : List (OracleReference kind))
    (checked : sequenceReferences state kind holder receivers bounds anchors = some refs) :
    refs.map (·.anchor) = anchors := by
  induction anchors generalizing refs with
  | nil => cases checked; rfl
  | cons a tail ih =>
    cases head : singletonView state kind holder receivers bounds a with
    | none => simp [sequenceReferences, head] at checked
    | some v =>
      cases rest : sequenceReferences state kind holder receivers bounds tail with
      | none => simp [sequenceReferences, head, rest] at checked
      | some vs =>
        simp [sequenceReferences, head, rest] at checked
        cases checked
        simp [singletonView_anchor state kind holder receivers bounds a v head, ih vs rest]

theorem pairedView_anchors (sort : OracleLogicalSort) (holder : Nat) (receivers : List Nat)
    (bounds : List (String × Nat)) (anchors : model.Value sort.type) (view : OracleDataView sort)
    (checked : pairedView state sort holder receivers bounds anchors = some view) :
    view.anchors model.toCarriers = anchors := by
  cases sort with
  | singleton kind => exact singletonView_anchor state kind holder receivers bounds anchors view checked
  | sequence kind maximum =>
    simp only [pairedView] at checked
    split at checked
    · contradiction
    · cases rest : sequenceReferences state kind holder receivers bounds anchors with
      | none => simp [rest] at checked
      | some refs =>
        simp [rest] at checked
        cases checked
        exact sequenceReferences_anchors state kind holder receivers bounds anchors refs rest

variable (oracles : List (CheckedOracle snapshot domains math))
  (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
  (location : OracleLocation) (roles : Nat → Nat) (sort : OracleLogicalSort)
  (holder : Nat) (receivers : List Nat) (anchors : model.Value sort.type)
  (other : state.self ≠ roles holder) (receives : state.self ∈ receivers.map roles)

include receives in
private theorem receiver_visible : OracleStore.visible state.self (roles holder) (receivers.map roles) = true := by
  simp only [OracleStore.visible, List.contains_iff_mem.mpr receives, Bool.or_true]

include other receives in
/-- A receiver's input either preserves its concrete handles exactly or
refuses at the original location. Neither result can consult the base provider. -/
theorem receiver_input (bounds : List (String × Nat)) :
    operation model oracles base location state.self roles (.input sort holder receivers bounds)
        (.cons none (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil)) state =
      if (pairedView state sort (roles holder) (receivers.map roles) bounds anchors).isSome then
        returned state (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil)
      else refusal state location "oracle-input-pair" := by
  have visible := receiver_visible state roles holder receivers receives
  cases h : pairedView state sort (roles holder) (receivers.map roles) bounds anchors with
  | none => simp [operation, visible, other, h]
  | some view => simp [operation, visible, other, h, pairedView_anchors state _ _ _ _ _ _ h]

include other receives in
/-- Projection uses the sort's own bounds and returns no holder data to a receiver. -/
theorem receiver_components :
    operation model oracles base location state.self roles (.components sort holder receivers)
        (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil) state =
      if (pairedView state sort (roles holder) (receivers.map roles) (sortBounds sort) anchors).isSome then
        returned state (.cons none (.cons (some (ProtocolValue.ofConcrete sort.type anchors)) .nil))
      else refusal state location "oracle-components-pair" := by
  have visible := receiver_visible state roles holder receivers receives
  cases h : pairedView state sort (roles holder) (receivers.map roles) (sortBounds sort) anchors with
  | none => simp [operation, visible, h]
  | some view => simp [operation, visible, other, h, List.mem_map.mp receives]

end OracleExecution
end Zkc.Source.Structured
