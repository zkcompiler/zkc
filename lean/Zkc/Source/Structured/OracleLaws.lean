module

public import Zkc.Source.Structured.OracleExecution

@[expose] public section

/-! Local laws for the existing derivation and effect interpretation machinery. Source protocol
normalization uses these same typed requests; OracleNormalForm supplies the open action laws. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace OracleStore

theorem sameMembers_eq_true (left right : List Nat) :
    sameMembers left right = true ↔ ∀ role, role ∈ left ↔ role ∈ right := by
  simp only [sameMembers, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨forward, backward⟩ role
    exact ⟨forward role, backward role⟩
  · intro same
    exact ⟨fun role member ↦ (same role).mp member, fun role member ↦ (same role).mpr member⟩

theorem sameReference_eq_true {kind : OracleKind} (left right : OracleReference kind) :
    sameReference left right = true ↔ left = right := by
  cases kind with
  | table row fixed =>
    rcases left with ⟨leftAnchor, leftShape⟩
    rcases right with ⟨rightAnchor, rightShape⟩
    cases leftShape with | cons leftRows leftRest =>
      cases leftRest
      cases rightShape with | cons rightRows rightRest =>
        cases rightRest
        change (leftAnchor == rightAnchor && leftRows == rightRows) = true ↔ _
        simp only [Bool.and_eq_true, beq_iff_eq]
        constructor
        · rintro ⟨rfl, rfl⟩
          rfl
        · intro same
          exact ⟨congrArg OracleReference.anchor same,
            congrArg (fun reference ↦ referenceRows reference) same⟩

theorem sameReferenceList_eq_true {kind : OracleKind}
    (left right : List (OracleReference kind)) :
    sameReferenceList left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [sameReferenceList]
  | cons head tail ih =>
    cases right <;> simp [sameReferenceList, sameReference_eq_true, ih]

/-- Executable pair comparison retains every anchor, shape, duplicate and position, including
the complete indexed capacity for an empty sequence. Receiver order is membership-only. -/
theorem samePair_eq_true {sort : OracleLogicalSort} (left right : OracleDataView sort) :
    samePair left right = true ↔ left.SamePair right := by
  cases sort <;>
    simp [samePair, OracleDataView.SamePair, sameMembers_eq_true, sameReference_eq_true,
      sameReferenceList_eq_true, and_assoc]

theorem find_fresh {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (entries : OracleEntries model snapshot domains math)
    {row : Ty} (table : OracleStoredTable model snapshot domains math row) :
    find (⟨row, table⟩ :: entries) row table.anchor = some table := by
  simp [find]

/-- An invalid outer position suppresses the retained body and every provider interaction,
independently of payload, capture validity or the provider's stopping behavior. -/
theorem answer_outside {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {S E : Type}
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (self : Nat)
    {row : Ty} (table : OracleStoredTable model snapshot domains math row)
    (older : OracleEntries model snapshot domains math) (fixed : Option Nat)
    (position : Nat) (location : OracleLocation) (state : S × Nat)
    (outside : table.rows ≤ position) :
    answer model base self (⟨row, table⟩ :: older)
      ⟨.table row fixed, table.anchor, position, location, []⟩ state =
      ⟨.stopped .refused, (state.1, state.2 + 1),
        [.query ⟨.table row fixed, table.anchor, position, location, []⟩]⟩ := by
  simp [answer, OracleKind.answer, outside]

/-- Every base-provider outcome, including every stop, retains its post-state and ordered
events. The logical query is counted before provider interaction. -/
theorem answer_base {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {S E : Type}
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (self : Nat)
    (row : Ty) (fixed : Option Nat) (anchor : OracleAnchor) (rows holder : Nat)
    (receivers : List Nat) (data : Option (List (model.Value row)))
    (older : OracleEntries model snapshot domains math)
    (position : Nat) (location : OracleLocation) (state : S × Nat)
    (allowed : visible self holder receivers = true)
    (shaped : validRows (.table row fixed) rows = true) (inside : position < rows) :
    answer model base self
      (⟨row, ⟨anchor, rows, holder, receivers, .base data⟩⟩ :: older)
      ⟨.table row fixed, anchor, position, location, []⟩ state =
      let result := base ⟨.table row fixed, anchor, position, location, []⟩ state.1
      ⟨result.outcome, (result.state, state.2 + 1),
        .query ⟨.table row fixed, anchor, position, location, []⟩ ::
          result.events.map OracleEvent.provider⟩ := by
  simp [answer, OracleKind.answer, allowed, shaped, Nat.not_le_of_lt inside]

end OracleStore

/-- The query rule is local to the actual retained operation and quantifies over the fixed
effect interpretation. It is usable directly by `Region.Derivation.letOp`; it chooses no
whole-body meaning and preserves every reply and stop of the interpretation. -/
theorem oracleBody_queryLaw (model : DomainModel) {I : PIR.Signature}
    (tables : Evaluation.ComponentTablesOn model.toCarriers (oracleReadInterface model.toCarriers))
    (operations : PIR.OperationInterpretation (oracleReadInterface model.toCarriers) I)
    (kind : OracleKind) (location : OracleLocation) (anchor : OracleAnchor) (position : Nat) :
    (oracleBodyMeaning model tables).OperationLaw operations
      (.oracle (.query kind none) location) (.cons (some anchor) (.cons (some position) .nil)) .nil
      ((operations ⟨kind, anchor, position, location, []⟩).bind
        (fun answer ↦ .done (.cons (some answer) .nil))) := by
  intro bodies _
  cases bodies
  rfl

end Zkc.Source.Structured
