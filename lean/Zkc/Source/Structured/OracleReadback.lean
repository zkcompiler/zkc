module

public import Zkc.Source.Structured.OracleLaws

@[expose] public section

/-! Resolve reads in the immutable registry. A virtual read expands against
the prefix captured at its installation. Each child keeps its own coordinate
and the path of its enclosing reads. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleStore

theorem answerOfBase {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {S E : Type} (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (self : Nat) (entries : OracleEntries model snapshot domains math) (request : OracleRead)
    (state : S × Nat) (stored : OracleStoredTable model snapshot domains math request.kind.answer)
    (data : Option (List (model.Value request.kind.answer)))
    (found : find entries request.kind.answer request.anchor = some stored) (payload : stored.payload = .base data)
    (allowed : visible self stored.holder stored.receivers = true)
    (shape : validRows request.kind stored.rows = true) (inside : request.position < stored.rows) :
    answer model base self entries request state =
      let reply := base request state.1
      ⟨reply.outcome, (reply.state, state.2 + 1),
        .query request :: reply.events.map OracleEvent.provider⟩ := by
  induction entries with
  | nil => simp [find] at found
  | cons entry rest ih =>
    rcases entry with ⟨row, head⟩
    by_cases same : row = request.kind.answer
    · subst row
      by_cases anchor : head.anchor = request.anchor
      · have eq : head = stored := by simpa [find, anchor] using found
        subst head
        simp [answer, anchor, allowed, shape, Nat.not_le_of_lt inside, payload]
      · simpa [answer, anchor] using ih (by simpa [find, anchor] using found)
    · simpa [answer, same] using ih (by simpa [find, same] using found)

/-- Fresh entries at other anchors preserve the exact logical table, including
its holder, visibility and virtual captures. A suffix alone permits shadowing. -/
theorem findSkipNewer {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (newer older : OracleEntries model snapshot domains math)
    (row : Ty) (anchor : OracleAnchor) (fresh : hasAnchor newer anchor = false) :
    find (newer ++ older) row anchor = find older row anchor := by
  induction newer with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨storedRow, head⟩
    have absent : head.anchor ≠ anchor ∧ hasAnchor rest anchor = false := by
      simpa [hasAnchor] using fresh
    simp [find, absent.1, ih absent.2]

theorem answerSkipNewer {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {S E : Type} (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (self : Nat) (newer older : OracleEntries model snapshot domains math) (request : OracleRead)
    (state : S × Nat) (fresh : hasAnchor newer request.anchor = false) :
    answer model base self (newer ++ older) request state = answer model base self older request state := by
  induction newer with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨row, head⟩
    have absent : head.anchor ≠ request.anchor ∧ hasAnchor rest request.anchor = false := by
      simpa [hasAnchor] using fresh
    simp [answer, absent.1, ih absent.2]

theorem answerOfVirtual {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {S E : Type} (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (self : Nat) (older : OracleEntries model snapshot domains math) (parent : OracleRead)
    (rows holder : Nat) (receivers : List Nat) (checked : CheckedOracle snapshot domains math)
    (row : checked.declaration.kind.answer = parent.kind.answer)
    (captures : Values model.Value checked.declaration.inputs.dropLast)
    (signature : checked.declaration.inputs = checked.declaration.inputs.dropLast ++ [.index])
    (allowed : visible self holder receivers = true) (shape : validRows parent.kind rows = true)
    (inside : parent.position < rows) (state : S × Nat)
    (value : model.Value checked.declaration.kind.answer) (final : S × Nat) (trace : List (OracleEvent E))
    (run : let args : Values model.Value checked.declaration.inputs :=
              signature.symm ▸ captures.append (.cons parent.position .nil)
           (checked.denote model args.present).run
              (fun child current ↦ answer model base self older (parent.expand child) current)
              (state.1, state.2 + 1) = ⟨.returned (.cons (some value) .nil), final, trace⟩) :
    answer model base self
      (⟨parent.kind.answer, ⟨parent.anchor, rows, holder, receivers, .virtual checked row captures⟩⟩ :: older)
      parent state = ⟨.returned (row ▸ value), final, .query parent :: trace⟩ := by
  rw [answer]
  simp only [allowed, shape, Bool.not_true, Bool.false_or,
    Nat.not_le_of_lt inside, decide_false, Bool.false_eq_true, ite_false, dite_eq_left signature, run]
  rfl

end Zkc.Source.Structured.OracleStore
