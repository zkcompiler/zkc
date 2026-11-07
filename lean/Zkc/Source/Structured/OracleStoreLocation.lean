module

public import Zkc.Source.Structured.RegisteredLifetime
public import Zkc.Source.Structured.OracleForwarding

@[expose] public section

/-! Locate an installed table together with its immutable older registry.
Virtual expansion uses this older suffix, not the caller's current registry.
The source reachability invariant derives the placement from an actual lookup;
fresh extensions preserve it without any protocol-specific store induction. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleStore
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {row : Ty}

/-- The first matching installation and the registry visible to its children. -/
def Located (entries : OracleEntries model snapshot domains math)
    (table : OracleStoredTable model snapshot domains math row)
    (older : OracleEntries model snapshot domains math) : Prop :=
  ∃ newer, entries = newer ++ ⟨row, table⟩ :: older ∧ hasAnchor newer table.anchor = false

theorem Located.head (older : OracleEntries model snapshot domains math)
    (table : OracleStoredTable model snapshot domains math row) :
    Located (⟨row, table⟩ :: older) table older := ⟨[], rfl, rfl⟩

theorem Located.find {entries older : OracleEntries model snapshot domains math}
    {table : OracleStoredTable model snapshot domains math row}
    (located : Located entries table older) : find entries row table.anchor = some table := by
  obtain ⟨newer, rfl, fresh⟩ := located
  rw [findSkipNewer newer _ _ _ fresh]
  simp [OracleStore.find]

theorem Located.extend {entries older : OracleEntries model snapshot domains math}
    {table : OracleStoredTable model snapshot domains math row}
    (located : Located entries table older) (extra : OracleEntries model snapshot domains math)
    (fresh : hasAnchor extra table.anchor = false) : Located (extra ++ entries) table older := by
  obtain ⟨newer, rfl, earlierFresh⟩ := located
  exact ⟨extra ++ newer, (List.append_assoc ..).symm,
    by simpa [hasAnchor, List.any_append] using And.intro fresh earlierFresh⟩

/-- Later constructions preserve the exact older registry, body and captures. -/
theorem Located.transport {before after older : OracleEntries model snapshot domains math}
    {table : OracleStoredTable model snapshot domains math row}
    (located : Located before table older) (extension : FreshExtension before after) :
    Located after table older := by
  obtain ⟨extra, rfl, fresh⟩ := extension
  exact located.extend extra (fresh table.anchor (hasAnchor_of_find located.find))

/-- No author-chosen history is needed: successful lookup in the actual
reachable registry supplies the checked older prefix and capture validity. -/
theorem Reachable.find_location {self : Nat}
    {entries : OracleEntries model snapshot domains math}
    (reachable : Reachable self entries) {anchor : OracleAnchor}
    {table : OracleStoredTable model snapshot domains math row}
    (found : find entries row anchor = some table) :
    ∃ older, Located entries table older ∧ Reachable self older ∧
      PayloadBefore self older table ∧ older.length < entries.length := by
  induction reachable with
  | empty => cases found
  | @inserted older storedRow head earlier fresh captures ih =>
    by_cases typed : storedRow = row
    · subst storedRow
      by_cases same : head.anchor = anchor
      · have matched : head = table := by simpa [find, same] using found
        subst head
        exact ⟨older, .head older table, earlier, captures, by simp⟩
      · have inOlder : find older row anchor = some table := by simpa [find, same] using found
        obtain ⟨earlierEntries, located, reachablePrefix, valid, shorter⟩ := ih inOlder
        refine ⟨earlierEntries, ?_, reachablePrefix, valid, by simp only [List.length_cons]; omega⟩
        exact located.extend [⟨row, head⟩] (by simp [hasAnchor, find_anchor inOlder, same])
    · have inOlder : find older row anchor = some table := by simpa [find, typed] using found
      have different : head.anchor ≠ anchor := by
        intro equal
        simp [equal, hasAnchor_of_find inOlder] at fresh
      obtain ⟨earlierEntries, located, reachablePrefix, valid, shorter⟩ := ih inOlder
      refine ⟨earlierEntries, ?_, reachablePrefix, valid, by simp only [List.length_cons]; omega⟩
      exact located.extend [⟨storedRow, head⟩]
        (by simp [hasAnchor, find_anchor inOlder, different])

/-- Lookup keeps the same read semantics, including refusal and every stop.
In particular, a virtual body still expands against its installation suffix. -/
theorem Located.answer {S E : Type}
    {entries older : OracleEntries model snapshot domains math}
    {table : OracleStoredTable model snapshot domains math row}
    (located : Located entries table older)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (self : Nat) (request : OracleRead) (anchor : request.anchor = table.anchor) (state : S × Nat) :
    OracleStore.answer model base self entries request state =
      OracleStore.answer model base self (⟨row, table⟩ :: older) request state := by
  obtain ⟨newer, rfl, fresh⟩ := located
  exact answerSkipNewer base self newer _ request state (by simpa only [anchor] using fresh)

set_option backward.isDefEq.respectTransparency false in
/-- Full execution of the checked virtual body, not merely its successful
returns. Child stops retain their state and events, and skip the remaining body.
The caller must establish the actual parent admission checks. -/
theorem Located.virtual_answer {S E : Type}
    {entries older : OracleEntries model snapshot domains math}
    (checked : CheckedOracle snapshot domains math) (parent : OracleRead)
    (row : checked.declaration.kind.answer = parent.kind.answer)
    (rows holder : Nat) (receivers : List Nat)
    (captures : Values model.Value checked.declaration.inputs.dropLast)
    (located : Located entries
      (⟨parent.anchor, rows, holder, receivers, .virtual checked row captures⟩ :
        OracleStoredTable model snapshot domains math parent.kind.answer) older)
    (signature : checked.declaration.inputs = checked.declaration.inputs.dropLast ++ [.index])
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (self : Nat)
    (allowed : visible self holder receivers = true) (shape : validRows parent.kind rows = true)
    (inside : parent.position < rows) (state : S × Nat) :
    OracleStore.answer model base self entries parent state =
      let args : Values model.Value checked.declaration.inputs :=
        signature.symm ▸ captures.append (.cons parent.position .nil)
      let body := (checked.denote model args.present).run
        (fun child current ↦ OracleStore.answer model base self older (parent.expand child) current)
        (state.1, state.2 + 1)
      let outcome := match body.outcome with
        | .stopped reason => .stopped reason
        | .returned values => match values.get .here with
          | none => .stopped .incomplete
          | some value => .returned (row ▸ value)
      ⟨outcome, body.state, .query parent :: body.events⟩ := by
  rw [located.answer base self parent rfl state, OracleStore.answer]
  simp only [allowed, shape, Bool.not_true, Bool.false_or, Nat.not_le_of_lt inside,
    decide_false, Bool.false_eq_true, ↓reduceIte, dite_eq_left signature, dite_true]
  congr 1
  split <;> simp_all
  split <;> simp_all

end Zkc.Source.Structured.OracleStore
