module

public import Zkc.Source.Structured.OracleProcessStore
public import Zkc.Source.Structured.OracleProcessLaws
public import Zkc.Source.Structured.OracleStoreLocation

@[expose] public section

/-! Open-process laws at the actual immutable installation. These equations
retain arbitrary provider continuations, including their stopped state and log.
They expose the existing source expansion for controller simulation without
choosing a handler or introducing a second virtual-oracle evaluator.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

/-- Fresh later constructions preserve the same open provider computation.
This is stronger than equality after choosing a deterministic handler. -/
theorem answer_skip_newer (self : Nat)
    (newer older : OracleEntries model snapshot domains math)
    (request : OracleRead) (state : S × Nat)
    (fresh : OracleStore.hasAnchor newer request.anchor = false) :
    answer (E := E) model self (newer ++ older) request state =
      answer model self older request state := by
  induction newer with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨row, head⟩
    have absent : head.anchor ≠ request.anchor ∧
        OracleStore.hasAnchor rest request.anchor = false := by
      simpa [OracleStore.hasAnchor] using fresh
    simp [answer, absent.1, ih absent.2]

theorem answer_located {row : Ty}
    {entries older : OracleEntries model snapshot domains math}
    {table : OracleStoredTable model snapshot domains math row}
    (located : OracleStore.Located entries table older)
    (self : Nat) (request : OracleRead) (anchor : request.anchor = table.anchor)
    (state : S × Nat) :
    answer (E := E) model self entries request state =
      answer model self (⟨row, table⟩ :: older) request state := by
  obtain ⟨newer, rfl, fresh⟩ := located
  exact answer_skip_newer self newer _ request state (by simpa only [anchor] using fresh)

/-- Admission is checked before any provider call or virtual body. Refusal
still charges and records the reached logical query. -/
theorem answer_refused {entries older : OracleEntries model snapshot domains math}
    (request : OracleRead)
    (table : OracleStoredTable model snapshot domains math request.kind.answer)
    (located : OracleStore.Located entries table older)
    (anchor : request.anchor = table.anchor) (self : Nat) (state : S × Nat)
    (refused : (!OracleStore.visible self table.holder table.receivers ||
      !OracleStore.validRows request.kind table.rows || decide (request.position ≥ table.rows)) =
        true) :
    answer (E := E) model self entries request state =
      .done ⟨.stopped .refused, (state.1, state.2 + 1), [.query request]⟩ := by
  rw [answer_located located self request anchor state, answer]
  simp only [anchor, ↓reduceDIte, ↓reduceIte, refused]

/-- The leaf preserves the exact request, provider state, arbitrary outcome
and ordered provider events. It adds precisely one logical query. -/
theorem answer_base {entries older : OracleEntries model snapshot domains math}
    (request : OracleRead) (rows holder : Nat) (receivers : List Nat)
    (data : Option (List (model.Value request.kind.answer)))
    (located : OracleStore.Located entries
      (⟨request.anchor, rows, holder, receivers, .base data⟩ :
        OracleStoredTable model snapshot domains math request.kind.answer) older)
    (self : Nat) (allowed : OracleStore.visible self holder receivers = true)
    (shape : OracleStore.validRows request.kind rows = true)
    (inside : request.position < rows) (state : S × Nat) :
    answer (E := E) model self entries request state =
      mapResult (fun reply ↦ ⟨reply.outcome, (reply.state, state.2 + 1),
        .query request :: reply.events.map OracleEvent.provider⟩) (baseCall request state.1) := by
  rw [answer_located located self request rfl state, answer]
  simp only [allowed, shape, Bool.not_true, Bool.false_or, Nat.not_le_of_lt inside,
    decide_false, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
/-- A virtual entry retains its checked body, original captures and exact
older registry. Child requests extend the parent's source-relative path.
The equation includes refusals and incomplete results, not just successful
mathematical answers. -/
theorem answer_virtual {entries older : OracleEntries model snapshot domains math}
    (checked : CheckedOracle snapshot domains math) (parent : OracleRead)
    (row : checked.declaration.kind.answer = parent.kind.answer)
    (rows holder : Nat) (receivers : List Nat)
    (captures : Values model.Value checked.declaration.inputs.dropLast)
    (located : OracleStore.Located entries
      (⟨parent.anchor, rows, holder, receivers, .virtual checked row captures⟩ :
        OracleStoredTable model snapshot domains math parent.kind.answer) older)
    (signature : checked.declaration.inputs = checked.declaration.inputs.dropLast ++ [.index])
    (self : Nat) (allowed : OracleStore.visible self holder receivers = true)
    (shape : OracleStore.validRows parent.kind rows = true)
    (inside : parent.position < rows) (state : S × Nat) :
    answer (E := E) model self entries parent state =
      let args : Values model.Value checked.declaration.inputs :=
        signature.symm ▸ captures.append (.cons parent.position .nil)
      mapResult (fun result ↦
        let outcome := match result.outcome with
          | .stopped reason => .stopped reason
          | .returned values => match values.get .here with
            | none => .stopped .incomplete
            | some value => .returned (row ▸ value)
        ⟨outcome, result.state, .query parent :: result.events⟩)
        (present (fun child current ↦ answer model self older (parent.expand child) current)
          (checked.denote model args.present) (state.1, state.2 + 1)) := by
  rw [answer_located located self parent rfl state, answer]
  simp only [allowed, shape, Bool.not_true, Bool.false_or, Nat.not_le_of_lt inside,
    decide_false, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, dite_eq_left signature]
  congr 1
  funext result
  split <;> simp_all
  split <;> simp_all

/-- Specializing the open leaf equation preserves the complete outer monad.
In particular, missing probability mass cannot turn into a refused record. -/
theorem executeM_base {m : Type → Type} [Monad m] [LawfulMonad m]
    (external : PIR.MonadHandler m (External model) S E)
    (request : OracleRead) (state : S × Nat) :
    executeM external
      (mapResult (fun reply ↦ ⟨reply.outcome, (reply.state, state.2 + 1),
        .query request :: reply.events.map OracleEvent.provider⟩) (baseCall request state.1))
      state = (do
        let reply ← external (.inr request) state.1
        pure ⟨reply.outcome, (reply.state, state.2 + 1),
          .query request :: reply.events.map OracleEvent.provider⟩) := by
  simp [executeM, mapResult, baseCall, PIR.Process.bind, runM_effect_call,
    PIR.Process.runM]

end Zkc.Source.Structured.OracleProcess
