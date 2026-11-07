module

public import Zkc.Realization.ClearStorageLookup
public import Zkc.Realization.TableRead

@[expose] public section

/-! A checked table read consumes the word fixed by successful publication.
Stored and requested shape annotations may differ, but both must admit that
same word length. The equivalence includes every query position and refusal.
-/

set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {model : DomainModel} {domain : String} {storedShape requestedShape : Option Nat}

set_option backward.isDefEq.respectTransparency false in
/-- On an admitted publication the generated guarded collection read and the
provider have identical outcomes, including out-of-range queries. Location and
expansion describe the query occurrence and do not rename the published word. -/
theorem published_read {Aux E : Type}
    (word : PublishedWords.Word model (.field domain))
    (state : PublishedWords.State model Aux)
    (found : PublishedWords.find state.words (.field domain) word.anchor = some word)
    (kind : word.kind = .table (.field domain) storedShape)
    (valid : OracleStore.validRows word.kind word.rows = true)
    (compatible : OracleStore.validRows (.table (.field domain) requestedShape) word.rows = true)
    (length : word.cells.length = word.rows)
    (position : Nat) (location : OracleLocation) (expansion : List (OracleAnchor × OracleLocation)) :
    let request : OracleRead :=
      ⟨.table (.field domain) requestedShape, word.anchor, position, location, expansion⟩
    (PublishedWords.read (E := E) request state).outcome =
      Domain.closedOutcome (TableRead.read model domain word.cells word.rows position) := by
  dsimp only
  have finite : word.rows < indexLimit := by
    simp only [OracleStore.validRows, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1
  rw [TableRead.read_eq]
  by_cases within : position < word.rows
  · have positionFinite := lt_trans within finite
    simp only [positionFinite, finite, within, and_self, ↓reduceIte]
    simp only [PublishedWords.read, OracleKind.answer, found, kind, compatible,
      show OracleStore.validRows (.table (.field domain) storedShape) word.rows = true by
        simpa only [kind] using valid,
      length, Nat.not_le_of_gt within, bne_self_eq_false, Bool.not_true,
      Bool.false_or, decide_false]
    split
    · rename_i impossible
      cases impossible
    · cases word.cells[position]? <;> rfl
  · have outside := Nat.le_of_not_gt within
    rw [PublishedWords.read_out_of_range
      (⟨.table (.field domain) requestedShape, word.anchor, position, location, expansion⟩ : OracleRead)
      state word found outside]
    simp [within, Domain.closedOutcome]

set_option backward.isDefEq.respectTransparency false in
/-- Once lookup and projection supply the reached values, the actual read
block implements the provider associated with this exact immutable handle.
No FRI equation or later word-equality premise enters this connection. -/
noncomputable def Stored.read_simulation {Aux E : Type}
    {layout : Layout (.table (.field domain) storedShape)}
    {state : PublishedWords.State model Aux} {records : List (model.Value layout.recordType)}
    {reference : Nat × Nat} {word : PublishedWords.Word model (.field domain)}
    (stored : Stored layout state.words records reference word)
    (valid : OracleStore.validRows word.kind word.rows = true)
    (compatible : OracleStore.validRows (.table (.field domain) requestedShape) word.rows = true)
    (length : word.cells.length = word.rows)
    (position : Nat) (location : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (program : Program) (context : Context)
    (environment : Domain.Environment model.toCarriers) (data rowsSlot positionSlot : Nat)
    (site : String)
    (readData : environment[data]? = some (.data ⟨.vector domain, rfl, word.cells⟩))
    (readRows : environment[rowsSlot]? = some (.data (.index word.rows)))
    (readPosition : environment[positionSlot]? = some (.data (.index position))) :
    let request : OracleRead :=
      ⟨.table (.field domain) requestedShape, word.anchor, position, location, expansion⟩
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (((primitiveOutcome (I := closedInterface)
        (PublishedWords.read (E := E) request state).outcome).interpret
          (closedLift (I := Domain.effects model.toCarriers))).bind
            (fun value ↦ .done (environment ++ [.data (.boolean true),
              .data ⟨.field domain, rfl, value⟩])))
      (Domain.evaluate model program context
        (TableRead.instructions domain ⟨environment.length, data, rowsSlot, positionSlot, site⟩)
        environment) := by
  dsimp only
  have associated : PublishedWords.find state.words (.field domain) word.anchor = some word ∧
      word.kind = .table (.field domain) storedShape := by
    obtain ⟨record, _, _, found, encoded⟩ := stored
    exact ⟨found, encoded.kind_eq⟩
  rw [published_read word state associated.1 associated.2 valid compatible length]
  have closed : primitiveOutcome (I := closedInterface)
      (Domain.closedOutcome (TableRead.read model domain word.cells word.rows position)) =
      TableRead.read model domain word.cells word.rows position := by
    cases TableRead.read model domain word.cells word.rows position with
    | done value => rfl
    | halt reason => rfl
    | call operation next => exact nomatch operation
  rw [closed, TableRead.correspondence]
  exact TableRead.simulation model domain environment data rowsSlot positionSlot site
    word.cells word.rows position readData readRows readPosition

end Zkc.Realization.ClearStorage
