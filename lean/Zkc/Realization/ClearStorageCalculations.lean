module

public import Zkc.Realization.ClearStorage
public import Zkc.Construction.ConnectionPrimitives
public import Zkc.Realization.RecordProjection

@[expose] public section

/-! Record projections use the same typed calculations as the constructed
participant. The metadata and payload positions follow from the declared layout,
without a protocol-specific field reader. -/

set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- Skip precisely the stored enclosing iteration coordinates. -/
def afterCoordinates {tail : ProductFields} {type : Ty} : (depth : Nat) →
    Var tail.toList type → Var (indexFields depth tail).toList type
  | 0, field => field
  | depth + 1, field => .there (afterCoordinates depth field)

theorem packed_projection {carriers : Carriers} {tail : ProductFields} {type : Ty}
    (depth : Nat) {indices : List Nat} {value : carriers.ProductValue tail}
    {record : carriers.ProductValue (indexFields depth tail)}
    (packed : packCoordinates depth indices value = some record) (field : Var tail.toList type) :
    ((indexFields depth tail).unpack record).get (afterCoordinates depth field) =
      (tail.unpack value).get field := by
  induction depth generalizing indices with
  | zero =>
    cases indices with
    | nil => cases Option.some.inj packed; rfl
    | cons => simp [packCoordinates] at packed
  | succ depth ih =>
    cases indices with
    | nil => simp [packCoordinates] at packed
    | cons index rest =>
      rcases record with ⟨head, record⟩
      obtain ⟨actual, found, equal⟩ := Option.map_eq_some_iff.mp packed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ih found

variable {kind : OracleKind} {model : DomainModel}

def Layout.projection (layout : Layout kind) : RecordProjection.Layout :=
  ⟨layout.recordIdentity, "Record", layout.fields⟩

def Layout.rowField (layout : Layout kind) : RecordProjection.Selection layout.fields :=
  ⟨.index, afterCoordinates layout.depth .here⟩

def Layout.dataField (layout : Layout kind) : RecordProjection.Selection layout.fields :=
  ⟨kind.data, afterCoordinates layout.depth (.there (.there .here))⟩

set_option backward.isDefEq.respectTransparency false in
/-- Field selection in the generated projection gives the published row
count at its actual SSA result position. The author supplies no routing law. -/
theorem Encodes.projected_rows {layout : Layout kind}
    {word : PublishedWords.Word model kind.answer} {record : model.Value layout.recordType}
    (encoding : Encodes layout word record)
    (selections : List (RecordProjection.Selection layout.fields))
    (localFields : ∀ selection ∈ selections, Domain.localType selection.type = true)
    (ordinal : Nat) (selected : selections[ordinal]? = some layout.rowField)
    (environment : Domain.Environment model.toCarriers) :
    (environment ++ RecordProjection.results model layout.projection record selections)[
      environment.length + ordinal]? = some (.data (.index word.rows)) := by
  have read := RecordProjection.results_get model layout.projection record selections
    localFields ordinal layout.rowField selected rfl
  change (RecordProjection.results model layout.projection record selections)[ordinal]? =
    some (.data ⟨.index, rfl,
      (layout.fields.unpack record).get (afterCoordinates layout.depth .here)⟩) at read
  have projection : (layout.fields.unpack record).get (afterCoordinates layout.depth .here) =
      word.rows := packed_projection layout.depth encoding.encoded .here
  rw [projection] at read
  rw [List.getElem?_append_right (by omega)]
  simpa [Domain.Payload.index] using read

set_option backward.isDefEq.respectTransparency false in
/-- The projected data is the word fixed by publication. An unrelated
same-typed field cannot establish this statement through type agreement. -/
theorem Encodes.projected_data {domain : String} {shape : Option Nat}
    {layout : Layout (.table (.field domain) shape)}
    {word : PublishedWords.Word model (.field domain)} {record : model.Value layout.recordType}
    (encoding : Encodes layout word record)
    (selections : List (RecordProjection.Selection layout.fields))
    (localFields : ∀ selection ∈ selections, Domain.localType selection.type = true)
    (ordinal : Nat) (selected : selections[ordinal]? = some layout.dataField)
    (environment : Domain.Environment model.toCarriers) :
    (environment ++ RecordProjection.results model layout.projection record selections)[
      environment.length + ordinal]? = some (.data ⟨.vector domain, rfl, word.cells⟩) := by
  have read := RecordProjection.results_get model layout.projection record selections
    localFields ordinal layout.dataField selected rfl
  change (RecordProjection.results model layout.projection record selections)[ordinal]? =
    some (.data ⟨.vector domain, rfl,
      (layout.fields.unpack record).get
        (afterCoordinates layout.depth (.there (.there .here)))⟩) at read
  have projection : (layout.fields.unpack record).get
      (afterCoordinates layout.depth (.there (.there .here))) = word.cells :=
    packed_projection layout.depth encoding.encoded (.there (.there .here))
  rw [projection] at read
  rw [List.getElem?_append_right (by omega)]
  simpa using read

/-- The actual get-product calculation reads the published length. -/
theorem Encodes.rows {layout : Layout kind} {word : PublishedWords.Word model kind.answer}
    {record : model.Value layout.recordType} (encoding : Encodes layout word record) :
    ConnectionCalculations.closedCalculation model
      (.getProduct layout.recordIdentity "Record" layout.fields .index
        (afterCoordinates layout.depth .here)) (.cons record .nil) =
      .done (.cons word.rows .nil) := by
  exact congrArg (fun value : Nat ↦
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [.index])))
    (packed_projection layout.depth encoding.encoded .here)

/-- A clear base constructor contributes exactly one leaf to native accounting. -/
theorem Encodes.leaves {layout : Layout kind} {word : PublishedWords.Word model kind.answer}
    {record : model.Value layout.recordType} (encoding : Encodes layout word record) :
    ConnectionCalculations.closedCalculation model
      (.getProduct layout.recordIdentity "Record" layout.fields .index
        (afterCoordinates layout.depth (.there .here))) (.cons record .nil) =
      .done (.cons 1 .nil) := by
  exact congrArg (fun value : Nat ↦
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [.index])))
    (packed_projection layout.depth encoding.encoded (.there .here))

/-- The payload is the exact published word, not merely a word with the same
length or an agreement premise supplied at a later query. -/
theorem Encodes.data {layout : Layout kind} {word : PublishedWords.Word model kind.answer}
    {record : model.Value layout.recordType} (encoding : Encodes layout word record) :
    ConnectionCalculations.closedCalculation model
      (.getProduct layout.recordIdentity "Record" layout.fields kind.data
        (afterCoordinates layout.depth (.there (.there .here)))) (.cons record .nil) =
      .done (.cons (oracleRowsData model.toCarriers kind word.cells) .nil) := by
  exact congrArg (fun value : model.Value kind.data ↦
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [kind.data])))
    (packed_projection layout.depth encoding.encoded (.there (.there .here)))

/-- The checked constructed instruction reads this same immutable record.
Its physical environment and operand positions are supplied by the common view,
while the provider representation determines which publication it denotes. -/
theorem Stored.read_view {layout : Layout kind} {words : PublishedWords.Table model}
    {records : List (model.Value layout.recordType)} {reference : Nat × Nat}
    {word : PublishedWords.Word model kind.answer}
    (stored : Stored layout words records reference word)
    (inputData : (Primitive.sequenceAt layout.recordType).arguments.all Domain.localType = true)
    (outputData : (Primitive.sequenceAt layout.recordType).results.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references =
      Domain.encodeValues (tys := [.sequence layout.recordType, .index])
        (.cons records (.cons reference.2 .nil))) :
    ∃ record, Encodes layout word record ∧
      Domain.View.execute model (.sequenceAt layout.recordType) references
        [.data layout.recordType] environment =
      .done (environment ++ Original.encodeHelperResult (tys := [layout.recordType]) (.cons record .nil)) := by
  obtain ⟨record, encoding, outcome⟩ := stored.read_record
  refine ⟨record, encoding, ?_⟩
  have connection := ConnectionPrimitives.view_execute model (.sequenceAt layout.recordType)
    (.cons records (.cons reference.2 .nil)) inputData outputData environment references read
  simpa only [outcome, primitiveOutcome, PIR.Process.bind, Primitive.results,
    List.map_cons, List.map_nil] using connection

end Zkc.Realization.ClearStorage
