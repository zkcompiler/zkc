module

public import Zkc.Realization.ClearStorage
public import Zkc.Construction.ConnectionPrimitives

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
