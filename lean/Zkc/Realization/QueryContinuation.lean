module

public import Zkc.Realization.RecordAppend
public import Zkc.Realization.ClearStorageCalculations

@[expose] public section

/-! Continuation frames retain the outer continuation, parent instance and
position, and ordered indices of earlier child answers. The parent constructor
and answer kinds are fixed by the selected static continuation. Frame contents
alone do not establish a source occurrence or justify choosing that continuation.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryContinuation
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Frame where
  outer : Nat
  outerInstance : Nat
  parentInstance : Nat
  position : Nat
  answers : List Nat
  deriving DecidableEq, Repr

def fields (count : Nat) : ProductFields :=
  .cons .index (.cons .index (.cons .index (.cons .index (ClearStorage.indexFields count .nil))))

def layout (identity : String) (count : Nat) : RecordAppend.Layout := ⟨identity, fields count⟩

def Encodes {carriers : Carriers} (identity : String) (count : Nat)
    (frame : Frame) (record : carriers.Value (layout identity count).type) : Prop :=
  ∃ saved : carriers.ProductValue (ClearStorage.indexFields count .nil),
    ClearStorage.packCoordinates count frame.answers () = some saved ∧
    record = (frame.outer, frame.outerInstance, frame.parentInstance, frame.position, saved)

/-- The number of prior replies is determined by the actual packed frame. -/
theorem Encodes.answers_length {carriers : Carriers} {identity : String} {count : Nat}
    {frame : Frame} {record : carriers.Value (layout identity count).type}
    (encoded : Encodes identity count frame record) : frame.answers.length = count := by
  have width : ∀ (size : Nat) (indices : List Nat)
      (packed : carriers.ProductValue (ClearStorage.indexFields size .nil)),
      ClearStorage.packCoordinates size indices () = some packed → indices.length = size := by
    intro size
    induction size with
    | zero =>
        intro indices packed matched
        cases indices with
        | nil => rfl
        | cons => simp [ClearStorage.packCoordinates] at matched
    | succ size ih =>
        intro indices packed matched
        cases indices with
        | nil => simp [ClearStorage.packCoordinates] at matched
        | cons first rest =>
            obtain ⟨tail, found, _⟩ := Option.map_eq_some_iff.mp matched
            exact congrArg Nat.succ (ih rest tail found)
  obtain ⟨packed, matched, _⟩ := encoded
  exact width count frame.answers packed matched

theorem encoding_exists {carriers : Carriers} (identity : String) (count : Nat)
    (frame : Frame) (width : frame.answers.length = count) :
    ∃ record : carriers.Value (layout identity count).type, Encodes identity count frame record := by
  obtain ⟨saved, packed⟩ := ClearStorage.packCoordinates_exists (carriers := carriers)
    (tail := .nil) count frame.answers () width
  exact ⟨(frame.outer, frame.outerInstance, frame.parentInstance, frame.position, saved), saved, packed, rfl⟩

/-- Equal physical frame records retain the complete parent/continuation
coordinates and answer order, even when all these coordinates have one type. -/
theorem Encodes.unique {carriers : Carriers} {identity : String} {count : Nat}
    {first second : Frame} {record : carriers.Value (layout identity count).type}
    (left : Encodes identity count first record) (right : Encodes identity count second record) :
    first = second := by
  obtain ⟨saved, packed, rfl⟩ := left
  obtain ⟨other, otherPacked, same⟩ := right
  have parts := Prod.mk.inj same
  have innerParts := Prod.mk.inj parts.2
  have parentParts := Prod.mk.inj innerParts.2
  have positionParts := Prod.mk.inj parentParts.2
  obtain ⟨outer, inner, parent, position, rest⟩ :
      first.outer = second.outer ∧ first.outerInstance = second.outerInstance ∧
      first.parentInstance = second.parentInstance ∧ first.position = second.position ∧ saved = other := by
    exact ⟨parts.1, innerParts.1, parentParts.1, positionParts.1, positionParts.2⟩
  cases rest
  have answers := (ClearStorage.packCoordinates_unique count packed otherPacked).1
  cases first
  cases second
  simp_all

def Stored {carriers : Carriers} (identity : String) (count : Nat)
    (records : List (carriers.Value (layout identity count).type)) (slot : Nat) (frame : Frame) : Prop :=
  ∃ record, records[slot]? = some record ∧ Encodes identity count frame record

theorem stored_append {carriers : Carriers} {identity : String} {count : Nat}
    (records : List (carriers.Value (layout identity count).type))
    {frame : Frame} {record : carriers.Value (layout identity count).type}
    (encoded : Encodes identity count frame record) :
    Stored identity count (records ++ [record]) records.length frame :=
  ⟨record, by simp, encoded⟩

/-- Saving the actual encoded fields establishes the relation at the returned
old length. Later resumption does not get to choose a different parent frame. -/
theorem Encodes.save {model : DomainModel} {identity : String} {count : Nat}
    {frame : Frame} {record : model.Value (layout identity count).type}
    (encoded : Encodes identity count frame record)
    (records : List (model.Value (layout identity count).type))
    (data : (layout identity count).type.isHandle = false)
    (fieldData : (fields count).toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (store : Nat) (references : List Nat)
    (readStore : environment[store]? = some (.data ⟨.sequence (layout identity count).type, data, records⟩))
    (readFields : Domain.read environment references = Domain.encodeValues ((fields count).unpack record))
    (bounded : records.length < indexLimit) :
    Stored identity count (records ++ [record]) records.length frame ∧
    Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
      (.done (RecordAppend.result model (layout identity count) data environment records record))
      ((RecordAppend.spine (layout identity count) ⟨environment.length, store, references⟩).block model environment)) :=
  ⟨stored_append records encoded,
    ⟨RecordAppend.simulation model (layout identity count) data fieldData environment store references
      records record readStore readFields bounded⟩⟩

theorem Stored.transport {carriers : Carriers} {identity : String} {count slot : Nat} {frame : Frame}
    {before after : List (carriers.Value (layout identity count).type)}
    (stored : Stored identity count before slot frame) (extension : before <+: after) :
    Stored identity count after slot frame := by
  obtain ⟨record, found, encoded⟩ := stored
  obtain ⟨suffix, rfl⟩ := extension
  exact ⟨record, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found, encoded⟩

theorem Stored.unique {carriers : Carriers} {identity : String} {count slot : Nat} {first second : Frame}
    {records : List (carriers.Value (layout identity count).type)}
    (left : Stored identity count records slot first) (right : Stored identity count records slot second) :
    first = second := by
  obtain ⟨record, found, encoded⟩ := left
  obtain ⟨other, otherFound, otherEncoded⟩ := right
  cases Option.some.inj (found.symm.trans otherFound)
  exact encoded.unique otherEncoded

/-- A physical load returns the immutable record selected at save time.
The index is the current frame instance, not the parent anchor instance. -/
theorem Stored.load {model : DomainModel} {identity : String} {count slot : Nat} {frame : Frame}
    {records : List (model.Value (layout identity count).type)}
    (stored : Stored identity count records slot frame)
    (inputData : (Primitive.sequenceAt (layout identity count).type).arguments.all Domain.localType = true)
    (outputData : (Primitive.sequenceAt (layout identity count).type).results.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues
      (tys := [.sequence (layout identity count).type, .index]) (.cons records (.cons slot .nil))) :
    ∃ record, Encodes identity count frame record ∧
      Domain.View.execute model (.sequenceAt (layout identity count).type) references
        [.data (layout identity count).type] environment =
        .done (environment ++ Original.encodeHelperResult (.cons record .nil)) := by
  obtain ⟨record, found, encoded⟩ := stored
  refine ⟨record, encoded, ?_⟩
  have law := ConnectionPrimitives.view_execute model (.sequenceAt (layout identity count).type)
    (.cons records (.cons slot .nil)) inputData outputData environment references read
  simpa only [Primitive.evaluateOn, found, primitiveOutcome, PIR.Process.bind, Primitive.results,
    List.map_cons, List.map_nil] using law

/-- Ordered answers may have heterogeneous kinds. Indices name cells in the
arena belonging to that kind; they never become untyped payloads. -/
inductive AnswersRead {Kind : Type} {Value : Kind → Type} (arenas : (kind : Kind) → List (Value kind)) :
    {kinds : List Kind} → List Nat → Values Value kinds → Prop where
  | nil : AnswersRead arenas [] .nil
  | cons {kind : Kind} {kinds : List Kind} {index : Nat} {rest : List Nat}
      {value : Value kind} {values : Values Value kinds}
      (read : (arenas kind)[index]? = some value) (tail : AnswersRead arenas rest values) :
      AnswersRead arenas (index :: rest) (.cons value values)

theorem AnswersRead.length {Kind : Type} {Value : Kind → Type}
    {arenas : (kind : Kind) → List (Value kind)} {kinds : List Kind}
    {indices : List Nat} {values : Values Value kinds}
    (read : AnswersRead arenas indices values) : indices.length = kinds.length := by
  induction read with
  | nil => rfl
  | cons found tail ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem AnswersRead.transport {Kind : Type} {Value : Kind → Type}
    {before after : (kind : Kind) → List (Value kind)}
    (extension : ∀ kind, before kind <+: after kind) {kinds : List Kind}
    {indices : List Nat} {values : Values Value kinds} (read : AnswersRead before indices values) :
    AnswersRead after indices values := by
  induction read with
  | nil => exact .nil
  | @cons kind _ index rest value values read tail ih =>
    obtain ⟨suffix, changed⟩ := extension kind
    apply AnswersRead.cons (tail := ih)
    rw [← changed]
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

/-- A resumption appends the current child after all earlier answers. Repeated
equal-valued answers remain separate ordered accesses. -/
theorem AnswersRead.append {Kind : Type} {Value : Kind → Type}
    {arenas : (kind : Kind) → List (Value kind)} {leftKinds rightKinds : List Kind}
    {left right : List Nat} {leftValues : Values Value leftKinds} {rightValues : Values Value rightKinds}
    (first : AnswersRead arenas left leftValues) (second : AnswersRead arenas right rightValues) :
    AnswersRead arenas (left ++ right) (leftValues.append rightValues) := by
  induction first with
  | nil => exact second
  | cons read tail ih => exact .cons read ih

theorem AnswersRead.unique {Kind : Type} {Value : Kind → Type}
    {arenas : (kind : Kind) → List (Value kind)} {kinds : List Kind}
    {indices : List Nat} {first second : Values Value kinds}
    (left : AnswersRead arenas indices first) (right : AnswersRead arenas indices second) : first = second := by
  induction left with
  | nil => cases right; rfl
  | cons read tail ih =>
    cases right with
    | cons other rest => cases Option.some.inj (read.symm.trans other); cases ih rest; rfl

end Zkc.Realization.QueryContinuation
