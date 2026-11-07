module

public import Zkc.Realization.ClearStorageLocation
public import Zkc.Source.Structured.PublishedWordsLaws

@[expose] public section

/-! The representation relation for clear immutable oracle storage. The native
allocator appends a nominal record and returns (constructor, old length). Its
record stores actual iteration coordinates, rows, leaf count and clear data.
These laws relate those existing values to the logical publication provider;
they introduce no second execution semantics or trusted generated-name rule.
Actual source/candidate association and whole-program simulation remain separate.
-/

set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source Zkc.Source.Structured

/-- One statically selected base constructor at one role. Identities are the
complete nominal strings exported by the compiler, not author-chosen aliases. -/
structure Layout (kind : OracleKind) where
  constructor : Nat
  recordIdentity : String
  referenceIdentity : String
  location : OracleLocation
  holder : Nat
  receivers : List Nat

variable {kind : OracleKind}

def Layout.depth (layout : Layout kind) : Nat := (coordinates layout.location.invocation.frames).length

def indexFields : Nat → ProductFields → ProductFields
  | 0, tail => tail
  | depth + 1, tail => .cons .index (indexFields depth tail)

def Layout.fields (layout : Layout kind) : ProductFields :=
  indexFields layout.depth (.cons .index (.cons .index (.cons kind.data .nil)))

def Layout.recordType (layout : Layout kind) : Ty :=
  .product layout.recordIdentity "Record" layout.fields

def Layout.referenceType (layout : Layout kind) : Ty :=
  .product layout.referenceIdentity "Record" (.cons .index (.cons .index .nil))

/-- Exact arity, including the zero-coordinate case. Missing or extra indices
cannot silently change the storage record's field positions. -/
def packCoordinates {carriers : Carriers} {tail : ProductFields} :
    (depth : Nat) → List Nat → carriers.ProductValue tail →
      Option (carriers.ProductValue (indexFields depth tail))
  | 0, [], value => some value
  | depth + 1, index :: rest, value => (packCoordinates depth rest value).map (index, ·)
  | _, _, _ => none

theorem packCoordinates_exists {carriers : Carriers} {tail : ProductFields}
    (depth : Nat) (indices : List Nat) (value : carriers.ProductValue tail)
    (length : indices.length = depth) :
    ∃ packed, packCoordinates depth indices value = some packed := by
  induction depth generalizing indices with
  | zero =>
    cases indices with
    | nil => exact ⟨value, rfl⟩
    | cons => simp at length
  | succ depth ih =>
    cases indices with
    | nil => simp at length
    | cons index rest =>
      obtain ⟨packed, found⟩ := ih rest (by simpa using length)
      exact ⟨(index, packed), by change (packCoordinates depth rest value).map _ = _; rw [found]; rfl⟩

theorem packCoordinates_unique {carriers : Carriers} {tail : ProductFields}
    (depth : Nat) {left right : List Nat} {x y : carriers.ProductValue tail}
    {packed : carriers.ProductValue (indexFields depth tail)}
    (first : packCoordinates depth left x = some packed)
    (second : packCoordinates depth right y = some packed) : left = right ∧ x = y := by
  induction depth generalizing left right with
  | zero =>
    cases left with
    | cons => simp [packCoordinates] at first
    | nil =>
      cases right with
      | cons => simp [packCoordinates] at second
      | nil => exact ⟨rfl, (Option.some.inj first).trans (Option.some.inj second).symm⟩
  | succ depth ih =>
    cases left with
    | nil => simp [packCoordinates] at first
    | cons i left =>
      cases right with
      | nil => simp [packCoordinates] at second
      | cons j right =>
        rcases packed with ⟨index, packed⟩
        obtain ⟨a, ha, equal⟩ := Option.map_eq_some_iff.mp first
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        obtain ⟨b, hb, equal⟩ := Option.map_eq_some_iff.mp second
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        obtain ⟨rfl, rfl⟩ := ih ha hb
        exact ⟨rfl, rfl⟩

variable {model : DomainModel}

/-- The base clear record uses one leaf. Virtual records and authenticated
schemes have different payloads and need their own representation relation. -/
def Layout.encode (layout : Layout kind) (word : PublishedWords.Word model kind.answer) :
    Option (model.Value layout.recordType) :=
  packCoordinates layout.depth (coordinates word.location.invocation.frames)
    (word.rows, 1, oracleRowsData model.toCarriers kind word.cells, ())

/-- Besides physical bits, representation retains the exact publication
identity and its static owner information. Equal cells never identify handles. -/
structure Encodes (layout : Layout kind) (word : PublishedWords.Word model kind.answer)
    (record : model.Value layout.recordType) : Prop where
  kind_eq : word.kind = kind
  location : staticLocation word.location = staticLocation layout.location
  anchor : word.anchor = word.location.anchor
  holder : word.holder = layout.holder
  receivers : word.receivers = layout.receivers
  encoded : layout.encode word = some record

/-- A source-selected layout determines a record for every published word.
The coordinates are extracted from its reached location, never supplied by an
instance author or inferred from the physical allocation ordinal. -/
theorem encoding_exists (layout : Layout kind) (word : PublishedWords.Word model kind.answer)
    (nominal : word.kind = kind)
    (location : staticLocation word.location = staticLocation layout.location)
    (anchor : word.anchor = word.location.anchor)
    (holder : word.holder = layout.holder) (receivers : word.receivers = layout.receivers) :
    ∃ record, Encodes layout word record := by
  have shape : staticFrames word.location.invocation.frames =
      staticFrames layout.location.invocation.frames :=
    congrArg (fun value ↦ value.invocation.frames) location
  obtain ⟨record, encoded⟩ := packCoordinates_exists (carriers := model.toCarriers)
    (tail := .cons .index (.cons .index (.cons kind.data .nil))) layout.depth
    (coordinates word.location.invocation.frames)
    (word.rows, 1, oracleRowsData model.toCarriers kind word.cells, ())
    (coordinates_length_of_static shape)
  exact ⟨record, nominal, location, anchor, holder, receivers, encoded⟩

/-- The checked reference selects both a constructor and an immutable slot.
The provider lookup is part of the relation, not a new field in native data. -/
def Stored (layout : Layout kind) (words : PublishedWords.Table model)
    (records : List (model.Value layout.recordType)) (reference : Nat × Nat)
    (word : PublishedWords.Word model kind.answer) : Prop :=
  ∃ record, reference.1 = layout.constructor ∧ records[reference.2]? = some record ∧
    PublishedWords.find words kind.answer word.anchor = some word ∧ Encodes layout word record

/-- Appending a publication record assigns exactly the old sequence
length. It does not reuse a source loop index as an allocation counter. -/
theorem stored_append (layout : Layout kind) (words : PublishedWords.Table model)
    (records : List (model.Value layout.recordType))
    (word : PublishedWords.Word model kind.answer) (record : model.Value layout.recordType)
    (encoding : Encodes layout word record) :
    Stored layout (⟨kind.answer, word⟩ :: words) (records ++ [record])
      (layout.constructor, records.length) word := by
  refine ⟨record, rfl, by simp, ?_, encoding⟩
  simp [PublishedWords.find]

/-- The actual provider return establishes the publication side of allocation.
Only the selected source layout is a static prerequisite; word contents are
obtained from the attempted publication and need no mathematical premise. -/
theorem finish_stored {Aux E : Type} (request : OraclePublication.Request model)
    (layout : Layout request.kind) (before : PublishedWords.State model Aux)
    (records : List (model.Value layout.recordType))
    (attempt : PIR.Execution Aux E (List (model.Value request.kind.answer)))
    (success : (PublishedWords.finish request before attempt).outcome = .returned ())
    (location : staticLocation request.location = staticLocation layout.location)
    (holder : request.holder = layout.holder) (receivers : request.receivers = layout.receivers) :
    ∃ proposal record, attempt.outcome = .returned proposal ∧
      Stored layout (PublishedWords.finish request before attempt).state.words
        (records ++ [record]) (layout.constructor, records.length)
        (PublishedWords.word request (PublishedWords.selected request proposal)) := by
  obtain ⟨proposal, returned, _, valid⟩ := PublishedWords.finish_admitted request before attempt success
  have anchor : request.anchor = request.location.anchor := by
    simp only [PublishedWords.valid, Bool.and_eq_true, beq_iff_eq] at valid
    exact valid.1.1
  obtain ⟨record, encoding⟩ := encoding_exists layout
    (PublishedWords.word request (PublishedWords.selected request proposal)) rfl location anchor holder receivers
  obtain ⟨sameProposal, sameReturn, installed⟩ := PublishedWords.finish_success request before attempt success
  have same := PIR.Outcome.returned.inj (returned.symm.trans sameReturn)
  subst sameProposal
  refine ⟨proposal, record, returned, ?_⟩
  rw [installed]
  exact stored_append layout before.words records _ record encoding

/-- Provider extension and physical append preserve an existing association.
Auxiliary counters, events and later failures do not occur in this relation. -/
theorem Stored.transport {layout : Layout kind} {before after : PublishedWords.Table model}
    {records later : List (model.Value layout.recordType)} {reference : Nat × Nat}
    {word : PublishedWords.Word model kind.answer}
    (stored : Stored layout before records reference word)
    (provider : PublishedWords.Preserves before after) (physical : records <+: later) :
    Stored layout after later reference word := by
  obtain ⟨suffix, rfl⟩ := physical
  obtain ⟨record, constructor, atSlot, publication, encoding⟩ := stored
  refine ⟨record, constructor, ?_, provider.lookup _ _ _ publication, encoding⟩
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp atSlot).1).trans atSlot

/-- For one static source construction, the encoded coordinates determine its
logical anchor. A same-typed, equal-payload record at another iteration differs. -/
theorem Encodes.anchor_unique {layout : Layout kind}
    {first second : PublishedWords.Word model kind.answer}
    {record : model.Value layout.recordType}
    (left : Encodes layout first record) (right : Encodes layout second record) :
    first.anchor = second.anchor := by
  have indices := (packCoordinates_unique layout.depth left.encoded right.encoded).1
  have location := location_unique (left.location.trans right.location.symm) indices
  rw [left.anchor, right.anchor, location]

/-- A reference cannot be reassociated with another published anchor, even
when both references, records and payloads have the same declared types. -/
theorem Stored.anchor_unique {layout : Layout kind} {words : PublishedWords.Table model}
    {records : List (model.Value layout.recordType)} {reference : Nat × Nat}
    {first second : PublishedWords.Word model kind.answer}
    (left : Stored layout words records reference first)
    (right : Stored layout words records reference second) : first.anchor = second.anchor := by
  obtain ⟨record, _, atSlot, _, encoding⟩ := left
  obtain ⟨other, _, otherSlot, _, otherEncoding⟩ := right
  cases Option.some.inj (atSlot.symm.trans otherSlot)
  exact encoding.anchor_unique otherEncoding

/-- Record access uses the existing checked primitive, including its refusal
on an invalid slot. No alternative storage reader is introduced here. -/
theorem Stored.read_record {layout : Layout kind} {words : PublishedWords.Table model}
    {records : List (model.Value layout.recordType)} {reference : Nat × Nat}
    {word : PublishedWords.Word model kind.answer}
    (stored : Stored layout words records reference word) :
    ∃ record, Encodes layout word record ∧
      Primitive.evaluateOn model.toFieldModel (.sequenceAt layout.recordType)
        (.cons records (.cons reference.2 .nil)) = .returned (.cons record .nil) := by
  obtain ⟨record, _, atSlot, _, encoding⟩ := stored
  refine ⟨record, encoding, ?_⟩
  simp only [Primitive.evaluateOn, atSlot]

end Zkc.Realization.ClearStorage
