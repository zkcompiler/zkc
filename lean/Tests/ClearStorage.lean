module

public import Zkc.Realization.ClearStorageAllocation
public import Zkc.Realization.ClearStorageLookup

@[expose] public section

/-! Same-typed and equal-payload publications still retain different anchors.
Storage ordinals do not replace the two actual nested iteration coordinates. -/
namespace Tests.ClearStorage
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Realization.ClearStorage

abbrev kind : OracleKind := .table .index none

def location (outer inner : Nat) : OracleLocation :=
  ⟨⟨3, [.application 3 [4], .iteration 2 [6] outer,
    .application 2 [6, 1], .iteration 1 [2] inner]⟩, 0, [7]⟩

def layout : Layout kind :=
  ⟨7, "selected-clear-record", "selected-clear-reference", location 0 0, 0, [1]⟩

def word (model : DomainModel) (outer inner : Nat) : PublishedWords.Word model kind.answer :=
  ⟨kind, (location outer inner).anchor, 2, 0, [1], location outer inner, ([11, 22] : List Nat)⟩

def record (model : DomainModel) (outer inner : Nat) : model.Value layout.recordType :=
  (outer, inner, 2, 1, [11, 22], ())

theorem record_encodes (model : DomainModel) (outer inner : Nat) :
    Encodes layout (word model outer inner) (record model outer inner) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual allocator installs the same encoded word, for every nested
source coordinate and any previously allocated records. -/
theorem actual_allocation (model : DomainModel) (outer inner : Nat)
    (prior : List (model.Value layout.recordType)) (bounded : prior.length < indexLimit)
    (program : Program) (context : Construction.Context) :
    let environment : Construction.Domain.Environment model.toCarriers :=
      [.data ⟨.sequence layout.recordType, rfl, prior⟩, .data (.index outer),
       .data (.index inner), .data (.index 2), .data (.index 1), .data ⟨.indices, rfl, [11, 22]⟩]
    Stored layout [⟨kind.answer, word model outer inner⟩] (prior ++ [record model outer inner])
      (layout.constructor, prior.length) (word model outer inner) ∧
    Nonempty (Construction.Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (Zkc.Realization.RecordAllocator.result model layout.allocator rfl environment prior
        (record model outer inner)))
      (Construction.Domain.evaluate model program context
        (Zkc.Realization.RecordAllocator.instructions layout.allocator ⟨6, 0, [1, 2, 3, 4, 5]⟩)
        environment)) := by
  dsimp only
  apply (record_encodes model outer inner).allocate [] prior program context rfl rfl
  · rfl
  · rfl
  · decide
  · exact bounded

def words (model : DomainModel) : PublishedWords.Table model :=
  [⟨.index, word model 2 9⟩, ⟨.index, word model 2 7⟩]

def records (model : DomainModel) : List (model.Value layout.recordType) :=
  [record model 2 7, record model 2 9]

theorem first_stored (model : DomainModel) :
    Stored layout (words model) (records model) (7, 0) (word model 2 7) := by
  have first := stored_append layout [] [] _ _ (record_encodes model 2 7)
  exact first.transport
    (PublishedWords.cons_preserves _ (word model 2 9) (by rfl)) (by exact ⟨[record model 2 9], rfl⟩)

/-- Actual lookup retains the first publication even after the equal-payload
second word has been stored at a different source anchor. -/
theorem lookup_first (model : DomainModel) (program : Program) (context : Construction.Context) :
    let environment : Construction.Domain.Environment model.toCarriers :=
      [.data (.index 7), .data (.index 0),
        .data ⟨.sequence layout.recordType, rfl, records model⟩]
    ∃ record, Encodes layout (word model 2 7) record ∧
      Nonempty (Construction.Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
        (.done (environment ++ [.data (.index 7), .data (.boolean true),
          .data ⟨layout.recordType, rfl, record⟩]))
        (Construction.Domain.evaluate model program context
          (Zkc.Realization.RecordLookup.instructions layout.lookup ⟨3, 0, 1, 2, "record"⟩)
          environment)) :=
  (first_stored model).lookup program context rfl _ 0 1 2 "record" rfl rfl rfl (by decide)

theorem second_stored (model : DomainModel) :
    Stored layout (words model) (records model) (7, 1) (word model 2 9) :=
  stored_append layout [⟨.index, word model 2 7⟩] [record model 2 7] _ _ (record_encodes model 2 9)

/-- Equal cells and identical types cannot justify the swapped association. -/
theorem swapped_anchor_refused (model : DomainModel) :
    ¬ Stored layout (words model) (records model) (7, 1) (word model 2 7) := by
  intro wrong
  have equal := (second_stored model).anchor_unique wrong
  have different : (word model 2 9).anchor ≠ (word model 2 7).anchor := by
    change (location 2 9).anchor ≠ (location 2 7).anchor
    decide
  exact different equal

theorem wrong_constructor_refused (model : DomainModel) :
    ¬ Stored layout (words model) (records model) (8, 0) (word model 2 7) := by
  rintro ⟨_, impossible, _⟩
  contradiction

/-- The physical slot is one, while the two source indices are two and nine. -/
example (model : DomainModel) :
    Primitive.evaluateOn model.toFieldModel (.sequenceAt layout.recordType)
      (.cons (records model) (.cons 1 .nil)) = .returned (.cons (record model 2 9) .nil) := rfl

example (model : DomainModel) :
    Primitive.evaluateOn model.toFieldModel (.sequenceAt layout.recordType)
      (.cons (records model) (.cons 2 .nil)) = .stopped .refused := rfl

example (model : DomainModel) :
    packCoordinates (carriers := model.toCarriers) (tail := .cons .index .nil)
      2 [7] (3, ()) = none := rfl

example (model : DomainModel) :
    packCoordinates (carriers := model.toCarriers) (tail := .cons .index .nil)
      2 [7, 1, 9] (3, ()) = none := rfl

/-- Matching indices at a sibling application do not identify an anchor. -/
example : staticLocation (location 2 7) ≠ staticLocation
    ⟨⟨3, [.application 3 [5], .iteration 2 [6] 2,
      .application 2 [6, 1], .iteration 1 [2] 7]⟩, 0, [7]⟩ := by decide

def request (model : DomainModel) : OraclePublication.Request model :=
  ⟨kind, (location 2 9).anchor, 2, 0, [1], location 2 9, none⟩

def before (model : DomainModel) : PublishedWords.State model Nat := ⟨[], 5⟩

def attempt : PIR.Execution Nat Nat (List Nat) := ⟨.returned [11, 22], 6, [42]⟩

/-- Admission comes from the actual publication outcome, including its fresh
anchor and valid shape checks. The record is then derived from that request. -/
theorem publication_stored (model : DomainModel) :
    ∃ proposal record, attempt.outcome = .returned proposal ∧
      Stored layout (PublishedWords.finish (request model) (before model) attempt).state.words
        [record] (7, 0)
        (PublishedWords.word (request model) (PublishedWords.selected (request model) proposal)) :=
  finish_stored (request model) layout (before model) [] attempt rfl rfl rfl rfl

/-- A refused shape retains the old table, auxiliary poststate and events. -/
example (model : DomainModel) :
    PublishedWords.finish (request model) (before model) ⟨.returned ([11] : List Nat), 6, [42]⟩ =
      (⟨.stopped .refused, ⟨[], 6⟩, [42]⟩ : PIR.Execution _ Nat Unit) := rfl

example (model : DomainModel) :
    PublishedWords.finish (request model) (before model) ⟨.stopped .exhausted, 6, [42]⟩ =
      (⟨.stopped .exhausted, ⟨[], 6⟩, [42]⟩ : PIR.Execution _ Nat Unit) := rfl

/-- Re-publication cannot overwrite even an equal-payload word. -/
example (model : DomainModel) :
    PublishedWords.finish (request model) ⟨words model, 5⟩ attempt =
      (⟨.stopped .refused, ⟨words model, 6⟩, [42]⟩ : PIR.Execution _ Nat Unit) := rfl

example (model : DomainModel) :
    Zkc.Construction.ConnectionCalculations.closedCalculation model
      (.getProduct layout.recordIdentity "Record" layout.fields kind.data
        (afterCoordinates layout.depth (.there (.there .here))))
      (.cons (record model 2 9) .nil) = .done (.cons ([11, 22] : List Nat) .nil) :=
  (record_encodes model 2 9).data

#print axioms Zkc.Realization.ClearStorage.finish_stored
#print axioms Zkc.Realization.ClearStorage.Stored.read_view
#print axioms Zkc.Realization.ClearStorage.Stored.transport
#print axioms swapped_anchor_refused
#print axioms first_stored
#print axioms actual_allocation
#print axioms lookup_first
end Tests.ClearStorage
