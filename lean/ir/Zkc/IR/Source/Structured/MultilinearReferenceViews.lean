module

public import Zkc.IR.Source.Structured.MultilinearReference

@[expose] public section

/-! Smaller mathematical returns for the nominal multilinear library. The
existing complete body laws supply execution; conservation and input retention
supply reconstruction. No field domains or dependency tables are identified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Source.Structured.ReferenceLibrary.Multilinear
open Zkc.Source MultilinearBodies Zkc.Polynomial.Multilinear

variable (model : DomainModel) (domain : String) (bindings : Bindings)

theorem sums_restore_high (entries : List (model.Field domain)) :
    entries.sum - (entries.take (entries.length / 2)).sum =
      (entries.drop (entries.length / 2)).sum := by
  have conservation : (entries.take (entries.length / 2)).sum +
      (entries.drop (entries.length / 2)).sum = entries.sum := by
    simpa only [List.sum_append] using
      congrArg List.sum (List.take_append_drop (entries.length / 2) entries)
  rw [← conservation]
  exact add_sub_cancel_left _ _

def sumsViewOutcome (args : Values model.Value (triple domain)) :
    PIR.Outcome (model.Field domain) :=
  match halvesOutcome model domain (args.get .here) (args.get (.there .here)) with
  | .returned values => .returned (values.get .here).sum
  | .stopped reason => .stopped reason

def sumsViewPack (args : Values model.Value (triple domain)) (low : model.Field domain) :
    Values model.Value [.field domain, .field domain] :=
  .cons low (.cons ((args.get .here).sum - low) .nil)

theorem sums_reachable (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (args : Values model.Value (triple domain))
    (premises : (sums model domain bindings).Requires table args) :
    PIR.Yields (fun values ↦ sumsViewPack model domain args (values.get .here) = values)
      ((sumsBody domain bindings).denote
        (Evaluation.meaningOn model SiteObservations.closed table) args.get) := by
  have execution := (sums model domain bindings).valid table args premises
  change (sumsBody domain bindings).denote
    (Evaluation.meaningOn model SiteObservations.closed table) args.get = _ at execution
  rw [execution]
  cases args with | cons xs rest => cases rest with | cons n rest =>
    cases rest with | cons w rest =>
      cases rest
      simp only [sums, halves, halvesOutcome, Values.get]
      split_ifs <;> simp only [primitiveOutcome, PIR.Yields]
      change sumsViewPack model domain (tableValues model domain xs n w)
          (xs.take (xs.length / 2)).sum =
        .cons (xs.take (xs.length / 2)).sum (.cons (xs.drop (xs.length / 2)).sum .nil)
      simp only [sumsViewPack, tableValues, Values.get, sums_restore_high]

theorem sums_projected (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (args : Values model.Value (triple domain))
    (premises : (sums model domain bindings).Requires table args) :
    ((sumsBody domain bindings).denote
        (Evaluation.meaningOn model SiteObservations.closed table) args.get).bind
      (fun values ↦ .done (values.get .here)) =
        primitiveOutcome (sumsViewOutcome model domain args) := by
  have execution := (sums model domain bindings).valid table args premises
  change (sumsBody domain bindings).denote
    (Evaluation.meaningOn model SiteObservations.closed table) args.get = _ at execution
  rw [execution]
  cases args with | cons xs rest => cases rest with | cons n rest =>
    cases rest with | cons w rest =>
      cases rest
      simp only [sums, halves, halvesOutcome, sumsViewOutcome, Values.get]
      split_ifs <;> rfl

/-- Only the low endpoint is stored. The original halves dependency and every
raw-input stop remain part of the exact law. -/
def sumsView : ReferenceLaw model (triple domain) [.field domain, .field domain] :=
  ReferenceLaw.ofReachableView (sumsBody domain bindings) (sums model domain bindings).Requires
    (fun _ values ↦ values.get .here) (sumsViewPack model domain) (sumsViewOutcome model domain)
    (sums_reachable model domain bindings) (sums_projected model domain bindings)

theorem sumsView_reference (args : Values model.Value (triple domain)) :
    (sumsView model domain bindings).reference args = (sums model domain bindings).reference args := by
  cases args with | cons xs rest => cases rest with | cons n rest =>
    cases rest with | cons w rest =>
      cases rest
      simp only [sumsView, ReferenceLaw.ofReachableView, sumsViewOutcome,
        sums, halves, halvesOutcome, Values.get]
      split_ifs <;> try rfl
      change PIR.Outcome.returned
        (sumsViewPack model domain (tableValues model domain xs n w)
          (xs.take (xs.length / 2)).sum) =
          .returned (.cons (xs.take (xs.length / 2)).sum (.cons (xs.drop (xs.length / 2)).sum .nil))
      simp only [sumsViewPack, tableValues, Values.get, sums_restore_high]

def firstViewPack (args : Values model.Value (firstInputs domain))
    (entries : List (model.Field domain)) : Values model.Value (triple domain) :=
  tableValues model domain entries (args.get (.there .here) - 1)
    (args.get (.there (.there .here)))

def firstViewOutcome (args : Values model.Value (firstInputs domain)) :
    PIR.Outcome (List (model.Field domain)) :=
  if 0 < args.get (.there .here) then
    .returned (restrictValues (args.get .here) (args.get (.there (.there (.there .here)))))
  else .stopped .reject

theorem first_reachable (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (args : Values model.Value (firstInputs domain))
    (premises : (first model domain bindings).Requires table args) :
    PIR.Yields (fun values ↦ firstViewPack model domain args (values.get .here) = values)
      ((firstBody domain bindings).denote
        (Evaluation.meaningOn model SiteObservations.closed table) args.get) := by
  have execution := (first model domain bindings).valid table args premises
  change (firstBody domain bindings).denote
    (Evaluation.meaningOn model SiteObservations.closed table) args.get = _ at execution
  rw [execution]
  simp only [first, firstOutcome]
  split <;> first | rfl | trivial

theorem first_projected (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (args : Values model.Value (firstInputs domain))
    (premises : (first model domain bindings).Requires table args) :
    ((firstBody domain bindings).denote
        (Evaluation.meaningOn model SiteObservations.closed table) args.get).bind
      (fun values ↦ .done (values.get .here)) =
        primitiveOutcome (firstViewOutcome model domain args) := by
  have execution := (first model domain bindings).valid table args premises
  change (firstBody domain bindings).denote
    (Evaluation.meaningOn model SiteObservations.closed table) args.get = _ at execution
  rw [execution]
  simp only [first, firstOutcome, firstViewOutcome]
  split_ifs <;> rfl

/-- Restriction stores entries and restores dimension and columns from inputs.
Its exact applicability is the existing nominal library applicability. -/
def firstView : ReferenceLaw model (firstInputs domain) (triple domain) :=
  ReferenceLaw.ofReachableView (firstBody domain bindings) (first model domain bindings).Requires
    (fun _ values ↦ values.get .here) (firstViewPack model domain) (firstViewOutcome model domain)
    (first_reachable model domain bindings) (first_projected model domain bindings)

theorem firstView_reference (args : Values model.Value (firstInputs domain)) :
    (firstView model domain bindings).reference args = firstOutcome model domain args := by
  dsimp only [firstView, ReferenceLaw.ofReachableView, firstViewOutcome, firstOutcome]
  split_ifs <;> rfl

end Zkc.Source.Structured.ReferenceLibrary.Multilinear
