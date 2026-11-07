module

public import Zkc.Realization.VirtualStorage
public import Tests.CaptureLayout

@[expose] public section

namespace Tests.VirtualStorage
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization.VirtualStorage

abbrev fields : ProductFields := .cons (.product ClearStorage.layout.referenceIdentity "Record"
  Realization.CaptureLayout.referenceFields) (.cons (.product ClearStorage.layout.referenceIdentity "Record"
    Realization.CaptureLayout.referenceFields) (.cons .index .nil))

def layout : Layout CaptureLayout.inputs :=
  ⟨8, "virtual-record", "virtual-reference", ClearStorage.location 0 0, fields, CaptureLayout.layout⟩

def record (model : DomainModel) (outer inner parameter : Nat) : model.Value layout.recordType :=
  (outer, inner, 2, 2, (7, 0, ()), (7, 1, ()), parameter, ())

def captures (model : DomainModel) (parameter : Nat) :=
  CaptureLayout.captures model (ClearStorage.word model 2 7).anchor
    (ClearStorage.word model 2 9).anchor parameter

theorem encodes (model : DomainModel) (outer inner parameter : Nat) :
    Encodes (CaptureLayout.association model) layout (ClearStorage.location outer inner) 2 2
      (captures model parameter) (record model outer inner parameter) :=
  ⟨rfl, CaptureLayout.encoded model parameter, CaptureLayout.captures_related model parameter, rfl⟩

/-- The capture record actually executes the same immutable allocator as a base
publication, at arbitrary coordinates and after arbitrary earlier records. -/
theorem allocated (model : DomainModel) (outer inner parameter : Nat)
    (prior : List (model.Value layout.recordType)) (bounded : prior.length < indexLimit)
    (program : Program) (context : Context) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.sequence layout.recordType, rfl, prior⟩,
       .data (.index outer), .data (.index inner), .data (.index 2), .data (.index 2),
       .data ⟨Realization.CaptureLayout.referenceType ClearStorage.layout.referenceIdentity, rfl, (7, 0, ())⟩,
       .data ⟨Realization.CaptureLayout.referenceType ClearStorage.layout.referenceIdentity, rfl, (7, 1, ())⟩,
       .data (.index parameter)]
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (Realization.RecordAllocator.result model layout.allocator rfl environment prior
        (record model outer inner parameter)))
      (Domain.evaluate model program context
        (Realization.RecordAllocator.instructions layout.allocator ⟨8, 0, [1, 2, 3, 4, 5, 6, 7]⟩)
        environment)) := by
  dsimp only
  exact ((encodes model outer inner parameter).allocate prior program context rfl rfl
    _ 0 [1, 2, 3, 4, 5, 6, 7] rfl rfl (by decide) bounded).2

/-- The record's actual projection reads the parameter following both parents. -/
theorem parameter_read (model : DomainModel) (outer inner parameter : Nat) :
    ∃ physical, Realization.CaptureLayout.Related (CaptureLayout.association model) layout.captures
        (captures model parameter) physical ∧
      ConnectionCalculations.closedCalculation model
        (.getProduct layout.recordIdentity "Record" layout.recordFields .index
          (.there (.there (.there (.there (.there (.there .here)))))))
        (.cons (record model outer inner parameter) .nil) =
          .done (.cons (physical.get (.there (.there .here))) .nil) :=
  (encodes model outer inner parameter).capture_read (.there (.there .here))

theorem wrong_location_refused (model : DomainModel) (parameter : Nat) :
    ¬ Encodes (CaptureLayout.association model) layout (ClearStorage.location 3 5) 2 2
      (captures model parameter) (record model 3 4 parameter) := by
  intro wrong
  have equal := (encodes model 3 4 parameter).location_unique wrong
  have distinct : ClearStorage.location 3 4 ≠ ClearStorage.location 3 5 := by decide
  exact distinct equal

#print axioms allocated
#print axioms parameter_read
#print axioms Realization.VirtualStorage.Encodes.captures_unique
end Tests.VirtualStorage
