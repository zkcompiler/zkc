module

public import ZkcSecurity.Realizations.Sumcheck.OriginalComponent
public import Zkc.Protocols.Sumcheck.Source.Reduce
public import ZkcSecurity.FiatShamir.OriginalTransport
public import ZkcSecurity.FiatShamir.DomainViewReading
public import ZkcSecurity.Families.Sumcheck.TableComponentNominal

@[expose] public section

/-! Shared source declaration, routing contract, and complete root result.
All-input source readings and honest readback use these definitions without
installing a separate shaped-only security presentation. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalSecurity
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck
open TableComponent

namespace SourceFamily
/-- One original declaration reference shared by producer and validator readback. -/
abbrev sourceReference := @ZkcExamples.Structured.OriginalSumcheckLibrary.reduce
end SourceFamily

variable {F G : Type}

abbrev ConstructionState := Zkc.Construction.Original.State (uniformCarriers F G)

/-- Routing is checked at the reached source index, with its actual outer
source frames. No compiled operation count reconstructs an occurrence. -/
structure Routes (routing : Zkc.Construction.Original.Routing)
    (context : Realizations.Sumcheck.Original.Context) (schedule : Nominal.Schedule "bls12-381.fr")
    (frames : Zkc.Construction.Original.Frames) : Prop where
  mode : routing.mode = .validator
  low : ∀ index, routing.message (frames ++ [⟨Realizations.Sumcheck.Original.loopSite context, index⟩])
    (ZkcExamples.Structured.SumcheckVerifierLaws.lowSite context.protocol)
    (context.protocol.roles 0) routing.context.validator = some (schedule.low index)
  high : ∀ index, routing.message (frames ++ [⟨Realizations.Sumcheck.Original.loopSite context, index⟩])
    (ZkcExamples.Structured.SumcheckVerifierLaws.highSite context.protocol)
    (context.protocol.roles 0) routing.context.validator = some (schedule.high index)
  draw : ∀ index, routing.draw (frames ++ [⟨Realizations.Sumcheck.Original.loopSite context, index⟩])
    (ZkcExamples.Structured.SumcheckVerifierLaws.challengeSite context.protocol)
    "bls12-381.fr" context.handle = some (schedule.query index)
  delivery : ∀ index, routing.message (frames ++ [⟨Realizations.Sumcheck.Original.loopSite context, index⟩])
    (ZkcExamples.Structured.SumcheckVerifierLaws.deliverySite context.protocol)
    routing.context.validator (context.protocol.roles 0) = some (schedule.delivery index)

/-- Complete original source root return, before any artifact projection. -/
abbrev Result := Values (Component (assignment F G)) [.boolean] × ConstructionState (F := F) (G := G)

def acceptance (result : Result (F := F) (G := G)) : Option Bool :=
  match result.1 with
  | .cons value .nil => value

end ZkcSecurity.Realizations.Sumcheck.OriginalSecurity
