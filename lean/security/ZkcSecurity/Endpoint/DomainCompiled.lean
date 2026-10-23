module

public import Zkc.Construction.Compiled
public import Zkc.Construction.SourceOccurrences
public import Zkc.Construction.DomainProducer

@[expose] public section

/-! The actual constructed ideal verifier over nominal domain carriers. This
adapter retains the existing admission/check/selection authority and interprets
the supplied artifact with Domain.validate. Native bytes are outside its scope. -/
set_option autoImplicit false

namespace ZkcSecurity.Endpoint.Domain
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Artifacts where
  original : Snapshot
  participant : Participant
  publics : List Ty

abbrev Artifacts.Statement (art : Artifacts) (model : DomainModel) :=
  Values model.toCarriers.Value art.publics

structure Compiled (art : Artifacts) where
  imported : Structured.Imported art.original
  compiled : checkCompiled imported art.participant = .ok ()
  selection : Selection imported.program.payload.entry.outputs
  selected : select imported art.participant = some selection
  checked : selection.check imported art.participant = true
  publics : selection.publics = art.publics
  occurrences : SourceOccurrences.check art.original selection.context art.participant = .ok ()

namespace Compiled
variable {art : Artifacts}

def acceptance (c : Compiled art) {carriers : Carriers}
    (result : Construction.Domain.Result carriers) : Option Bool :=
  match result.values[c.selection.position]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- A typed oracle cannot fail. Its dependent result is read at precisely the
event requested by the actual constructed evaluator. -/
def oracle {m : Type → Type} [Monad m] {carriers : Carriers}
    (query : Construction.Domain.History carriers → (event : Construction.Domain.Event carriers) →
      m (Construction.Domain.Raw event)) : Construction.Domain.Oracle m carriers Unit :=
  fun history event _ => (fun raw => (PIR.Outcome.returned raw, ())) <$> query history event

/-- Invalid statement shape refuses. The interpreter's result and unread proof
are retained; complete acceptance additionally requires an empty suffix. -/
def verifier (c : Compiled art) (model : DomainModel) {m : Type → Type} [Monad m]
    (query : Construction.Domain.History model.toCarriers →
      (event : Construction.Domain.Event model.toCarriers) → m (Construction.Domain.Raw event))
    (statement : art.Statement model) (initial : Construction.Domain.History model.toCarriers)
    (proof : Construction.Domain.Proof model.toCarriers) :
    m (PIR.Outcome (Option Bool) × Construction.Domain.Proof model.toCarriers) :=
  match Construction.Domain.encodeValues statement with
  | none => pure (.stopped .refused, proof)
  | some inputs =>
      (fun result => (Zkc.Transcript.mapOutcome c.acceptance result.outcome, result.state.proof)) <$>
        Construction.Domain.validate model c.imported.program c.selection.context art.participant
          (inputs ++ [.transcript c.selection.context.suite initial]) proof (oracle query) ()

end Compiled

def CompleteAccepted {carriers : Carriers}
    (result : PIR.Outcome (Option Bool) × Construction.Domain.Proof carriers) : Prop :=
  Zkc.Transcript.Accepted (· = some true) result.1 ∧ result.2 = []

end ZkcSecurity.Endpoint.Domain
