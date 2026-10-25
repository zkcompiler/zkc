module

public import Zkc.Source.Structured.Import
public import Zkc.Source.Structured.Participant

@[expose] public section

namespace Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Each named helper captures its checked prefix. Protocols have their own
context-parametric table, with the same Region/Process interpretation. -/
def UnitPayload.tables (payload : UnitPayload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] : OpenTables F G :=
  payload.definitions.foldl (Evaluation.ComponentTables.extend (observedSites F G)) ⟨[], []⟩

/-- Every protocol closure captures its dependency prefix and the unqualified helpers. -/
def UnitPayload.protocolTable (payload : UnitPayload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] :
    ProtocolTable (assignment F G) (observedInterface F G) :=
  payload.protocols.foldl
    (extendProtocolTable (observedSites F G) observeAction (payload.tables F G)) []

/-- Plain closures are derived by interpretation of the same observed table. -/
def UnitPayload.plainProtocolTable (payload : UnitPayload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] :
    ProtocolTable (assignment F G) (participantInterface F G) :=
  payload.protocols.foldl
    (extendProtocolTable (.silent (participantInterface F G)) (participantActions F G)
      (payload.definitions.foldl
        (Evaluation.ComponentTables.extend (.silent (participantInterface F G))) ⟨[], []⟩)) []

theorem UnitPayload.protocolTable_forgetSites (payload : UnitPayload) :
    ProtocolTable.Interprets forgetSites (payload.protocolTable F G) (payload.plainProtocolTable F G) :=
  ProtocolTable.fold_interpret forgetSites observedSites_forgetSites observeAction_forgetSites
    (Evaluation.ComponentTables.fold_forgetSites payload.definitions)
    (ProtocolTable.Interprets.empty _) payload.protocols

def Program.observed (program : Program) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (self : Nat) (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    PIR.Process (observedInterface F G)
      (Values (Component (assignment F G)) program.payload.entry.outputs) :=
  invokeProtocol (program.payload.protocolTable F G) program.payload.entry.signature {} self inputs

/-- A participant is selected by its index in this root's roster. Admission
validates role references; callers choose a valid self (the CLI checks it). -/
def Program.participant (program : Program) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (self : Nat) (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    PIR.Process (participantInterface F G)
      (Values (Component (assignment F G)) program.payload.entry.outputs) :=
  (program.observed F G self inputs).interpret forgetSites

theorem UnitPayload.tables_adequate (payload : UnitPayload) :
    (payload.tables F G).Adequate :=
  Evaluation.ComponentTables.adequate_fold (observedSites F G) _
    Evaluation.ComponentTables.adequate_empty _

end Zkc.Source.Structured
