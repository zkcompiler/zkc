module

public import Zkc.Source.Structured.Import
public import Zkc.Source.Structured.Participant

@[expose] public section

namespace Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Each named body captures its checked prefix. Protocol roots never enter
these closure tables. -/
def UnitPayload.tables (payload : UnitPayload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] : OpenTables F G :=
  payload.definitions.foldl (Evaluation.ComponentTables.extend (observedSites F G)) ⟨[], []⟩

def Program.observed (program : Program) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (self : Nat) (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    PIR.Proc (observedInterface F G)
      (Values (Component (assignment F G)) program.payload.entry.outputs) :=
  program.payload.entry.observed (program.payload.tables F G) self inputs

/-- A participant is selected by its index in this root's roster. Admission
validates role references; callers choose a valid self (the CLI checks it). -/
def Program.participant (program : Program) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (self : Nat) (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    PIR.Proc (participantInterface F G)
      (Values (Component (assignment F G)) program.payload.entry.outputs) :=
  (program.observed F G self inputs).interpret forgetSites

theorem UnitPayload.tables_adequate (payload : UnitPayload) :
    (payload.tables F G).Adequate :=
  Evaluation.ComponentTables.adequate_fold (observedSites F G) _
    Evaluation.ComponentTables.adequate_empty _

/-- Direct plain meaning, obtained by erasing only the internal site effects. -/
theorem Program.participant_direct (program : Program) (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G self inputs =
      (program.payload.entry.body.denote
        (participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
          (program.payload.definitions.foldl
            (Evaluation.ComponentTables.extend (F := F) (G := G) (.silent (participantInterface F G)))
            ⟨[], []⟩) self)
        (maskValues self program.payload.entry.inputScopes inputs).get).bind
          (fun results => .done (maskValues self program.payload.entry.outputScopes results)) :=
  program.payload.entry.participant_direct_fold program.payload.definitions self inputs

end Zkc.Source.Structured
