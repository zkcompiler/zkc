module

public import Zkc.Source.Structured.DomainParticipantInterpretation

@[expose] public section

/-! An occurrence view of the same admitted nominal source interpreter.

Only reached protocol iterations add boundaries. Their coordinates are the
actual induction indices; calls retain the existing root-qualified site and
role substitution. Erasing boundaries recovers the existing participant
process for every input and every response, including incomplete and stopped
runs. This is a source-view theorem, not construction or cryptographic transport.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured.Occurrence

structure Frame where
  site : String
  index : Nat
  deriving DecidableEq, Repr

inductive Action (carriers : Carriers) where
  | enter (frame : Frame)
  | leave (frame : Frame)
  | action (operation : (participantInterfaceOn carriers).Op)

abbrev signature (carriers : Carriers) : PIR.Signature where
  Op := Action carriers
  Reply
    | .enter _ | .leave _ => Unit
    | .action operation => (participantInterfaceOn carriers).Reply operation

variable {carriers : Carriers}

def actions : PIR.OperationInterpretation (participantInterfaceOn carriers) (signature carriers) :=
  fun operation => .call (.action operation) .done

def iterations : IterationObservations (signature carriers) :=
  .observed (fun site index => .call (.enter ⟨site, index⟩) .done)
    (fun site index => .call (.leave ⟨site, index⟩) .done)

def erase : PIR.OperationInterpretation (signature carriers) (participantInterfaceOn carriers)
  | .enter _ | .leave _ => .done ()
  | .action operation => .call operation .done

theorem actions_erase (operation : (participantInterfaceOn carriers).Op) :
    (actions operation).interpret erase = participantActionsOn carriers operation := by
  simp only [actions, erase, participantActionsOn, PIR.Process.interpret, PIR.Process.bind_done]

theorem iterations_erase : IterationObservations.Interprets
    (erase (carriers := carriers)) iterations .silent := by
  constructor <;> intro site index <;> rfl

/-- The helper bodies and every protocol closure come from the same payload. -/
def table (model : DomainModel) (payload : UnitPayload) :
    ProtocolTable model.Value (signature model.toCarriers) :=
  let helpers := payload.definitions.foldl
    (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩
  payload.protocols.foldl
    (fun captured definition => extendProtocolTableOn model (.silent _) actions
      helpers captured definition iterations) []

def participant (model : DomainModel) (program : Program) (self : Nat)
    (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    PIR.Process (signature model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs) :=
  invokeProtocol (table model program.payload) program.payload.entry.signature {} self inputs

theorem table_erase (model : DomainModel) (payload : UnitPayload) :
    ProtocolTable.Interprets erase (table model payload) (payload.plainProtocolTableOn model) :=
  ProtocolTable.foldOn_interpret erase (SiteObservations.silent_interpret _) actions_erase
    (Evaluation.ComponentTablesOn.fold_interpret erase (SiteObservations.silent_interpret _)
      (.empty _) payload.definitions) (.empty _) iterations_erase payload.protocols

/-- The source occurrence view does not assume honesty, success, valid indices,
or matching peer inputs. Every provider response remains universally quantified. -/
theorem participant_erase (model : DomainModel) (program : Program) (self : Nat)
    (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    (participant model program self inputs).interpret erase = program.participantOn model self inputs := by
  rw [Program.participantOn_eq_plain]
  exact table_erase model program.payload program.payload.entry.signature {} self inputs

end Zkc.Source.Structured.Occurrence
