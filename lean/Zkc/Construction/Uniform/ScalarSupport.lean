module

public import Zkc.Construction.ConnectionRouting
public import Zkc.Construction.ScalarVerifier

@[expose] public section

/-! Structural support for the retained scalar observation. This judgment reads
only source effects, never artifact instructions or routing templates. Nominal
field and group identifiers remain in the operations and their typed replies.
Private service handling remains a separate routing-scope obligation. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.ScalarSupport
open Zkc.Source Zkc.Source.Structured
variable {F G A B : Type}

inductive Message : Ty → Prop where
  | boolean : Message .boolean
  | field (name : String) : Message (.field name)
  | group (name : String) : Message (.group name)

def Action : (participantInterface F G).Op → Prop
  | .receive ty _ _ => Message ty
  | @Participant.Action.send _ _ _ _ ty _ _ _ => Message ty
  | .query _ _ _ => True

/-- All continuations are checked, including replies never produced honestly.
Iteration support is selected from the actual artifact before this evidence. -/
inductive Supported (iterations : Bool) :
    PIR.Process (Occurrence.signature (uniformCarriers F G)) A → Prop where
  | done (value : A) : Supported iterations (.done value)
  | halt (reason : PIR.Stop) : Supported iterations (.halt reason)
  | enter (frame : Occurrence.Frame)
      {next : Unit → PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (allowed : iterations = true) (tail : Supported iterations (next ())) :
      Supported iterations (.call (.enter frame) next)
  | leave (frame : Occurrence.Frame)
      {next : Unit → PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (tail : Supported iterations (next ())) :
      Supported iterations (.call (.leave frame) next)
  | action (operation : (participantInterface F G).Op)
      {next : (participantInterface F G).Reply operation →
        PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (allowed : Action operation) (tail : ∀ reply, Supported iterations (next reply)) :
      Supported iterations (.call (.action operation) next)

/-- The fragment excludes collection and capability messages semantically;
failure of a proof search is never interpreted as a refusal theorem. -/
theorem index_not_message : ¬ Message .index := by intro h; cases h

theorem service_not_message (contract : String) : ¬ Message (.service contract) := by
  intro h; cases h

end Zkc.Construction.Uniform.ScalarSupport
