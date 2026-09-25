import Zkc.Compiler.Participant.Projection
import Zkc.Source.Protocol.Execution

/-! A scheduled target executor and exact common-source correspondence.

The target handler executes local/send/receive primitives directly. It does not
read common-source bodies or invoke the common-source interpreter. The theorem
compares complete results, including every role's state, events and stop origin.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Participant

open Zkc.Source Zkc.Source.Protocol Zkc.Source.LocatedExecution

variable {Role Entry Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {Value : language.Ty → Type}
  {State Event : Role → Type}

def handler [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    (localDefinitions : Source.Definitions language locals) :
    PIR.Handler (interface Role Entry Binding Schema language locals Value runtime.Packet)
      (StateWithOrigin Role Entry Binding State) (LocatedEvent Role Entry Binding Event)
  | .local origin callee args, state =>
      let implementation := runtime.implementations origin.instanceId origin.role
      LocatedExecution.run origin implementation.meaning localDefinitions callee args
        implementation.handler state.locals
  | .send origin schema receiver value, state =>
      lift origin state.locals
        (runtime.send origin schema receiver value (state.locals origin.role))
  | .receive origin schema sender packet, state =>
      lift origin state.locals
        (runtime.receive origin schema sender packet (state.locals origin.role))
  | .stop origin reason, state => ⟨.stopped reason, ⟨state.locals, some origin⟩, []⟩

theorem handler_expand [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    (localDefinitions : Source.Definitions language locals)
    (op : (Protocol.interface Role Entry Binding Schema language locals Value).Op)
    (state : StateWithOrigin Role Entry Binding State) :
    (expand op).run (handler runtime localDefinitions) state =
      runtime.handler localDefinitions op state := by
  cases op <;>
    simp only [expand, PIR.Proc.run, handler, PIR.Execution.follow_return,
      Protocol.Runtime.handler, Protocol.Runtime.message]

/-- Execute an actual scheduled target table, with separately supplied participant inputs. -/
def run [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    (localDefinitions : Source.Definitions language locals)
    {scope : List (Signature Role language.Ty)}
    (definitions : Definitions Nat Role Binding Schema language locals scope)
    {signature : Signature Role language.Ty}
    (selected : Instance Role Binding language.Ty scope signature) (entry : Entry)
    (inputs : Environments Value signature.arguments) (states : States State) :
    PIR.Execution (StateWithOrigin Role Entry Binding State)
      (LocatedEvent Role Entry Binding Event) (Values (PortValue Value) signature.results) :=
  (definitions.denote selected.callee entry selected.binding [] inputs).run
    (handler runtime localDefinitions) ⟨states, none⟩

/-- All common-source constructors and actual shared callees preserve complete execution. -/
theorem run_project [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    (localDefinitions : Source.Definitions language locals)
    {scope : List (Signature Role language.Ty)}
    (definitions : Protocol.Definitions Nat Role Binding Schema language locals scope)
    {signature : Signature Role language.Ty}
    (selected : Instance Role Binding language.Ty scope signature) (entry : Entry)
    (args : Values (PortValue Value) signature.arguments) (states : States State) :
    run runtime localDefinitions (projectDefinitions definitions) selected entry
      (separate args.get) states =
        runtime.run localDefinitions definitions selected entry args states := by
  unfold run Protocol.Runtime.run
  rw [denote_projectDefinitions, PIR.Proc.run_interpret]
  have same : (fun op state => (expand op).run (handler runtime localDefinitions) state) =
      runtime.handler localDefinitions := by
    funext op state
    exact handler_expand runtime localDefinitions op state
  rw [same]

end Zkc.Compiler.Participant
