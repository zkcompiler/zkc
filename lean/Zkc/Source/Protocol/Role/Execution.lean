import Zkc.Source.Protocol.Role.Interface
import Zkc.Source.Protocol.Execution

/-! One role's actual local library and external services.
The runtime has one state type and no family of other roles' states. A selected
binding chooses an implementation of primitives; local calls resolve stored
Source.Definitions, including their branches, nested calls and private stops.
-/

set_option autoImplicit false

namespace Zkc.Source.Protocol.Role

structure State (Entry Binding S : Type) where
  localState : S
  stoppedAt : Option (Location Entry Binding)
  deriving Repr

structure Event (Entry Binding E : Type) where
  location : Location Entry Binding
  value : E
  deriving DecidableEq, Repr

structure Runtime (Party Entry Binding Schema : Type) (language : Language)
    (Value : language.Ty → Type) (S E : Type) where
  implementations : Binding → LocalImplementation language Value S E
  send : {ty : language.Ty} → Location Entry Binding → Schema → Party → Value ty →
    S → PIR.Execution S E Unit
  receive : (ty : language.Ty) → Location Entry Binding → Schema → Party →
    S → PIR.Execution S E (Value ty)

variable {Party Entry Binding Schema : Type} {language : Language}
  {Value : language.Ty → Type} {S E A : Type}

def lift (location : Location Entry Binding) (result : PIR.Execution S E A) :
    PIR.Execution (State Entry Binding S) (Event Entry Binding E) A :=
  ⟨result.outcome, ⟨result.state,
    match result.outcome with
    | .returned _ => none
    | .stopped _ => some location⟩,
    result.events.map fun value => ⟨location, value⟩⟩

/-- A completed incoming strategy need not describe an honest sender or joint run. -/
def Runtime.handler (runtime : Runtime Party Entry Binding Schema language Value S E)
    {locals : List (DefinitionSignature language.Ty)}
    (definitions : Source.Definitions language locals) :
    PIR.Handler (interface Party Entry Binding Schema language locals Value)
      (State Entry Binding S) (Event Entry Binding E)
  | .local location callee args, state =>
      let implementation := runtime.implementations location.binding
      lift location ((definitions.operation implementation.meaning (.call callee) args).run
        implementation.handler state.localState)
  | .send location schema receiver value, state =>
      lift location (runtime.send location schema receiver value state.localState)
  | .receive ty location schema sender, state =>
      lift location (runtime.receive ty location schema sender state.localState)
  | .stop location reason, state =>
      ⟨.stopped reason, ⟨state.localState, some location⟩, []⟩

/-- `none` means no message is available. It supplies no reply, effects or rejection.
A decoded hostile value or an actual codec failure can instead return `some`.
-/
abbrev Ingress (Party Entry Binding Schema : Type) (language : Language)
    (Value : language.Ty → Type) (S E : Type) :=
  (ty : language.Ty) → Location Entry Binding → Schema → Party →
    S → Option (PIR.Execution S E (Value ty))

def Runtime.poll (runtime : Runtime Party Entry Binding Schema language Value S E)
    {locals : List (DefinitionSignature language.Ty)}
    (definitions : Source.Definitions language locals)
    (ingress : Ingress Party Entry Binding Schema language Value S E)
    (op : (interface Party Entry Binding Schema language locals Value).Op)
    (state : State Entry Binding S) :
    Option (PIR.Execution (State Entry Binding S) (Event Entry Binding E)
      ((interface Party Entry Binding Schema language locals Value).Reply op)) :=
  match op with
  | .receive ty location schema sender =>
      (ingress ty location schema sender state.localState).map (lift location)
  | .local location callee args =>
      some (runtime.handler definitions (.local location callee args) state)
  | .send location schema receiver value =>
      some (runtime.handler definitions (.send location schema receiver value) state)
  | .stop location reason => some (runtime.handler definitions (.stop location reason) state)

/-- Completed ingress connects polling to the finite reference handler. -/
theorem Runtime.poll_complete
    (runtime : Runtime Party Entry Binding Schema language Value S E)
    {locals : List (DefinitionSignature language.Ty)}
    (definitions : Source.Definitions language locals)
    (op : (interface Party Entry Binding Schema language locals Value).Op)
    (state : State Entry Binding S) :
    runtime.poll definitions (fun ty location schema sender state =>
      some (runtime.receive ty location schema sender state)) op state =
        some (runtime.handler definitions op state) := by
  cases op <;> rfl

/-- Only ingress can suspend this adapter, never an owned local stop or service failure. -/
theorem Runtime.poll_none_receive
    (runtime : Runtime Party Entry Binding Schema language Value S E)
    {locals : List (DefinitionSignature language.Ty)}
    (definitions : Source.Definitions language locals)
    (ingress : Ingress Party Entry Binding Schema language Value S E)
    (op : (interface Party Entry Binding Schema language locals Value).Op)
    (state : State Entry Binding S) (missing : runtime.poll definitions ingress op state = none) :
    ∃ ty location schema sender, op = .receive ty location schema sender := by
  cases op with
  | receive ty location schema sender => exact ⟨ty, location, schema, sender, rfl⟩
  | «local» | send | stop => simp [Runtime.poll] at missing

end Zkc.Source.Protocol.Role
