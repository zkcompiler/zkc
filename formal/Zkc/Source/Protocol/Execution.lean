import Zkc.Source.Protocol.Meaning

/-! Execute common source with separate participant states and message endpoints.

The runtime supplies local primitive implementations, not protocol-body callbacks.
Send and receive have independent outcomes. Each sees only its own role's state;
the joint driver retains both effects when reception fails after a successful send.
Admission and cryptographic service contracts remain additional obligations.
-/

set_option autoImplicit false

namespace Zkc.Source.Protocol

open LocatedExecution

/-- One selected interpretation with a fixed domain-value family. -/
structure LocalImplementation (language : Language) (Value : language.Ty → Type)
    (State Event : Type) where
  effects : PIR.Signature
  condition : Value language.condition → Bool
  operation : (op : language.Op) → Values Value (language.arguments op) →
    PIR.Proc effects (Value (language.result op))
  handler : PIR.Handler effects State Event

abbrev LocalImplementation.meaning {language : Language} {Value : language.Ty → Type}
    {S E : Type} (implementation : LocalImplementation language Value S E) :
    Interpretation language implementation.effects where
  Value := Value
  condition := implementation.condition
  operation := implementation.operation

structure Runtime (Role Entry Binding Schema : Type) (language : Language)
    (Value : language.Ty → Type) (State Event : Role → Type) where
  implementations : Binding → (role : Role) →
    LocalImplementation language Value (State role) (Event role)
  Packet : language.Ty → Type
  send : {ty : language.Ty} → (origin : Origin Role Entry Binding) → Schema → Role →
    Value ty → State origin.role → PIR.Execution (State origin.role) (Event origin.role) (Packet ty)
  receive : {ty : language.Ty} → (origin : Origin Role Entry Binding) → Schema → Role →
    Packet ty → State origin.role → PIR.Execution (State origin.role) (Event origin.role) (Value ty)

variable {Role Entry Binding Schema : Type} {language : Language}
  {Value : language.Ty → Type} {State Event : Role → Type}

/-- Reception binds its actual returned value, after the actual sender post-state. -/
def Runtime.message [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    {ty : language.Ty} (origin : Origin Role Entry Binding) (schema : Schema)
    (receiver : Role) (value : Value ty) (states : States State) :
    PIR.Execution (StateWithOrigin Role Entry Binding State)
      (LocatedEvent Role Entry Binding Event) (Value ty) :=
  (lift origin states (runtime.send origin schema receiver value (states origin.role))).follow
    fun packet sent =>
      lift { origin with role := receiver } sent.locals
        (runtime.receive { origin with role := receiver } schema origin.role packet
          (sent.locals receiver))

def Runtime.handler [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    {locals : List (DefinitionSignature language.Ty)}
    (definitions : Source.Definitions language locals) :
    PIR.Handler (interface Role Entry Binding Schema language locals Value)
      (StateWithOrigin Role Entry Binding State) (LocatedEvent Role Entry Binding Event)
  | .local origin callee args, state =>
      let implementation := runtime.implementations origin.instanceId origin.role
      LocatedExecution.run origin implementation.meaning definitions callee args
        implementation.handler state.locals
  | .message origin schema receiver _ value, state =>
      runtime.message origin schema receiver value state.locals
  | .stop origin reason, state =>
      ⟨.stopped reason, ⟨state.locals, some origin⟩, []⟩

/-- Start a selected stored protocol at the root path, with explicit ordered input ports. -/
def Runtime.run [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    {locals : List (DefinitionSignature language.Ty)}
    (localDefinitions : Source.Definitions language locals)
    {scope : List (Signature Role language.Ty)}
    (protocols : Definitions Nat Role Binding Schema language locals scope)
    {signature : Signature Role language.Ty}
    (selected : Instance Role Binding language.Ty scope signature) (entry : Entry)
    (args : Values (PortValue Value) signature.arguments) (states : States State) :
    PIR.Execution (StateWithOrigin Role Entry Binding State)
      (LocatedEvent Role Entry Binding Event) (Values (PortValue Value) signature.results) :=
  (protocols.denote selected.callee entry selected.binding [] args).run
    (runtime.handler localDefinitions) ⟨states, none⟩

/-- A failed send never invokes reception, and retains the sender's actual effects. -/
theorem Runtime.message_send_stopped [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    {ty : language.Ty} (origin : Origin Role Entry Binding) (schema : Schema)
    (receiver : Role) (value : Value ty) (states : States State)
    (reason : PIR.Stop) (final : State origin.role) (events : List (Event origin.role))
    (stopped : runtime.send origin schema receiver value (states origin.role) =
      ⟨.stopped reason, final, events⟩) :
    runtime.message origin schema receiver value states =
      ⟨.stopped reason, ⟨update states origin.role final, some origin⟩,
        events.map fun event => ⟨origin, event⟩⟩ := by
  simp only [message, stopped, lift, PIR.Execution.follow]

/-- Failed reception retains successful-send effects, without rewriting peer outcomes. -/
theorem Runtime.message_receive_stopped [DecidableEq Role]
    (runtime : Runtime Role Entry Binding Schema language Value State Event)
    {ty : language.Ty} (origin : Origin Role Entry Binding) (schema : Schema)
    (receiver : Role) (different : receiver ≠ origin.role)
    (value : Value ty) (states : States State)
    (packet : runtime.Packet ty) (sentState : State origin.role)
    (sentEvents : List (Event origin.role))
    (sent : runtime.send origin schema receiver value (states origin.role) =
      ⟨.returned packet, sentState, sentEvents⟩)
    (reason : PIR.Stop) (final : State receiver) (events : List (Event receiver))
    (stopped : runtime.receive { origin with role := receiver } schema origin.role packet
      (states receiver) = ⟨.stopped reason, final, events⟩) :
    runtime.message origin schema receiver value states =
      ⟨.stopped reason,
        ⟨update (update states origin.role sentState) receiver final,
          some { origin with role := receiver }⟩,
        sentEvents.map (fun event => ⟨origin, event⟩) ++
          events.map (fun event => ⟨{ origin with role := receiver }, event⟩)⟩ := by
  simp only [message, sent, lift, PIR.Execution.follow, update_other _ _ _ _ different, stopped]

end Zkc.Source.Protocol
