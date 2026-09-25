import Zkc.Compiler.Role.Simulation.Transfer

/-! Source-cut prefix theorem at the actual stored-role entry. The joint input
is explicit; reply coupling is required only at executed primitive boundaries.
All source/table alignment premises are discharged by definitions_aligned. -/
set_option autoImplicit false
namespace Zkc.Compiler.Role.Simulation
open Zkc.Source Zkc.Source.Protocol
open Zkc.Source.LocatedExecution (Frame)
open Driver

variable {Party Entry Binding Schema : Type} [DecidableEq Party]
  {language : Language} {locals : List (DefinitionSignature language.Ty)}
  {scope : List (Signature Party language.Ty)} {Value : language.Ty → Type}
  {S E : Type}

/-- The main successful-prefix connection. `services` may depend on the selected
source cut (e.g. actual coupled ingress), but receives only this role's request
and state. Its primitive replies must match the actual joint prefix. -/
theorem stored_prefix_simulation (self : Party)
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (inputs : Values (PortValue Value) signature.arguments)
    (state : S) (events : List E)
    (services : Services
      (Protocol.interface Party Entry Binding Schema language locals Value)
      (Protocol.Role.interface Party Entry Binding Schema language locals Value) S E)
    (cuts : List (Cut (Protocol.interface Party Entry Binding Schema language locals Value)))
    (tail : PIR.Proc (Protocol.interface Party Entry Binding Schema language locals Value)
      (Values (PortValue Value) signature.results))
    (reached : SourcePrefix (definitions.denote ref entry binding path inputs) cuts tail)
    (coupled : Coupled (sourceView self) services cuts
      ⟨(projectDefinitions self definitions).denote ref entry binding path (focusValues self inputs),
        state, events⟩) :
    let initial : Cursor _ S E _ :=
      ⟨(projectDefinitions self definitions).denote ref entry binding path (focusValues self inputs),
        state, events⟩
    Aligned (sourceView self) (focusValues self) tail
        (Driver.drive (sourceView self) services cuts initial).program ∧
      OpenPrefix initial (Driver.drive (sourceView self) services cuts initial) :=
  prefix_simulation (sourceView self) (focusValues self) services reached _
    (definitions_aligned self definitions ref entry binding path inputs) coupled

/-- The schedule is derived from actual joint execution. Only primitive reply
coupling remains; neither source alignment nor a desired whole-run theorem is
supplied by the caller. Use the maintained runtime.handler as jointHandler. -/
theorem stored_trace_simulation {T F : Type} (self : Party)
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (inputs : Values (PortValue Value) signature.arguments)
    (jointHandler : PIR.Handler (Protocol.interface Party Entry Binding Schema language locals Value) T F)
    (jointState : T) (state : S) (events : List E)
    (services : Services
      (Protocol.interface Party Entry Binding Schema language locals Value)
      (Protocol.Role.interface Party Entry Binding Schema language locals Value) S E) :
    let trace := successfulTrace jointHandler (definitions.denote ref entry binding path inputs) jointState
    let initial : Cursor _ S E _ :=
      ⟨(projectDefinitions self definitions).denote ref entry binding path (focusValues self inputs),
        state, events⟩
    Coupled (sourceView self) services trace.1 initial →
      Aligned (sourceView self) (focusValues self) trace.2
        (Driver.drive (sourceView self) services trace.1 initial).program ∧
      OpenPrefix initial (Driver.drive (sourceView self) services trace.1 initial) := by
  dsimp only
  intro coupled
  exact stored_prefix_simulation self definitions ref entry binding path inputs state events services
    _ _ (successfulTrace_source jointHandler _ jointState) coupled

/-- The source local-action cut never steps any foreign role, even when that
foreign role is already at a later local action, receive, return or stop. -/
theorem foreign_local_cursor_unchanged (self : Party)
    (origin : LocatedExecution.Origin Party Entry Binding) (different : origin.role ≠ self)
    {signature : DefinitionSignature language.Ty} (callee : Var locals signature)
    (args : Values Value signature.arguments) {A : Type}
    (handler : PIR.Handler (Protocol.Role.interface Party Entry Binding Schema language locals Value) S E)
    (cursor : Cursor (Protocol.Role.interface Party Entry Binding Schema language locals Value) S E A) :
    select (sourceView self) (.local origin callee args) handler cursor = cursor := by
  simp only [select, sourceView, different, if_false]

/-- At a message cut the actual independent sender and receiver heads match the
same source location/schema and supplied sender value. Every returned receive
value continues the joint tree with both open continuations aligned. -/
theorem message_heads {A B C : Type}
    (origin : LocatedExecution.Origin Party Entry Binding) (schema : Schema)
    (receiver : Party) (different : origin.role ≠ receiver) {ty : language.Ty} (value : Value ty)
    (next : Value ty → PIR.Proc (Protocol.interface Party Entry Binding Schema language locals Value) A)
    (senderResult : A → B) (receiverResult : A → C)
    (sender : PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) B)
    (recipient : PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) C)
    (sendAligned : Aligned (sourceView origin.role) senderResult
      (.call (.message origin schema receiver different value) next) sender)
    (receiveAligned : Aligned (sourceView receiver) receiverResult
      (.call (.message origin schema receiver different value) next) recipient) :
    ∃ sendNext receiveNext,
      sender = .call (.send (location origin) schema receiver value) sendNext ∧
      recipient = .call (.receive ty (location origin) schema origin.role) receiveNext ∧
      (∀ received, Aligned (sourceView origin.role) senderResult (next received) (sendNext ())) ∧
      (∀ received, Aligned (sourceView receiver) receiverResult (next received) (receiveNext received)) := by
  simp only [Aligned, sourceView, if_true] at sendAligned
  simp only [Aligned, sourceView, different, if_false, if_true] at receiveAligned
  obtain ⟨sendNext, hs, sendAligned⟩ := sendAligned
  obtain ⟨receiveNext, hr, receiveAligned⟩ := receiveAligned
  exact ⟨sendNext, receiveNext, hs, hr, sendAligned, receiveAligned⟩

/-- Source-derived endpoint heads plus the actual packet-producing runtime give
one successful message step of the two independent continuations. Send failure
and receive failure retain the states established by messageExchange_joint and
the distinct cursor shapes of exchange_send_stopped/exchange_receive_stopped. -/
theorem message_cut_simulation {A B C : Type} {State Event : Party → Type}
    (runtime : Protocol.Runtime Party Entry Binding Schema language Value State Event)
    (origin : LocatedExecution.Origin Party Entry Binding) (schema : Schema)
    (receiver : Party) (different : origin.role ≠ receiver) {ty : language.Ty} (value : Value ty)
    (next : Value ty → PIR.Proc (Protocol.interface Party Entry Binding Schema language locals Value) A)
    (senderResult : A → B) (receiverResult : A → C)
    (sender : PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) B)
    (recipient : PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) C)
    (sendAligned : Aligned (sourceView origin.role) senderResult
      (.call (.message origin schema receiver different value) next) sender)
    (receiveAligned : Aligned (sourceView receiver) receiverResult
      (.call (.message origin schema receiver different value) next) recipient)
    (states : LocatedExecution.States State)
    (es : List (Event origin.role)) (fs : List (Event receiver)) :
    ∃ sendNext receiveNext,
      sender = .call (.send (location origin) schema receiver value) sendNext ∧
      recipient = .call (.receive ty (location origin) schema origin.role) receiveNext ∧
      let driven := messageExchange runtime origin schema receiver value sendNext receiveNext states es fs
      let joint := runtime.message origin schema receiver value states
      driven.outcome = joint.outcome ∧
      driven.sender.state = joint.state.locals origin.role ∧
      driven.receiver.state = joint.state.locals receiver ∧
      ∀ received, driven.outcome = .returned received →
        Aligned (sourceView origin.role) senderResult (next received) driven.sender.program ∧
        Aligned (sourceView receiver) receiverResult (next received) driven.receiver.program := by
  obtain ⟨sendNext, receiveNext, hs, hr, sendTail, receiveTail⟩ :=
    message_heads origin schema receiver different value next senderResult receiverResult
      sender recipient sendAligned receiveAligned
  refine ⟨sendNext, receiveNext, hs, hr, ?_⟩
  obtain ⟨outcome, senderState, receiverState⟩ :=
    messageExchange_joint runtime origin schema receiver (Ne.symm different) value
      sendNext receiveNext states es fs
  refine ⟨outcome, senderState, receiverState, ?_⟩
  intro received success
  dsimp only [messageExchange] at success ⊢
  cases hsend : runtime.send origin schema receiver value (states origin.role) with
  | mk out sent emitted =>
      cases out with
      | stopped reason => simp only [Driver.exchange, hsend] at success; cases success
      | returned packet =>
          cases hreceive : runtime.receive {origin with role := receiver} schema origin.role packet
              (states receiver) with
          | mk out final emittedR =>
              cases out with
              | stopped reason =>
                  simp only [Driver.exchange, hsend, hreceive] at success
                  cases success
              | returned reply =>
                  simp only [Driver.exchange, hsend, hreceive, PIR.Outcome.returned.injEq] at success
                  subst reply
                  simpa only [Driver.exchange, hsend, hreceive] using
                    And.intro (sendTail received) (receiveTail received)

/-- An actual stored local body steps its independent owner cursor at the source
cut. No assumption of totality or rolled-back failure state is made. Together
with foreign_local_cursor_unchanged this gives the local joint/open step. -/
theorem local_cut_simulation {A B : Type} {State Event : Party → Type}
    (runtime : Protocol.Runtime Party Entry Binding Schema language Value State Event)
    (localDefinitions : Source.Definitions language locals)
    (origin : LocatedExecution.Origin Party Entry Binding)
    {signature : DefinitionSignature language.Ty} (callee : Var locals signature)
    (args : Values Value signature.arguments)
    (next : Value signature.result →
      PIR.Proc (Protocol.interface Party Entry Binding Schema language locals Value) A)
    (resultView : A → B)
    (owner : PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) B)
    (aligned : Aligned (sourceView origin.role) resultView (.call (.local origin callee args) next) owner)
    (states : LocatedExecution.States State) (events : List (Event origin.role)) :
    ∃ ownerNext,
      owner = .call (.local (location origin) callee args) ownerNext ∧
      let implementation := runtime.implementations origin.instanceId origin.role
      let actual := (localDefinitions.operation implementation.meaning (.call callee) args).run
        implementation.handler (states origin.role)
      let driven := Driver.accept ownerNext actual events
      let joint := runtime.handler localDefinitions (.local origin callee args) ⟨states, none⟩
      actual.outcome = joint.outcome ∧
      driven.state = joint.state.locals origin.role ∧
      driven.events = events ++ actual.events ∧
      (∀ value, actual.outcome = .returned value →
        Aligned (sourceView origin.role) resultView (next value) driven.program) ∧
      (∀ reason, actual.outcome = .stopped reason → driven.program = .halt reason) := by
  simp only [Aligned, sourceView, if_true] at aligned
  obtain ⟨ownerNext, head, tails⟩ := aligned
  refine ⟨ownerNext, head, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [Driver.accept, Protocol.Runtime.handler, LocatedExecution.run,
      LocatedExecution.lift, LocatedExecution.update_self]
  · intro value success
    simpa only [Driver.accept, success, id_eq] using tails value
  · intro reason stopped
    simp only [Driver.accept, stopped]

end Zkc.Compiler.Role.Simulation
