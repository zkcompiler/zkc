import Zkc.Compiler.Role.Driver

/-! One coupled message cut on two independent pending requests. A successful
send produces the actual packet passed to reception. Failure retains each
endpoint's actual state and continuation, without transferring terminal reasons.
The generic exchange is instantiated on the maintained typed source interface. -/
set_option autoImplicit false
namespace Zkc.Compiler.Role.Driver

variable {I J : PIR.Signature} {S T E F A B Packet : Type}

structure ExchangeResult (I J : PIR.Signature) (S T E F A B V : Type) where
  outcome : PIR.Outcome V
  sender : Cursor I S E A
  receiver : Cursor J T F B

/-- The caller has inspected the two pending heads. Only `send` receives sender
state; only `receive` receives receiver state and the produced packet. -/
def exchange (sendOp : I.Op) (ack : I.Reply sendOp) (receiveOp : J.Op)
    (send : S → PIR.Execution S E Packet)
    (receive : Packet → T → PIR.Execution T F (J.Reply receiveOp))
    (sendNext : I.Reply sendOp → PIR.Proc I A)
    (receiveNext : J.Reply receiveOp → PIR.Proc J B)
    (s : S) (t : T) (es : List E) (fs : List F) :
    ExchangeResult I J S T E F A B (J.Reply receiveOp) :=
  let sent := send s
  match sent.outcome with
  | .stopped reason =>
      ⟨.stopped reason, ⟨.halt reason, sent.state, es ++ sent.events⟩,
        ⟨.call receiveOp receiveNext, t, fs⟩⟩
  | .returned packet =>
      let received := receive packet t
      ⟨received.outcome, ⟨sendNext ack, sent.state, es ++ sent.events⟩,
        ⟨match received.outcome with
          | .returned value => receiveNext value
          | .stopped reason => .halt reason,
          received.state, fs ++ received.events⟩⟩

/-- A failed send never evaluates the receive service or changes its cursor. -/
theorem exchange_send_stopped (sendOp : I.Op) (ack : I.Reply sendOp) (receiveOp : J.Op)
    (send : S → PIR.Execution S E Packet)
    (receive : Packet → T → PIR.Execution T F (J.Reply receiveOp))
    (sendNext : I.Reply sendOp → PIR.Proc I A)
    (receiveNext : J.Reply receiveOp → PIR.Proc J B)
    (s : S) (t : T) (es : List E) (fs : List F)
    (reason : PIR.Stop) (final : S) (emitted : List E)
    (stopped : send s = ⟨.stopped reason, final, emitted⟩) :
    exchange sendOp ack receiveOp send receive sendNext receiveNext s t es fs =
      ⟨.stopped reason, ⟨.halt reason, final, es ++ emitted⟩,
        ⟨.call receiveOp receiveNext, t, fs⟩⟩ := by simp only [exchange, stopped]

/-- A failed receive leaves the successful sender's next action ready to run. -/
theorem exchange_receive_stopped (sendOp : I.Op) (ack : I.Reply sendOp) (receiveOp : J.Op)
    (send : S → PIR.Execution S E Packet)
    (receive : Packet → T → PIR.Execution T F (J.Reply receiveOp))
    (sendNext : I.Reply sendOp → PIR.Proc I A)
    (receiveNext : J.Reply receiveOp → PIR.Proc J B)
    (s finalS : S) (t finalT : T) (es emittedS : List E) (fs emittedT : List F)
    (packet : Packet) (reason : PIR.Stop)
    (sent : send s = ⟨.returned packet, finalS, emittedS⟩)
    (stopped : receive packet t = ⟨.stopped reason, finalT, emittedT⟩) :
    exchange sendOp ack receiveOp send receive sendNext receiveNext s t es fs =
      ⟨.stopped reason, ⟨sendNext ack, finalS, es ++ emittedS⟩,
        ⟨.halt reason, finalT, fs ++ emittedT⟩⟩ := by simp only [exchange, sent, stopped]

end Zkc.Compiler.Role.Driver

namespace Zkc.Compiler.Role.Simulation
open Zkc.Source Zkc.Source.Protocol Zkc.Source.LocatedExecution

variable {Party Entry Binding Schema : Type} [DecidableEq Party]
  {language : Language} {locals : List (DefinitionSignature language.Ty)}
  {Value : language.Ty → Type} {State Event : Party → Type} {A B : Type}

/-- Concrete instantiation: the retained sender request contains the transmitted
value, and the receiver request contains no sender operand. -/
def messageExchange
    (runtime : Protocol.Runtime Party Entry Binding Schema language Value State Event)
    {ty : language.Ty} (origin : Origin Party Entry Binding) (schema : Schema)
    (receiver : Party) (value : Value ty)
    (sendNext : Unit → PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) A)
    (receiveNext : Value ty → PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) B)
    (states : States State) (es : List (Event origin.role)) (fs : List (Event receiver)) :=
  Driver.exchange
    (I := Protocol.Role.interface Party Entry Binding Schema language locals Value)
    (J := Protocol.Role.interface Party Entry Binding Schema language locals Value)
    (.send (location origin) schema receiver value) ()
    (.receive ty (location origin) schema origin.role)
    (runtime.send origin schema receiver value)
    (runtime.receive {origin with role := receiver} schema origin.role)
    sendNext receiveNext (states origin.role) (states receiver) es fs

/-- Complete message outcome and both actual residual states agree with the
maintained joint runtime. This includes failed-send and failed-receive effects.
It does not equate the two endpoint outcomes. -/
theorem messageExchange_joint
    (runtime : Protocol.Runtime Party Entry Binding Schema language Value State Event)
    {ty : language.Ty} (origin : Origin Party Entry Binding) (schema : Schema)
    (receiver : Party) (different : receiver ≠ origin.role) (value : Value ty)
    (sendNext : Unit → PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) A)
    (receiveNext : Value ty → PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) B)
    (states : States State) (es : List (Event origin.role)) (fs : List (Event receiver)) :
    let driven := messageExchange runtime origin schema receiver value sendNext receiveNext states es fs
    let joint := runtime.message origin schema receiver value states
    driven.outcome = joint.outcome ∧
      driven.sender.state = joint.state.locals origin.role ∧
      driven.receiver.state = joint.state.locals receiver := by
  dsimp only [messageExchange]
  cases hs : runtime.send origin schema receiver value (states origin.role) with
  | mk outcome sent emitted =>
      cases outcome with
      | stopped reason =>
          simp only [Driver.exchange, hs, Runtime.message, lift, PIR.Execution.follow,
            update_self, update_other _ _ _ _ different, and_self]
      | returned packet =>
          cases hr : runtime.receive {origin with role := receiver} schema origin.role packet
              (states receiver) with
          | mk outcome received emittedR =>
              cases outcome <;>
                simp only [Driver.exchange, hs, hr, Runtime.message, lift, PIR.Execution.follow,
                  update_self, update_other _ _ _ _ different,
                  update_other _ _ _ _ (Ne.symm different), and_self]

/-- At a fresh message boundary, concatenating the tagged endpoint emissions
recovers the complete joint event list, in send-before-receive order. -/
theorem messageExchange_events
    (runtime : Protocol.Runtime Party Entry Binding Schema language Value State Event)
    {ty : language.Ty} (origin : Origin Party Entry Binding) (schema : Schema)
    (receiver : Party) (different : receiver ≠ origin.role) (value : Value ty)
    (sendNext : Unit → PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) A)
    (receiveNext : Value ty → PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value) B)
    (states : States State) :
    let driven := messageExchange runtime origin schema receiver value sendNext receiveNext states [] []
    (runtime.message origin schema receiver value states).events =
      driven.sender.events.map (fun event => LocatedEvent.mk origin event) ++
      driven.receiver.events.map (fun event => LocatedEvent.mk {origin with role := receiver} event) := by
  dsimp only [messageExchange]
  cases hs : runtime.send origin schema receiver value (states origin.role) with
  | mk outcome sent emitted =>
      cases outcome with
      | stopped reason =>
          simp only [Driver.exchange, hs, Runtime.message, lift, PIR.Execution.follow,
            List.nil_append, List.map_nil, List.append_nil]
      | returned packet =>
          cases hr : runtime.receive {origin with role := receiver} schema origin.role packet
              (states receiver) with
          | mk outcome received emittedR =>
              cases outcome <;>
                simp only [Driver.exchange, hs, hr, Runtime.message, lift, PIR.Execution.follow,
                  update_other _ _ _ _ different, List.nil_append]

end Zkc.Compiler.Role.Simulation
