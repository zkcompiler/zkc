import Zkc.Compiler.Role.Simulation

/-! Actual stored source: P:a; V:check; P:b. Check consumes state and fails.
The controller freezes P at a, with b still pending and no peer stop diagnostic.
Also exercise coupled message failure halves and exact prefix granularity. -/
set_option autoImplicit false
namespace Tests.RoleDriver
open Zkc.Source Zkc.Compiler.Role
open Zkc.Compiler.Role.Simulation

abbrev language : Language where
  Ty := Unit
  Op := Nat
  arguments _ := []
  result _ := ()
  condition := ()
abbrev Value (_ : Unit) := Nat
abbrev localSignature : DefinitionSignature Unit := ⟨[], ()⟩

def localDefinitions : Zkc.Source.Definitions language
    [localSignature, localSignature, localSignature] :=
  (((Zkc.Source.Definitions.nil : Zkc.Source.Definitions language []).snoc localSignature
    (.letOp (.primitive 1) .nil (.ret .here))).snoc localSignature
    (.letOp (.primitive 2) .nil (.ret .here))).snoc localSignature
    (.letOp (.primitive 3) .nil (.ret .here))

abbrev signature : Protocol.Signature Bool Unit := ⟨[], []⟩
def source : Protocol.Program Nat Bool Unit Unit language
    [localSignature, localSignature, localSignature] [] [] [] :=
  .localCall 1 true (.there (.there .here)) .nil
    (.localCall 2 false (.there .here) .nil
      (.localCall 3 true .here .nil (.ret .nil)))
def definitions := Protocol.Definitions.snoc (language := language) .nil signature source

abbrev effects : PIR.Signature := ⟨Nat, fun _ => Nat⟩
def implementation : Protocol.LocalImplementation language Value Nat Nat where
  effects := effects
  condition := fun n => n != 0
  operation := fun op _ => .call op .done
  handler op state :=
    if op = 2 then ⟨.stopped .reject, state + 10, [op]⟩
    else ⟨.returned op, state + 1, [op]⟩

def runtime : Protocol.Runtime Bool Unit Unit Unit language Value (fun _ => Nat) (fun _ => Nat) where
  implementations _ _ := implementation
  Packet _ := Nat
  send _ _ _ value state := ⟨.returned value, state + 1, [20]⟩
  receive _ _ _ packet state :=
    if packet = 0 then ⟨.stopped .abort, state + 10, [21]⟩
    else ⟨.returned packet, state + 1, [21]⟩

def roleRuntime : Protocol.Role.Runtime Bool Unit Unit Unit language Value Nat Nat where
  implementations _ := implementation
  send _ _ _ _ state := ⟨.returned (), state + 1, [20]⟩
  receive _ _ _ _ state := ⟨.returned 7, state + 1, [21]⟩

abbrev jointI := Protocol.interface Bool Unit Unit Unit language
  [localSignature, localSignature, localSignature] Value
abbrev roleI := Protocol.Role.interface Bool Unit Unit Unit language
  [localSignature, localSignature, localSignature] Value

def joint := definitions.denote (Value := Value) .here () () [] .nil
def jointHandler := runtime.handler localDefinitions
def localHandler := roleRuntime.handler localDefinitions
def sourceTrace := Driver.successfulTrace jointHandler joint ⟨fun _ => 0, none⟩
def initial (self : Bool) : Cursor roleI (Protocol.Role.State Unit Unit Nat)
    (Protocol.Role.Event Unit Unit Nat) (Protocol.Role.Environment Value self []) :=
  ⟨(projectDefinitions self definitions).denote .here () () [] (focusValues self (Values.nil (Value := Protocol.PortValue Value))),
    ⟨0, none⟩, []⟩
def atFailure (self : Bool) := Driver.drive (sourceView self) (fun _ => localHandler)
  sourceTrace.1 (initial self)
def failedOp : jointI.Op := .local ⟨false, (), (), [], 2⟩ (.there .here) .nil

def afterFailure (self : Bool) := Driver.select (sourceView self) failedOp localHandler (atFailure self)

example : sourceTrace.1.length = 1 := by cbv
example : (joint.run jointHandler ⟨fun _ => 0, none⟩).outcome = .stopped .reject := by cbv
example : (joint.run jointHandler ⟨fun _ => 0, none⟩).state.locals true = 1 := by cbv
example : (joint.run jointHandler ⟨fun _ => 0, none⟩).state.locals false = 10 := by cbv

example : (atFailure true).state.localState = 1 := by cbv
example : (atFailure true).events.map (·.value) = [1] := by cbv
example : afterFailure true = atFailure true := by cbv
example : (afterFailure true).state.stoppedAt = none := by cbv
example : (afterFailure false).state.localState = 10 := by cbv
example : (afterFailure false).events.map (·.value) = [2] := by cbv
example : (afterFailure false).program = .halt .reject := by cbv

/-- P can independently continue to b after the joint controller has stopped. -/
example : (Driver.tick localHandler (afterFailure true)).state.localState = 2 := by cbv
example : (Driver.tick localHandler (afterFailure true)).events.map (·.value) = [1, 3] := by cbv
example : ((initial true).program.run localHandler (initial true).state).outcome =
    .returned Protocol.Role.Environment.empty := by
  cbv
  congr 1
  funext ty ref
  exact nomatch ref

/-- Instantiate the generic prefix theorem on source-derived actual execution,
not a handwritten same-tree equality. No service coupling premise remains. -/
theorem actual_source_prefix (self : Bool) :
    Aligned (sourceView self) (focusValues self) sourceTrace.2 (atFailure self).program ∧
      Driver.OpenPrefix (initial self) (atFailure self) := by
  apply Driver.prefix_simulation (sourceView self) (focusValues self) (fun _ => localHandler)
    (Driver.successfulTrace_source jointHandler joint ⟨fun _ => 0, none⟩)
  · exact definitions_aligned self definitions .here () () [] .nil
  · cases self <;> cbv <;> trivial

/-- Raw source action granularity detects a fused a+b observation. -/
example : [1].isPrefixOf [1, 3] = true := by decide
example : [1].isPrefixOf [13] = false := by decide

/-- Two actual pending message continuations. Reception of zero consumes then
fails; the sender remains ready for the post-send local action. -/
def sendNext (_ : Unit) : PIR.Proc roleI Unit :=
  .call (.local ⟨(), (), [], 3⟩ .here .nil) fun _ => .done ()
def receiveNext (_ : Nat) : PIR.Proc roleI Unit := .done ()
def exchange (value : Nat) := messageExchange runtime (ty := ()) (locals := [localSignature, localSignature, localSignature])
  ⟨true, (), (), [], 4⟩ () false value sendNext receiveNext (fun _ => 0) [] []

example : (exchange 0).outcome = .stopped .abort := by cbv
example : (exchange 0).sender.state = 1 := by cbv
example : (exchange 0).receiver.state = 10 := by cbv
example : (exchange 0).sender.events = [20] := by cbv
example : (exchange 0).receiver.events = [21] := by cbv
example : (exchange 0).sender.program = sendNext () := by cbv
example : (exchange 0).receiver.program = .halt .abort := by cbv
example : (exchange 7).outcome = .returned 7 := by cbv
example : (exchange 7).receiver.program = .done () := by cbv

example : (exchange 0).outcome = (runtime.message (ty := ()) ⟨true, (), (), [], 4⟩ () false 0
    (fun _ => 0)).outcome :=
  (messageExchange_joint runtime (ty := ()) ⟨true, (), (), [], 4⟩ () false (by decide) 0
    sendNext receiveNext (fun _ => 0) [] []).1

/-- A failed send leaves an already pending receiver exactly unchanged. -/
def failedSend : Nat → PIR.Execution Nat Nat Nat := fun state =>
  ⟨.stopped .exhausted, state + 5, [20]⟩
def forbiddenReceive : Nat → Nat → PIR.Execution Nat Nat Nat := fun _ state =>
  ⟨.stopped .refused, state + 1000, [99]⟩
def sendFailure := Driver.exchange
  (I := roleI) (J := roleI) (.send (ty := ()) ⟨(), (), [], 4⟩ () false 9) ()
  (.receive () ⟨(), (), [], 4⟩ () true)
  failedSend forbiddenReceive sendNext receiveNext 0 0 [] []
example : sendFailure.sender.state = 5 := by cbv
example : sendFailure.receiver.state = 0 := by cbv
example : sendFailure.receiver.events = [] := by cbv
example : sendFailure.receiver.program = .call (.receive () ⟨(), (), [], 4⟩ () true) receiveNext := by cbv

/-- Stored protocol calls preserve the source action origin; failure in the
first child prevents a second invocation without making P observe that stop. -/
def nestedDefinitions := definitions.snoc signature
  (.invoke 7 ⟨.here, ()⟩ .nil (.invoke 8 ⟨.here, ()⟩ .nil (.ret .nil)))
def nestedJoint := nestedDefinitions.denote (Value := Value) .here () () [] .nil
example : (Driver.successfulTrace jointHandler nestedJoint ⟨fun _ => 0, none⟩).1.length = 1 := by cbv
example : (nestedJoint.run jointHandler ⟨fun _ => 0, none⟩).events.map (fun e => e.origin.path) =
    [[LocatedExecution.Frame.invocation 7], [LocatedExecution.Frame.invocation 7]] := by cbv

/-- Public zero loops do no work; a failed first iteration does not run its
second iteration, even though P can independently continue its projected loop. -/
def loopDefinitions (count : Nat) := Protocol.Definitions.snoc (language := language) .nil signature
  (Protocol.Program.repeat 10 count .nil source (.ret .nil))
def loopJoint (count : Nat) := (loopDefinitions count).denote (Value := Value) .here () () [] .nil
example : (loopJoint 0 |>.run jointHandler ⟨fun _ => 0, none⟩).events = [] := by cbv
example : (loopJoint 2 |>.run jointHandler ⟨fun _ => 0, none⟩).state.locals true = 1 := by cbv
example : (loopJoint 2 |>.run jointHandler ⟨fun _ => 0, none⟩).events.map (fun e => e.origin.path) =
    [[LocatedExecution.Frame.iteration 10 0], [LocatedExecution.Frame.iteration 10 0]] := by cbv

/-- A foreign syntactic leaf is incomplete, unlike the dynamic foreign check
above, which leaves P's genuine later continuation present. -/
def stopDefinitions := Protocol.Definitions.snoc (Count := Nat) (language := language)
  (Binding := Unit) (Schema := Unit)
  (locals := [localSignature, localSignature, localSignature]) .nil signature
  (Protocol.Program.stop 11 false .abort)
example : ((projectDefinitions true stopDefinitions).denote (Value := Value) .here () () []
    Protocol.Role.Environment.empty) = .halt .incomplete := by cbv

/-- A real stored message is projected before the generic message-cut law is
instantiated. Its zero packet fails reception after successful send. -/
abbrev messageSignature : Protocol.Signature Bool Unit := ⟨[(true, ())], [(false, ())]⟩
def messageDefinitions := Protocol.Definitions.snoc (Count := Nat) (language := language)
  (Binding := Unit) (Schema := Unit) (locals := [localSignature, localSignature, localSignature])
  .nil messageSignature (.message 4 () true false (by decide) .here (.ret (.cons .here .nil)))
def messageInputs : Values (Protocol.PortValue (Role := Bool) Value) [(true, ())] := .cons 0 .nil
def messageRole (self : Bool) := (projectDefinitions self messageDefinitions).denote (Value := Value)
  .here () () [] (focusValues self messageInputs)
def messageNext (value : Nat) : PIR.Proc jointI (Values (Protocol.PortValue Value) [(false, ())]) :=
  .done (.cons value .nil)

example : ∃ sendNext receiveNext,
    messageRole true = .call (.send (ty := ()) ⟨(), (), [], 4⟩ () false 0) sendNext ∧
    messageRole false = .call (.receive () ⟨(), (), [], 4⟩ () true) receiveNext ∧
    (messageExchange runtime (ty := ()) ⟨true, (), (), [], 4⟩ () false 0
      sendNext receiveNext (fun _ => 0) [] []).outcome = .stopped .abort := by
  have sender := definitions_aligned true messageDefinitions (Value := Value)
    .here () () [] messageInputs
  have receiver := definitions_aligned false messageDefinitions (Value := Value)
    .here () () [] messageInputs
  obtain ⟨sendNext, receiveNext, hs, hr, outcome, _⟩ := message_cut_simulation runtime
    ⟨true, (), (), [], 4⟩ () false (by decide) (ty := ()) 0 messageNext
    (@focusValues Bool language Value [(false, ())] true)
    (@focusValues Bool language Value [(false, ())] false)
    (messageRole true) (messageRole false)
    sender receiver (fun _ => 0) [] []
  exact ⟨sendNext, receiveNext, hs, hr, outcome.trans (by cbv)⟩

end Tests.RoleDriver
