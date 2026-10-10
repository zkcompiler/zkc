import Zkc.Source.Protocol.Execution

set_option autoImplicit false

namespace Tests.CommonProtocol

open Zkc.Source
open Zkc.Source.Protocol
open Zkc.Source.LocatedExecution

inductive Role where
  | prover | verifier | auditor
  deriving DecidableEq, Repr

abbrev Value (_ : Unit) := Nat
abbrev State : Role → Type
  | .prover => Nat
  | .verifier => List Nat
  | .auditor => Bool

inductive Kind where
  | compute | send | receive
  deriving DecidableEq, Repr

abbrev Event (_ : Role) := Kind × Nat

def initial : States State
  | .prover => 0
  | .verifier => []
  | .auditor => true

abbrev language : Language where
  Ty := Unit
  Op := Unit
  arguments _ := [()]
  result _ := ()
  condition := ()

abbrev localSignature : DefinitionSignature Unit := ⟨[()], ()⟩
def localDefinitions : Zkc.Source.Definitions language [localSignature] :=
  Zkc.Source.Definitions.snoc (language := language) .nil localSignature
    (.letOp (.primitive ()) (.cons .here .nil) (.ret .here))

abbrev effects : PIR.Signature := ⟨Nat, fun _ => Nat⟩

def localHandler (binding : Nat) : (role : Role) → PIR.Handler effects (State role) (Event role)
  | .prover => fun value cursor =>
      ⟨.returned (value + binding + cursor), cursor + 1, [(.compute, value)]⟩
  | .verifier => fun value seen =>
      ⟨.returned (value + binding), value :: seen, [(.compute, value)]⟩
  | .auditor => fun value enabled =>
      ⟨.returned (value + binding), enabled, [(.compute, value)]⟩

def record (role : Role) (value : Nat) : State role → State role :=
  match role with
  | .prover => fun cursor => cursor + 10
  | .verifier => fun seen => value :: seen
  | .auditor => fun _ => false

def runtime (sendStop receiveStop : Nat → Bool := fun _ => false)
    (received : Nat → Nat := id) : Runtime Role String Nat Unit language Value State Event where
  implementations binding role :=
    { effects := effects
      condition := fun value => value != 0
      operation := fun () (.cons value .nil) => .call value .done
      handler := localHandler binding role }
  Packet _ := Nat
  send origin _ _ value state :=
    ⟨if sendStop value then .stopped .exhausted else .returned value,
      record origin.role value state, [(.send, value)]⟩
  receive origin _ _ packet state :=
    ⟨if receiveStop packet then .stopped .refused else .returned (received packet),
      record origin.role packet state, [(.receive, packet)]⟩

abbrev inputPorts : List (Port Role Unit) := [(.prover, ())]
abbrev resultPorts : List (Port Role Unit) := [(.prover, ()), (.verifier, ())]
abbrev signature : Protocol.Signature Role Unit := ⟨inputPorts, resultPorts⟩

/-- A shared body contains real local syntax and an explicit receive boundary. -/
def child : Protocol.Program Nat Role Nat Unit language [localSignature] [] inputPorts resultPorts :=
  .localCall 0 .prover .here (.cons .here .nil)
    (.message 1 () .prover .verifier (by decide) .here
      (.localCall 2 .verifier .here (.cons .here .nil)
        (.ret (.cons (.there (.there .here)) (.cons .here .nil)))))

def children : Protocol.Definitions Nat Role Nat Unit language [localSignature] [signature] :=
  Protocol.Definitions.snoc (language := language) .nil signature child

/-- Direct role execution, independent of common-source traversal and protocol resolution. -/
def directChild (selectedRuntime : Runtime Role String Nat Unit language Value State Event)
    (binding value : Nat) (path : List Frame) (states : States State) :=
  let prover := selectedRuntime.implementations binding .prover
  let verifier := selectedRuntime.implementations binding .verifier
  (LocatedExecution.run ⟨.prover, "interactive", binding, path, 0⟩ prover.meaning
    localDefinitions .here (.cons value .nil) prover.handler states).follow fun sent first =>
      (selectedRuntime.message (ty := ())
        ⟨.prover, "interactive", binding, path, 1⟩ () .verifier
        sent first.locals).follow fun received second =>
          (LocatedExecution.run ⟨.verifier, "interactive", binding, path, 2⟩ verifier.meaning
            localDefinitions .here (.cons received .nil) verifier.handler second.locals).follow
              fun checked final =>
                ⟨.returned (Values.cons (Value := PortValue (Role := Role) Value)
                  (ty := (Role.prover, ())) sent
                    (.cons (ty := (Role.verifier, ())) checked .nil)),
                  final, []⟩

/-- Equality is for arbitrary local services, transport behavior, inputs and role states. -/
theorem child_run_eq_direct
    (selectedRuntime : Runtime Role String Nat Unit language Value State Event)
    (binding value : Nat) (path : List Frame) (states : States State) :
    (children.denote .here "interactive" binding path (.cons value .nil)).run
      (selectedRuntime.handler localDefinitions) ⟨states, none⟩ =
        directChild selectedRuntime binding value path states := rfl

/-- Two calls share a body, select different bindings and return to the parent's binding. -/
def parent : Protocol.Program Nat Role Nat Unit language [localSignature] [signature]
    inputPorts resultPorts :=
  .invoke 10 ⟨.here, 2⟩ (.cons .here .nil)
    (.invoke 11 ⟨.here, 5⟩ (.cons .here .nil)
      (.localCall 12 .verifier .here (.cons (.there .here) .nil)
        (.ret (.cons (.there .here) (.cons .here .nil)))))

def parents := children.snoc signature parent

def pairOutcome : PIR.Outcome (Values (PortValue Value) resultPorts) → PIR.Outcome (Nat × Nat)
  | .returned (.cons prover (.cons verifier .nil)) => .returned (prover, verifier)
  | .stopped reason => .stopped reason

def runParent (selectedRuntime := runtime) (value : Nat := 3) :=
  selectedRuntime.run localDefinitions parents ⟨.here, 99⟩ "interactive"
    (.cons value .nil) initial

example : pairOutcome runParent.outcome = .returned (21, 125) := rfl
example : runParent.state.locals .prover = 22 := rfl
example : runParent.state.locals .verifier = [26, 21, 21, 5, 5] := rfl
example : runParent.state.locals .auditor = true := rfl
example : runParent.state.stoppedAt = none := rfl
example : runParent.events.map (fun event => (event.origin.role, event.value)) =
    [(.prover, .compute, 3), (.prover, .send, 5), (.verifier, .receive, 5),
      (.verifier, .compute, 5), (.prover, .compute, 5), (.prover, .send, 21),
      (.verifier, .receive, 21), (.verifier, .compute, 21), (.verifier, .compute, 26)] := rfl
example : runParent.events.map (fun event => event.origin.instanceId) =
    [2, 2, 2, 2, 5, 5, 5, 5, 99] := rfl

/-- An independent received value changes the actual verifier computation. -/
example : pairOutcome (runParent (runtime (received := fun value => value + 100))).outcome =
    .returned (21, 225) := rfl

def sendFailure := runParent (runtime (sendStop := fun value => value == 5))
example : pairOutcome sendFailure.outcome = .stopped .exhausted := rfl
example : sendFailure.state.locals .prover = 11 := rfl
example : sendFailure.state.locals .verifier = [] := rfl
example : sendFailure.events.map (fun event => event.value) =
    [(.compute, 3), (.send, 5)] := rfl
example : sendFailure.state.stoppedAt =
    some ⟨.prover, "interactive", 2, [.invocation 10], 1⟩ := rfl

def receiveFailure := runParent (runtime (receiveStop := fun value => value == 5))
example : pairOutcome receiveFailure.outcome = .stopped .refused := rfl
example : receiveFailure.state.locals .prover = 11 := rfl
example : receiveFailure.state.locals .verifier = [5] := rfl
example : receiveFailure.events.map (fun event => event.value) =
    [(.compute, 3), (.send, 5), (.receive, 5)] := rfl
example : receiveFailure.state.stoppedAt =
    some ⟨.verifier, "interactive", 2, [.invocation 10], 1⟩ := rfl

def localFailureRuntime : Runtime Role String Nat Unit language Value State Event :=
  { runtime with
    implementations := fun binding role =>
      { runtime.implementations binding role with
        effects := effects
        handler := fun request state =>
          let result := localHandler binding role request state
          if request == 21 then { result with outcome := .stopped .reject } else result } }

def localFailure := runParent localFailureRuntime
example : pairOutcome localFailure.outcome = .stopped .reject := rfl
example : localFailure.state.locals .prover = 22 := rfl
example : localFailure.state.locals .verifier = [21, 21, 5, 5] := rfl
example : localFailure.events.length = 8 := rfl
example : localFailure.state.stoppedAt =
    some ⟨.verifier, "interactive", 5, [.invocation 11], 2⟩ := rfl

/-- Binding a multi-role result has the same ordered ports as the inline continuation. -/
def bound : Protocol.Program Nat Role Nat Unit language [localSignature] [signature]
    inputPorts resultPorts :=
  .bind (.invoke 10 ⟨.here, 2⟩ (.cons .here .nil)
    (.ret (.cons .here (.cons (.there .here) .nil))))
    (.ret (.cons .here (.cons (.there .here) .nil)))

example : pairOutcome (runtime.run localDefinitions (children.snoc signature bound)
    ⟨.here, 99⟩ "interactive" (.cons 3 .nil) initial).outcome = .returned (5, 7) := rfl

/-- The fixture's local computations satisfy the separate all-reply locality judgment. -/
example (binding value : Nat) (role : Role) :
    LocallyAdmitted (fun _ => some role) role
      (localDefinitions.operation (runtime.implementations binding role).meaning
        (.call .here) (.cons value .nil)) := ⟨rfl, fun _ => True.intro⟩

/-- The judgment above is about the classification, not only about the body:
    the classification that gives this operation to nobody refuses it. Without
    this, an all-permitting classification would satisfy the positive example
    whatever the body did. -/
example (binding value : Nat) (role : Role) :
    ¬ LocallyAdmitted (fun _ => none) role
      (localDefinitions.operation (runtime.implementations binding role).meaning
        (.call .here) (.cons value .nil)) := by
  rintro ⟨h, -⟩
  simp [localPolicy] at h

def nested : Protocol.Program Nat Role Nat Unit language [localSignature] [signature, signature]
    inputPorts resultPorts :=
  .invoke 20 ⟨.here, 99⟩ (.cons .here .nil) (.ret (.cons .here (.cons (.there .here) .nil)))

def nestedFailure :=
  (runtime (receiveStop := fun value => value == 5)).run localDefinitions
    (parents.snoc signature nested) ⟨.here, 1000⟩ "interactive" (.cons 3 .nil) initial

example : nestedFailure.state.stoppedAt =
    some ⟨.verifier, "interactive", 2, [.invocation 20, .invocation 10], 1⟩ := rfl

abbrev loopSignature : Protocol.Signature Role Unit := ⟨inputPorts, inputPorts⟩

def loop (count : Nat) : Protocol.Program Nat Role Nat Unit language [localSignature] [signature]
    inputPorts inputPorts :=
  .repeat 30 count (.cons .here .nil)
    (.invoke 31 ⟨.here, 1⟩ (.cons .here .nil) (.ret (.cons .here .nil)))
    (.ret (.cons .here .nil))

def runLoop (count : Nat) (selectedRuntime := runtime) :=
  selectedRuntime.run localDefinitions (children.snoc loopSignature (loop count))
    ⟨.here, 77⟩ "interactive" (.cons 3 .nil) initial

def singleOutcome : PIR.Outcome (Values (PortValue Value) inputPorts) → PIR.Outcome Nat
  | .returned (.cons value .nil) => .returned value
  | .stopped reason => .stopped reason

example : singleOutcome (runLoop 0).outcome = .returned 3 := rfl
example : (runLoop 0).events = [] := rfl
example : singleOutcome (runLoop 3).outcome = .returned 39 := by cbv
example : (runLoop 3).state.locals .prover = 33 := by cbv
example : (runLoop 3).state.locals .verifier = [39, 39, 16, 16, 4, 4] := by cbv
example : (runLoop 3).events.map (fun event => event.origin.path) =
    List.replicate 4 [.iteration 30 0, .invocation 31] ++
      List.replicate 4 [.iteration 30 1, .invocation 31] ++
        List.replicate 4 [.iteration 30 2, .invocation 31] := by cbv

def loopFailure := runLoop 3 (runtime (receiveStop := fun value => value == 16))
example : singleOutcome loopFailure.outcome = .stopped .refused := rfl
example : loopFailure.state.locals .prover = 22 := rfl
example : loopFailure.state.locals .verifier = [16, 4, 4] := rfl
example : loopFailure.events.length = 7 := rfl
example : loopFailure.state.stoppedAt =
    some ⟨.verifier, "interactive", 1, [.iteration 30 1, .invocation 31], 1⟩ := rfl

/-- A same-signature reference does not identify the actual protocol body. -/
def stopped := children.snoc signature (.stop 40 .auditor .reject)
example : pairOutcome (runtime.run localDefinitions stopped ⟨.here, 8⟩
    "interactive" (.cons 3 .nil) initial).outcome = .stopped .reject := rfl
example : pairOutcome (runtime.run localDefinitions stopped ⟨.there .here, 8⟩
    "interactive" (.cons 3 .nil) initial).outcome = .returned (11, 19) := rfl
example : (runtime.run localDefinitions stopped ⟨.here, 8⟩ "interactive"
    (.cons 3 .nil) initial).state.stoppedAt =
      some ⟨.auditor, "interactive", 8, [], 40⟩ := rfl

/-- Equal underlying scalar representations do not permit cross-role operands or returns. -/
example : Var.decode inputPorts (.verifier, ()) 0 = none := rfl
example : Var.decode resultPorts (.verifier, ()) 0 = none := rfl
example : Var.decode resultPorts (.verifier, ()) 1 = some (.there .here) := rfl
example : Var.decode [signature] loopSignature 0 = none := rfl

end Tests.CommonProtocol
