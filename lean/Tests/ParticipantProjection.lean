import Zkc.Compiler.Participant.Execution
import Tests.CommonProtocol

set_option autoImplicit false

namespace Tests.ParticipantProjection

open Zkc.Source Zkc.Source.Protocol
open Zkc.Compiler.Participant
open Tests.CommonProtocol

/-- Only the prover has an input port; no peer value is stored in this input family. -/
def inputs (value : Nat) : Environments Value inputPorts
  | .prover => fun _ => value
  | .verifier => fun ref => nomatch ref
  | .auditor => fun ref => nomatch ref

theorem inputs_eq (value : Nat) :
    inputs value = separate (Values.cons (Value := PortValue Value)
      (ty := (Role.prover, ())) value .nil).get := by
  funext role ty ref
  cases ref with
  | here => rfl
  | there ref => cases ref

def projectedParent (selectedRuntime := runtime) (value : Nat := 3) :=
  run selectedRuntime localDefinitions (projectDefinitions parents) ⟨.here, 99⟩
    "interactive" (inputs value) initial

/-- The end-to-end law compares whole results for arbitrary selected runtime services. -/
example (selectedRuntime : Runtime Role String Nat Unit language Value State Event) (value : Nat) :
    projectedParent selectedRuntime value = runParent selectedRuntime value := by
  unfold projectedParent
  rw [inputs_eq]
  exact run_project _ _ _ _ _ _ _

/-! The concrete results below follow from the law above, which equates the
projected run with the unprojected one for every runtime and input, and they
repeat the values `Tests.CommonProtocol` states for that unprojected run. They
are kept because they reach those values a different way: the law is proved by
rewriting and unfolding, while these evaluate the projected program itself, so
a law that held because both sides collapsed to the same thing for an
unintended reason would still leave these to answer. Changing one of these
without changing its counterpart in `Tests.CommonProtocol` means the
projection changed behaviour, which is the failure worth seeing twice. -/

example : pairOutcome projectedParent.outcome = .returned (21, 125) := by cbv
example : projectedParent.state.locals .prover = 22 := by cbv
example : projectedParent.state.locals .verifier = [26, 21, 21, 5, 5] := by cbv
example : projectedParent.events.map (fun event => event.origin.instanceId) =
    [2, 2, 2, 2, 5, 5, 5, 5, 99] := by cbv
example : pairOutcome
    (projectedParent (runtime (received := fun value => value + 100))).outcome =
      .returned (21, 225) := by cbv

def sendFailure := projectedParent (runtime (sendStop := fun value => value == 5))
example : pairOutcome sendFailure.outcome = .stopped .exhausted := by cbv
example : sendFailure.state.locals .prover = 11 := by cbv
example : sendFailure.state.locals .verifier = [] := by cbv
example : sendFailure.events.map (fun event => event.value) =
    [(.compute, 3), (.send, 5)] := by cbv

def receiveFailure := projectedParent (runtime (receiveStop := fun value => value == 5))
example : receiveFailure.state.locals .prover = 11 := by cbv
example : receiveFailure.state.locals .verifier = [5] := by cbv
example : receiveFailure.events.map (fun event => event.value) =
    [(.compute, 3), (.send, 5), (.receive, 5)] := by cbv
example : receiveFailure.state.stoppedAt =
    some ⟨.verifier, "interactive", 2, [.invocation 10], 1⟩ := by cbv

example : (projectedParent localFailureRuntime).events.length = 8 := by cbv
example : (projectedParent localFailureRuntime).state.stoppedAt =
    some ⟨.verifier, "interactive", 5, [.invocation 11], 2⟩ := by cbv

def projectedLoop (count : Nat) (selectedRuntime := runtime) :=
  run selectedRuntime localDefinitions
    (projectDefinitions (children.snoc loopSignature (loop count))) ⟨.here, 77⟩
      "interactive" (inputs 3) initial

example (count : Nat) (selectedRuntime : Runtime Role String Nat Unit language Value State Event) :
    projectedLoop count selectedRuntime = runLoop count selectedRuntime := by
  unfold projectedLoop
  rw [inputs_eq]
  exact run_project _ _ _ _ _ _ _

example : singleOutcome (projectedLoop 0).outcome = .returned 3 := by cbv
example : (projectedLoop 0).events = [] := by cbv
example : singleOutcome (projectedLoop 3).outcome = .returned 39 := by cbv
example : (projectedLoop 3).state.locals .verifier = [39, 39, 16, 16, 4, 4] := by cbv
example : (projectedLoop 3).events.map (fun event => event.origin.path) =
    List.replicate 4 [.iteration 30 0, .invocation 31] ++
      List.replicate 4 [.iteration 30 1, .invocation 31] ++
        List.replicate 4 [.iteration 30 2, .invocation 31] := by cbv

def stoppedLoop := projectedLoop 3 (runtime (receiveStop := fun value => value == 16))
example : singleOutcome stoppedLoop.outcome = .stopped .refused := by cbv
example : stoppedLoop.state.locals .verifier = [16, 4, 4] := by cbv
example : stoppedLoop.events.length = 7 := by cbv
example : stoppedLoop.state.stoppedAt =
    some ⟨.verifier, "interactive", 1, [.iteration 30 1, .invocation 31], 1⟩ := by cbv

example : (run (runtime (receiveStop := fun value => value == 5)) localDefinitions
    (projectDefinitions (parents.snoc signature nested)) ⟨.here, 1000⟩
      "interactive" (inputs 3) initial).state.stoppedAt =
        some ⟨.verifier, "interactive", 2, [.invocation 20, .invocation 10], 1⟩ := by cbv

/-- Independently authored target instructions use the actual received value. -/
def transfer : Transfer Role Unit Unit := ⟨60, (), .prover, .verifier, by decide, ()⟩

def exchange : Zkc.Compiler.Participant.Program Nat Role Nat Unit language [localSignature] []
    none inputPorts resultPorts :=
  .send transfer .here (.receive (.ret (.cons (.there .here) (.cons .here .nil))))

def exchangeDefinitions : Zkc.Compiler.Participant.Definitions Nat Role Nat Unit language
    [localSignature] [signature] :=
  Zkc.Compiler.Participant.Definitions.snoc (language := language) .nil signature exchange

example : pairOutcome (run (runtime (received := fun value => value + 40)) localDefinitions
    exchangeDefinitions ⟨.here, 9⟩ "interactive" (inputs 3) initial).outcome =
      .returned (3, 43) := by cbv

/-- The target interpreter executes the supplied body, not an original-source replay. -/
def alternative := exchangeDefinitions.snoc signature (.stop 61 .auditor .abort)
example : pairOutcome (run runtime localDefinitions alternative ⟨.here, 9⟩
    "interactive" (inputs 3) initial).outcome = .stopped .abort := by cbv
example : pairOutcome (run runtime localDefinitions alternative ⟨.there .here, 9⟩
    "interactive" (inputs 3) initial).outcome = .returned (3, 3) := by cbv

/-- A pending packet can only be consumed by receive; ret/call/another send have the wrong index. -/
example {Γ results : List (Port Role Unit)}
    (program : Zkc.Compiler.Participant.Program Nat Role Nat Unit language [localSignature] []
      (some transfer) Γ results) :
    ∃ next, program = .receive next := program.pending_receive

/-- Runtime equality does not mean equal interface-request counts. -/
def sourceChild := children.denote (Value := Value) .here "interactive" 2 [] (.cons 3 .nil)
def targetChild := (projectDefinitions children).denote (Value := Value) (Packet := fun _ => Nat)
  .here "interactive" 2 [] (inputs 3)

example : PIR.Within 3 sourceChild := fun _ _ _ => True.intro
example : PIR.Within 4 targetChild := fun _ _ _ _ => True.intro
example : ¬ PIR.Within 3 targetChild := by
  intro bounded
  exact bounded 0 0 0

end Tests.ParticipantProjection
