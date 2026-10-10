import Zkc.Compiler.Role.Execution
import Tests.CommonProtocol

/-! All-constructor role projection on the maintained stored-call/loop client.
Expected values and failure prefixes are specified independently of projection.
-/

set_option autoImplicit false

namespace Tests.RoleProjection

open Zkc.Source Zkc.Compiler.Role
open Tests.CommonProtocol

abbrev Focus (Value : Unit → Type) (self : Role) (ports : List (Protocol.Port Role Unit)) :=
  Zkc.Source.Protocol.Role.Environment Value self ports

-- There is no prover value argument, even though the source input schema has a prover port.
def verifierInputs : Focus Value Role.verifier inputPorts := fun ref => nomatch ref
def auditorInputs : Focus Value Role.auditor inputPorts := fun ref => nomatch ref

def proverInputs (value : Nat) : Focus Value Role.prover inputPorts
  | _, .here => value
  | _, .there ref => nomatch ref

/-- Select one existing local implementation and state; incoming data is independent.
`received` is supplied by the strategy, with no sender state or sender operand.
-/
def openRuntime (role : Role) (received : Nat := 40)
    (selectedRuntime := runtime) :
    Protocol.Role.Runtime Role String Nat Unit language Value (State role) (Event role) where
  implementations binding := selectedRuntime.implementations binding role
  send location schema receiver value state :=
    (selectedRuntime.send (location.origin role) schema receiver value state).follow
      fun _ final => ⟨.returned (), final, []⟩
  receive _ _ _ _ state :=
    ⟨.returned received, record role received state, [(.receive, received)]⟩

def verifierParent := run (openRuntime .verifier) localDefinitions
  (projectDefinitions .verifier parents) ⟨.here, 99⟩ "interactive" verifierInputs []
def proverParent := run (openRuntime .prover) localDefinitions
  (projectDefinitions .prover parents) ⟨.here, 99⟩ "interactive" (proverInputs 3) 0

def verifierOutput {ports : List (Protocol.Port Role Unit)}
    (ref : Var ports (.verifier, ())) : PIR.Outcome (Focus Value Role.verifier ports) → PIR.Outcome Nat
  | .returned values => .returned (values ref)
  | .stopped reason => .stopped reason

def proverOutput {ports : List (Protocol.Port Role Unit)}
    (ref : Var ports (.prover, ())) : PIR.Outcome (Focus Value Role.prover ports) → PIR.Outcome Nat
  | .returned values => .returned (values ref)
  | .stopped reason => .stopped reason

example : verifierOutput (.there .here) verifierParent.outcome = .returned 144 := by cbv
example : proverOutput .here proverParent.outcome = .returned 21 := by cbv
example : proverParent.state.localState = 22 := by cbv
example : verifierParent.state.localState = [45, 40, 40, 40, 40] := by cbv
example : verifierParent.events.map (fun event => event.location.binding) = [2, 2, 5, 5, 99] := by cbv
example : verifierParent.events.map (fun event => event.location.path) =
    [[.invocation 10], [.invocation 10], [.invocation 11], [.invocation 11], []] := by cbv
example : verifierParent.events.map (fun event => event.location.site) = [1, 2, 1, 2, 12] := by cbv
example : verifierParent.events.map (fun event => event.location.entry) =
    List.replicate 5 "interactive" := by cbv

/-- Two actual hostile reply values change verifier computation without any prover inputs. -/
example : verifierOutput (.there .here)
    (run (openRuntime .verifier 900) localDefinitions (projectDefinitions .verifier parents)
      ⟨.here, 99⟩ "interactive" verifierInputs []).outcome = .returned 1004 := by cbv

/-- Actual source and target tables are related for arbitrary local handlers and ingress. -/
example (handler : PIR.Handler
    (Protocol.Role.interface Role String Nat Unit language [localSignature] Value) Nat Nat)
    (state : Nat) :
    ((projectDefinitions .verifier parents).denote .here "entry" 99 [] verifierInputs).run
      handler state =
    (Protocol.Role.denoteDefinitions .verifier parents .here "entry" 99 [] verifierInputs).run
      handler state := run_project handler parents .here "entry" 99 [] verifierInputs state

/-- Binding and caller restoration use the actual tuple, not the whole caller environment. -/
example : verifierOutput (.there .here)
    (run (openRuntime .verifier) localDefinitions (projectDefinitions .verifier
      (children.snoc signature bound)) ⟨.here, 99⟩ "entry" verifierInputs []).outcome =
        .returned 42 := by cbv

example : proverOutput .here
    (run (openRuntime .prover) localDefinitions (projectDefinitions .prover
      (children.snoc signature bound)) ⟨.here, 99⟩ "entry" (proverInputs 3) 0).outcome =
        .returned 5 := by cbv

def proverLoop (count : Nat) := run (openRuntime .prover) localDefinitions
  (projectDefinitions .prover (children.snoc loopSignature (loop count)))
    ⟨.here, 77⟩ "entry" (proverInputs 3) 0

def verifierLoop (count : Nat) := run (openRuntime .verifier) localDefinitions
  (projectDefinitions .verifier (children.snoc loopSignature (loop count)))
    ⟨.here, 77⟩ "entry" verifierInputs []

example : proverOutput .here (proverLoop 0).outcome = .returned 3 := by cbv
example : (verifierLoop 0).events = [] := by cbv
example : proverOutput .here (proverLoop 3).outcome = .returned 39 := by cbv
example : (verifierLoop 3).state.localState = [40, 40, 40, 40, 40, 40] := by cbv
example : (verifierLoop 3).events.map (fun event => event.location.path) =
    List.replicate 2 [.iteration 30 0, .invocation 31] ++
    List.replicate 2 [.iteration 30 1, .invocation 31] ++
    List.replicate 2 [.iteration 30 2, .invocation 31] := by cbv

/-- The third role supplies no values and executes no actions in these stored bodies. -/
example : (run (openRuntime .auditor) localDefinitions (projectDefinitions .auditor parents)
    ⟨.here, 99⟩ "entry" auditorInputs true).events = [] := by cbv

/-- Rejection in an actual erased foreign local service cannot stop the prover. -/
def privateFailure := run (openRuntime .prover 40 localFailureRuntime) localDefinitions
  (projectDefinitions .prover parents) ⟨.here, 99⟩ "interactive" (proverInputs 3) 0
example : proverOutput .here privateFailure.outcome = .returned 21 := by cbv
example : privateFailure.state.stoppedAt = none := by cbv

/-- Own service failure retains the failed state/events and skips the parent suffix. -/
def ownFailure := run (openRuntime .verifier 21 localFailureRuntime) localDefinitions
  (projectDefinitions .verifier parents) ⟨.here, 99⟩ "interactive" verifierInputs []
example : verifierOutput (.there .here) ownFailure.outcome = .stopped .reject := by cbv
example : ownFailure.state.localState = [21, 21] := by cbv
example : ownFailure.state.stoppedAt = some ⟨"interactive", 2, [.invocation 10], 2⟩ := by cbv
example : ownFailure.events.map (fun event => event.value) = [(.receive, 21), (.compute, 21)] := by cbv

/-- A nested caller does not replace a child's stop binding or invocation path. -/
example : (run (openRuntime .verifier 21 localFailureRuntime) localDefinitions
    (projectDefinitions .verifier (parents.snoc signature nested)) ⟨.here, 1000⟩
      "entry" verifierInputs []).state.stoppedAt =
        some ⟨"entry", 2, [.invocation 20, .invocation 10], 2⟩ := by cbv

/-- Own syntactic stop is observed; foreign stop has neither a peer reason nor output. -/
def foreignLeaf (reason : PIR.Stop) : Protocol.Definitions Nat Role Nat Unit language
    [localSignature] [signature] :=
  Protocol.Definitions.snoc (language := language) .nil signature (.stop 70 Role.prover reason)

def verifierLeaf (reason : PIR.Stop) := run (openRuntime .verifier) localDefinitions
  (projectDefinitions .verifier (foreignLeaf reason)) ⟨.here, 9⟩ "entry" verifierInputs [8]

example : verifierOutput (.there .here) (verifierLeaf .reject).outcome = .stopped .incomplete := by cbv
example : (verifierLeaf .abort).state.localState = [8] := by cbv
example : (verifierLeaf .exhausted).state.stoppedAt = none := by cbv
example : (verifierLeaf .refused).events = [] := by cbv
example : proverOutput .here
    (run (openRuntime .prover) localDefinitions (projectDefinitions .prover (foreignLeaf .abort))
      ⟨.here, 9⟩ "entry" (proverInputs 3) 7).outcome = .stopped .abort := by cbv
example : (run (openRuntime .prover) localDefinitions
    (projectDefinitions .prover (foreignLeaf .abort)) ⟨.here, 9⟩ "entry" (proverInputs 3) 7
    ).state.stoppedAt = some ⟨"entry", 9, [], 70⟩ := by cbv

/-- Stop/incomplete through bind cannot manufacture a result for its normal suffix. -/
def boundLeaf : Protocol.Definitions Nat Role Nat Unit language [localSignature] [signature] :=
  Protocol.Definitions.snoc (language := language) .nil signature (.bind (.stop (results := resultPorts) 71 Role.prover .reject)
    (.stop 72 Role.verifier .abort))
example : verifierOutput (.there .here)
    (run (openRuntime .verifier) localDefinitions (projectDefinitions .verifier boundLeaf)
      ⟨.here, 9⟩ "entry" verifierInputs []).outcome = .stopped .incomplete := by cbv

/-- Missing ingress suspends at the first receive, before any verifier effects. -/
def blocked := drive (openRuntime .verifier) localDefinitions
  (projectDefinitions .verifier parents) ⟨.here, 99⟩ "interactive" verifierInputs []
    (fun _ _ _ _ _ => none) 20

def status {I : PIR.Signature} {S E A : Type} : RunResult I S E A → Nat
  | .finished _ => 0
  | .suspended _ => 1
  | .yielded _ => 2

example : status blocked = 1 := by cbv
example : (match blocked with
    | .suspended cursor => cursor.state.localState
    | _ => [999]) = [] := by cbv
example : (match blocked with
    | .suspended cursor => cursor.events.length
    | _ => 999) = 0 := by cbv
example : (match blocked with
    | .suspended ⟨.call (.receive _ location _ _) _, _, _⟩ => some location
    | _ => none) = some ⟨"interactive", 2, [.invocation 10], 1⟩ := by cbv

/-- Resuming the exact retained continuation consumes hostile replies and restores callers. -/
def resumed := blocked.resume (fun op state =>
  some ((openRuntime .verifier).handler localDefinitions op state)) 20
example : (match resumed with
    | .finished result => verifierOutput (.there .here) result.outcome
    | _ => .stopped .incomplete) = .returned 144 := by cbv
example : (match resumed with
    | .finished result => result.events.map (fun event => event.location.binding)
    | _ => []) = [2, 2, 5, 5, 99] := by cbv

/-- Fuel zero yields an unchanged cursor, separately from suspension and incomplete. -/
example : status (drive (openRuntime .verifier) localDefinitions
    (projectDefinitions .verifier parents) ⟨.here, 99⟩ "interactive" verifierInputs []
      (fun _ _ _ _ _ => none) 0) = 2 := by cbv

/-- A real ingress failure is distinct from absence, and retains its effects. -/
def malformed := drive (openRuntime .verifier) localDefinitions
  (projectDefinitions .verifier parents) ⟨.here, 99⟩ "interactive" verifierInputs []
    (fun _ _ _ _ state => some ⟨.stopped .refused, 123 :: state, [(.receive, 123)]⟩) 20
example : (match malformed with
    | .finished result => verifierOutput (.there .here) result.outcome
    | _ => .returned 0) = .stopped .refused := by cbv
example : (match malformed with
    | .finished result => result.state.localState
    | _ => []) = [123] := by cbv

/-- Mixed loop accumulators contain local values only; foreign tuple entries are metadata. -/
def mixedInputsP (value : Nat) : Focus Value Role.prover resultPorts
  | _, .here => value
  | _, .there (.there ref) => nomatch ref

def mixedInputsV (value : Nat) : Focus Value Role.verifier resultPorts
  | _, .there .here => value
  | _, .there (.there ref) => nomatch ref

abbrev mixedSignature : Protocol.Signature Role Unit := ⟨resultPorts, resultPorts⟩

def cuts {Γ : List (Protocol.Port Role Unit)} :
    Protocol.Program Nat Role Nat Unit language [localSignature] [] (resultPorts ++ Γ) resultPorts :=
  .localCall 80 .prover .here (.cons .here .nil)
    (.localCall 81 .verifier .here (.cons (.there (.there .here)) .nil)
      (.localCall 82 .prover .here (.cons (.there .here) .nil)
        (.ret (.cons .here (.cons (.there .here) .nil)))))

def cutDefinitions := Protocol.Definitions.snoc (language := language)
  .nil mixedSignature (cuts (Γ := []))

-- A concrete separator, not a claimed general joint/open simulation.
def jointCut := localFailureRuntime.run localDefinitions cutDefinitions ⟨.here, 1⟩ "cut"
  (.cons 3 (.cons 21 .nil)) initial

def openCut := run (openRuntime .prover 40 localFailureRuntime) localDefinitions
  (projectDefinitions .prover cutDefinitions) ⟨.here, 1⟩ "cut" (mixedInputsP 3) 0

example : jointCut.state.locals .prover = 1 := by cbv
example : pairOutcome jointCut.outcome = .stopped .reject := by cbv
example : openCut.state.localState = 2 := by cbv
example : proverOutput .here openCut.outcome = .returned 6 := by cbv
example : openCut.events.map (fun event => event.value) = [(.compute, 3), (.compute, 4)] := by cbv

/-- This particular aligned cut agrees before P:b; it does not assert arbitrary scheduling. -/
def openCutPrefix := advance
  (fun op state => some ((openRuntime .prover 40 localFailureRuntime).handler localDefinitions op state))
  1 (start (projectDefinitions .prover cutDefinitions) ⟨.here, 1⟩ "cut" (mixedInputsP 3) 0)

example : (match openCutPrefix with
    | .yielded cursor => cursor.state.localState
    | _ => 999) = jointCut.state.locals .prover := by cbv
example : (match openCutPrefix with
    | .yielded cursor => cursor.events.map (fun event => event.location.site)
    | _ => []) = jointCut.events.filterMap (fun event =>
      if event.origin.role == .prover then some event.origin.site else none) := by cbv

def mixedLoop (count : Nat) :
    Protocol.Program Nat Role Nat Unit language [localSignature] [] resultPorts resultPorts :=
  .repeat 83 count (.cons .here (.cons (.there .here) .nil)) cuts
    (.ret (.cons .here (.cons (.there .here) .nil)))

def mixedDefinitions (count : Nat) := Protocol.Definitions.snoc (language := language)
  .nil mixedSignature (mixedLoop count)

example : proverOutput .here
    (run (openRuntime .prover) localDefinitions (projectDefinitions .prover (mixedDefinitions 2))
      ⟨.here, 1⟩ "mixed" (mixedInputsP 3) 0).outcome = .returned 13 := by cbv
example : verifierOutput (.there .here)
    (run (openRuntime .verifier) localDefinitions (projectDefinitions .verifier (mixedDefinitions 2))
      ⟨.here, 1⟩ "mixed" (mixedInputsV 4) []).outcome = .returned 6 := by cbv

/-- A foreign leaf is not visited at count zero, and ends iteration at positive count. -/
def leafLoop (count : Nat) :
    Protocol.Program Nat Role Nat Unit language [localSignature] [] inputPorts inputPorts :=
  .repeat 84 count (.cons .here .nil) (.stop 85 .verifier .reject)
    (.ret (.cons .here .nil))
def leafLoopDefinitions (count : Nat) := Protocol.Definitions.snoc (language := language)
  .nil loopSignature (leafLoop count)
example : proverOutput .here
    (run (openRuntime .prover) localDefinitions (projectDefinitions .prover (leafLoopDefinitions 0))
      ⟨.here, 1⟩ "leaf" (proverInputs 3) 7).outcome = .returned 3 := by cbv
example : proverOutput .here
    (run (openRuntime .prover) localDefinitions (projectDefinitions .prover (leafLoopDefinitions 2))
      ⟨.here, 1⟩ "leaf" (proverInputs 3) 7).outcome = .stopped .incomplete := by cbv

/-- A failed outgoing service retains its actual effects and skips the remainder. -/
def failedSend := run
  (openRuntime .prover 40 (runtime (sendStop := fun value => value == 5))) localDefinitions
  (projectDefinitions .prover parents) ⟨.here, 99⟩ "entry" (proverInputs 3) 0
example : proverOutput .here failedSend.outcome = .stopped .exhausted := by cbv
example : failedSend.state.localState = 11 := by cbv
example : failedSend.events.map (fun event => event.value) = [(.compute, 3), (.send, 5)] := by cbv
example : failedSend.state.stoppedAt = some ⟨"entry", 2, [.invocation 10], 1⟩ := by cbv

end Tests.RoleProjection
