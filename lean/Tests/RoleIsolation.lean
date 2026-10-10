import Zkc.Compiler.Role.Execution

/-! No foreign runtime values, even when their semantic type is uninhabited.
The receiver runs against arbitrary ingress without an executable honest sender.
-/

set_option autoImplicit false

namespace Tests.RoleIsolation

open Zkc.Source Zkc.Compiler.Role

-- false is the receiver, true is the sender; true is an uninhabited private sort.
abbrev Value : Bool → Type
  | false => Nat
  | true => Empty

abbrev language : Language where
  Ty := Bool
  Op := Empty
  arguments op := nomatch op
  result op := nomatch op
  condition := false

abbrev localSignature : DefinitionSignature Bool := ⟨[true], false⟩
def localDefinitions : Zkc.Source.Definitions language [localSignature] :=
  Zkc.Source.Definitions.snoc (language := language) .nil localSignature (.stop .abort)

abbrev inputs : List (Protocol.Port Bool Bool) := [(true, true)]
abbrev outputs : List (Protocol.Port Bool Bool) := [(false, false)]
abbrev signature : Protocol.Signature Bool Bool := ⟨inputs, outputs⟩

def source : Protocol.Program Nat Bool Unit Unit language [localSignature] [] inputs outputs :=
  .localCall 1 true .here (.cons .here .nil)
    (.message 2 () true false (by decide) .here (.ret (.cons .here .nil)))

def definitions := Protocol.Definitions.snoc (language := language) .nil signature source

def receiverInputs : Protocol.Role.Environment Value false inputs := fun ref => nomatch ref

/-- There cannot be a joint environment supplying the foreign private port. -/
example : ¬ Nonempty (Zkc.Source.Environment (Protocol.PortValue Value) inputs) := by
  intro ⟨env⟩
  exact nomatch env .here

/-- The receiver's environment has no readable reference to that foreign port. -/
example (ref : Var inputs (false, true)) : False := nomatch ref
example : Var.decode inputs (false, true) 0 = none := by cbv

abbrev effects : PIR.Signature := ⟨Empty, fun op => nomatch op⟩

def runtime : Protocol.Role.Runtime Bool Unit Unit Unit language Value Nat Nat where
  implementations _ :=
    { effects := effects
      condition := fun value => value != 0
      operation := fun op => nomatch op
      handler := fun op => nomatch op }
  send {ty} _ _ _ value state :=
    match ty, value with
    | false, value => ⟨.returned (), state, [value]⟩
    | true, value => nomatch value
  receive ty _ _ _ state :=
    match ty with
    | false => ⟨.returned 33, state + 1, [33]⟩
    | true => ⟨.stopped .exhausted, state, []⟩

def sourceRun :=
  (Protocol.Role.denoteDefinitions false definitions (Value := Value)
    .here () () [] receiverInputs).run (runtime.handler localDefinitions) ⟨0, none⟩

def targetRun := run runtime localDefinitions (projectDefinitions false definitions)
  ⟨.here, ()⟩ () receiverInputs 0

def output : PIR.Outcome (Protocol.Role.Environment Value false outputs) → PIR.Outcome Nat
  | .returned env => .returned (env .here)
  | .stopped reason => .stopped reason

example : output sourceRun.outcome = .returned 33 := by
  simp only [sourceRun, definitions, Protocol.Role.denoteDefinitions, source]
  cbv
example : output targetRun.outcome = .returned 33 := by cbv
example : targetRun.state.localState = 1 := by cbv
example : targetRun.events.map (fun event => event.value) = [33] := by cbv
example : targetRun.state.stoppedAt = none := by cbv
example : targetRun = sourceRun := by
  unfold targetRun run start sourceRun
  exact run_project _ _ _ _ _ _ _ _

end Tests.RoleIsolation
