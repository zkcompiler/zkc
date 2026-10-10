import Zkc.Source.Protocol.Family
import Zkc.Source.Family
import Zkc.Compiler.Participant.Counts
import Zkc.Compiler.Role.Counts
import Tests.CommonProtocol

set_option autoImplicit false
namespace Tests.ProtocolFamily
open Zkc.Source Zkc.Source.Protocol Tests.CommonProtocol

def template := (loop 0).mapCounts (fun _ => (PublicDimensions.Dim.param ⟨0, by decide⟩ : PublicDimensions.Dim 1))

theorem selected_member (count : Nat) : template.instantiate (fun _ => count) = loop count := rfl

example : template.nodeCount = 4 := by decide
example (count : Nat) : (template.instantiate (fun _ => count)).nodeCount = 4 := rfl

example (count : Nat) :
    Zkc.Compiler.Participant.project (template.instantiate (fun _ => count)) =
      (Zkc.Compiler.Participant.project template).mapCounts (PublicDimensions.Dim.eval (fun _ => count)) :=
  Zkc.Compiler.Participant.project_mapCounts _ _

example (self : Role) (count : Nat) :
    Zkc.Compiler.Role.project self (template.instantiate (fun _ => count)) =
      (Zkc.Compiler.Role.project self template).mapCounts (PublicDimensions.Dim.eval (fun _ => count)) :=
  Zkc.Compiler.Role.project_mapCounts _ _ _

/-- Resolve the template, retaining the actual stored child, then execute at
zero, one and multiple configurations with the existing source interpreter. -/
def execute (count : Nat) (seed : Nat := 3) :=
  runtime.run localDefinitions
    (children.snoc loopSignature (template.instantiate (fun _ => count)))
    ⟨.here, 77⟩ "interactive" (.cons seed .nil) initial

example : singleOutcome (execute 0).outcome = .returned 3 := rfl
example : singleOutcome (execute 1).outcome = .returned 4 := rfl
example : singleOutcome (execute 3).outcome = .returned 39 := by cbv
example (count : Nat) : execute count = runLoop count := rfl

/-- Connect actual ingress inputs to the stored counted protocol argument port.
The example uses an unrestricted phase profile;
its nontrivial admission obligation is an all-reply bound on stored calls. -/
abbrev effects := interface Role String Nat Unit language [localSignature] Value
abbrev JointState := LocatedExecution.StateWithOrigin Role String Nat State
abbrev JointEvent := LocatedExecution.LocatedEvent Role String Nat Event
abbrev Result := Values (PortValue Value) inputPorts

def member (count : Nat) (seed : Nat) : PIR.Proc effects Result :=
  (children.snoc loopSignature (template.instantiate (fun _ => count))).denote
    .here "interactive" 77 [] (.cons seed .nil)

def allowed (count : Nat) (_ : Nat) : Prop := count < 4

def ingress (raw : Nat × Nat) (state : JointState) :
    PIR.Execution JointState JointEvent (Sigma (fun _ : Nat => Nat)) :=
  if raw.1 < 4 then ⟨.returned ⟨raw.1, raw.2⟩, state, []⟩ else ⟨.stopped .refused, state, []⟩

theorem selects : Family.Selects ingress (fun _ _ => True) allowed := by
  intro raw state bound _ selected
  unfold ingress at selected
  split at selected
  next small => cases PIR.Outcome.returned.inj selected; exact small
  next large => cases selected

def interaction : PIR.Interaction effects :=
  ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
def contract (_ : Nat) (_ : Nat) : PIR.EndpointContract interaction Result :=
  ⟨(), 12, fun _ _ => True⟩

theorem admitted : Family.Admitted interaction member contract allowed where
  conforms count inputs _ := by
    induction member count inputs with
    | done => trivial
    | halt => trivial
    | call op next ih => exact ⟨trivial, fun reply => ih reply⟩
  bounded count inputs valid := by
    have cases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by
      unfold allowed at valid
      omega
    rcases cases with h | h | h | h <;> subst count <;>
      repeat first | exact True.intro | intro reply
  returned count inputs _ := by
    induction member count inputs with
    | done => trivial
    | halt => trivial
    | call op next ih => exact fun reply => ih reply

def executeInput (raw : Nat × Nat) :=
  Family.run ingress member (runtime.handler localDefinitions) raw ⟨initial, none⟩
theorem member_run (count seed : Nat) :
    (member count seed).run (runtime.handler localDefinitions) ⟨initial, none⟩ =
      execute count seed := rfl
theorem selected_execution (raw : Nat × Nat) (small : raw.1 < 4) :
    executeInput raw = execute raw.1 raw.2 := by
  simpa only [executeInput, Family.run, ingress, if_pos small, PIR.Execution.follow,
    List.nil_append] using member_run raw.1 raw.2
example : executeInput (3, 3) = execute 3 := selected_execution (3, 3) (by decide)
example : (executeInput (4, 3)).outcome = .stopped .refused := rfl
example : (executeInput (4, 3)).events = [] := rfl

/-- Assumes the selected count has been disclosed to the role. This selector
does not establish transport delivery or derive a view from joint ingress. -/
def known (self : Role) : Family.Known (fun count => count < 4) id
    (fun count => Zkc.Compiler.Role.project self (template.instantiate (fun _ => count))) where
  select count := Zkc.Compiler.Role.project self (template.instantiate (fun _ => count))
  realizes _ _ := rfl

theorem selected_role_schedule (self : Role) (raw : Nat × Nat)
    (bound : Sigma (fun _ : Nat => Nat))
    (chosen : (ingress raw ⟨initial, none⟩).outcome = .returned bound) :
    (known self).select bound.1 =
      (Zkc.Compiler.Role.project self template).mapCounts
        (PublicDimensions.Dim.eval (fun _ => bound.1)) := by
  have valid := selects raw ⟨initial, none⟩ bound trivial chosen
  calc
    _ = Zkc.Compiler.Role.project self (template.instantiate (fun _ => bound.1)) :=
      (known self).realizes bound.1 valid
    _ = _ := Zkc.Compiler.Role.project_mapCounts _ _ _

/-- Removing access to the selected public count makes these two schedules
indistinguishable locally. A global family alone cannot repair that knowledge. -/
example : ¬ Nonempty (Family.Known (fun count => count < 4) (fun _ : Nat => ())
    (fun count => Zkc.Compiler.Role.project .prover
      (template.instantiate (fun _ => count)))) := by
  rintro ⟨selection⟩
  have impossible := selection.agree 0 1 (by decide) (by decide) rfl
  cases impossible

example (raw : Nat × Nat) (bound : Sigma (fun _ : Nat => Nat))
    (chosen : (ingress raw ⟨initial, none⟩).outcome = .returned bound) :
    PIR.Within 12 (member bound.1 bound.2) :=
  (Family.Admitted.selected interaction member contract allowed admitted ingress
    (fun _ _ => True) selects raw ⟨initial, none⟩ bound trivial chosen).2.1

/-- Different ingress seeds reach the same stored argument port. -/
example : singleOutcome (executeInput (1, 20)).outcome = .returned 21 := rfl
example : singleOutcome (executeInput (1, 3)).outcome = .returned 4 := rfl

/-- A caller and its counted callee are resolved in the same dimension scope. -/
def caller : Protocol.Program (PublicDimensions.Dim 1) Role Nat Unit language [localSignature]
    [loopSignature, signature] inputPorts inputPorts :=
  .invoke 40 ⟨.here, 77⟩ (.cons .here .nil) (.ret (.cons .here .nil))
def storedTemplates :=
  let prior := children.mapCounts (fun n => (PublicDimensions.Dim.lit n : PublicDimensions.Dim 1))
  (prior.snoc loopSignature template).snoc loopSignature caller
def executeStored (count seed : Nat) :=
  runtime.run localDefinitions
    (storedTemplates.mapCounts (PublicDimensions.Dim.eval (fun _ => count)))
    ⟨.here, 99⟩ "interactive" (.cons seed .nil) initial
example : singleOutcome (executeStored 0 11).outcome = .returned 11 := rfl
example : singleOutcome (executeStored 1 11).outcome = .returned 12 := rfl
example : singleOutcome (executeStored 3 11).outcome = .returned 47 := by cbv

end Tests.ProtocolFamily
