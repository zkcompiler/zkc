import Tests.ResourceView
import Zkc.Compiler.Role.Resources
import Zkc.Compiler.Role.Simulation.Source

/-! Scoped resource execution of actual stored typed source and projected roles.
The selected store contains Ticket and Nat cells, while a String cell is framed.
The source also binds heterogeneous Nat/Unit results through the public Context API. -/
set_option autoImplicit false
namespace Tests.RoleResources
open Zkc.Source Zkc.Compiler.Role
open Zkc.Semantics.ResourceView Tests.ResourceView

abbrev Value : Bool → Type
  | false => Unit
  | true => Nat

abbrev language : Language where
  Ty := Bool
  Op := Op
  arguments _ := []
  result
    | .use _ _ => false
    | .spend _ => true
  condition := true

def implementation : Protocol.LocalImplementation language Value (Selected Cell admitted) String where
  effects := Tests.ResourceView.signature
  condition n := n != 0
  operation op _ := match op with
    | .use handle abortAfterUse => .call (.use handle abortAfterUse) .done
    | .spend amount => .call (.spend amount) .done
  handler := handler

abbrev useSignature : DefinitionSignature Bool := ⟨[], false⟩
abbrev spendSignature : DefinitionSignature Bool := ⟨[], true⟩
def localDefinitions (abortAfterUse : Bool) : Zkc.Source.Definitions language [spendSignature, useSignature] :=
  (((Zkc.Source.Definitions.nil : Zkc.Source.Definitions language []).snoc useSignature
    (.letOp (.primitive (.use original abortAfterUse)) .nil (.ret .here))).snoc spendSignature
    (.letOp (.primitive (.spend 3)) .nil (.ret .here)))

def runtime : Protocol.Role.Runtime Bool Unit Unit Unit language Value
    (Selected Cell admitted) String where
  implementations _ := implementation
  send _ _ _ _ state := (handler (.spend 1) state).follow fun _ next =>
    ⟨.returned (), next, ["sent"]⟩
  receive ty _ _ _ state := (handler (.spend 2) state).follow fun remaining next =>
    ⟨.returned (match ty with | false => () | true => remaining), next, ["received"]⟩

abbrev signature : Protocol.Signature Bool Bool := ⟨[], [(true, true), (true, false)]⟩
def body : Protocol.Program Nat Bool Unit Unit language [spendSignature, useSignature] [] [] signature.results :=
  .localCall 10 true .here .nil
    (.localCall 11 true (.there .here) .nil
      (.ret (.cons (.there .here) (.cons .here .nil))))

/-- Bind the heterogeneous returned tuple, preserving both roles' static indices. -/
def definitions := Protocol.Definitions.snoc (language := language) .nil signature
  (Protocol.Program.bind body (.ret (.cons .here (.cons (.there .here) .nil))))
def selected : Protocol.Instance Bool Unit Bool [signature] signature := ⟨.here, ()⟩

def scopedRun (abortAfterUse : Bool) :=
  Zkc.Compiler.Role.run (Resources.scopeRuntime admitted runtime) (localDefinitions abortAfterUse)
    (projectDefinitions true definitions) selected () Protocol.Role.Environment.empty initial

theorem stored_resource_connection (abortAfterUse : Bool) :
    PIR.Related (Resources.StateFrame admitted initial) (fun e => [e]) (fun e => [e])
      ((Protocol.Role.denoteDefinitions true definitions selected.callee () () []
        Protocol.Role.Environment.empty).run (runtime.handler (localDefinitions abortAfterUse))
          ⟨restrict admitted initial, none⟩)
      (scopedRun abortAfterUse) :=
  Resources.run_project_scoped admitted initial runtime (localDefinitions abortAfterUse)
    definitions true selected () Protocol.Role.Environment.empty

example : (scopedRun false).state.localState .ticket = ⟨17, 1, false⟩ := by cbv
example : (scopedRun false).state.localState .quota = 5 := by cbv
example : (scopedRun false).state.stoppedAt = none := by cbv
example : (scopedRun false).events.map (·.value) = ["spent", "consumed"] := by cbv
example : (scopedRun true).outcome = .stopped .abort := by cbv
example : (scopedRun true).state.localState .ticket = ⟨17, 1, false⟩ := by cbv
example : (scopedRun true).state.localState .quota = 5 := by cbv
example : (scopedRun true).state.stoppedAt = some ⟨(), (), [], 11⟩ := by cbv
example : (scopedRun true).events.map (·.value) = ["spent", "consumed"] := by cbv
example (abortAfterUse : Bool) : (scopedRun abortAfterUse).state.localState .outside = "retained" :=
  (stored_resource_connection abortAfterUse).state.1.2 .outside (by decide)
example : match (scopedRun false).outcome with
  | .returned values => values .here = 5 ∧ values (.there .here) = ()
  | .stopped _ => False := by cbv; trivial

/-- The source-to-role prepend bridge also covers a foreign head and a retained
caller variable of another type. No inhabitedness premise or private helper. -/
def retainedEnv (n : Nat) : Zkc.Source.Environment (Protocol.PortValue Value) [(true, true)] :=
  (Values.cons n .nil).get
def mixedValues (n : Nat) (u : Unit) : Values (Protocol.PortValue Value) [(false, false), (true, true)] :=
  .cons u (.cons n .nil)

example (quota : Nat) (ticket : Unit) (retained : Nat) :
    @Eq (Protocol.Role.Environment Value true [(false, false), (true, true), (true, true)])
      (Simulation.focus (language := language) true
        (Zkc.Source.Environment.prepend (retainedEnv retained) (mixedValues quota ticket)))
      (Protocol.Role.Environment.prepend
        (Simulation.focus (language := language) true (retainedEnv retained))
        (Simulation.focusValues (language := language) true (mixedValues quota ticket))) :=
  Simulation.focus_prepend (language := language) (Value := Value) true
    (retainedEnv retained) (mixedValues quota ticket)

abbrev interface := Protocol.Role.interface Bool Unit Unit Unit language [spendSignature, useSignature] Value
def wholeHandler := (Resources.scopeRuntime admitted runtime).handler (localDefinitions false)
def atQuota (n : Nat) : Protocol.Role.State Unit Unit (Store Cell) :=
  ⟨install admitted initial (replaceSelected ⟨17, 0, true⟩ n), none⟩
def sendOp : interface.Op := .send (ty := true) ⟨(), (), [], 20⟩ () false 7
def receiveOp : interface.Op := .receive true ⟨(), (), [], 21⟩ () false

example : (wholeHandler sendOp (atQuota 8)).outcome = .returned () := by cbv
example : (wholeHandler sendOp (atQuota 8)).state.localState .quota = 7 := by cbv
example : (wholeHandler sendOp (atQuota 0)).outcome = .stopped .exhausted := by cbv
example : (wholeHandler sendOp (atQuota 0)).events.map (·.value) = ["spent"] := by cbv
example : (wholeHandler sendOp (atQuota 0)).state.stoppedAt = some ⟨(), (), [], 20⟩ := by cbv
example : (wholeHandler sendOp (atQuota 0)).state.localState .outside = "retained" := by cbv
example : (wholeHandler receiveOp (atQuota 8)).outcome = .returned (6 : Nat) := by cbv
example : (wholeHandler receiveOp (atQuota 1)).outcome = .stopped .exhausted := by cbv
example : (wholeHandler receiveOp (atQuota 1)).state.localState .quota = 0 := by cbv
example : (wholeHandler receiveOp (atQuota 1)).events.map (·.value) = ["spent"] := by cbv
example : (wholeHandler receiveOp (atQuota 1)).state.stoppedAt = some ⟨(), (), [], 21⟩ := by cbv
example : (wholeHandler receiveOp (atQuota 1)).state.localState .outside = "retained" := by cbv
example : (wholeHandler (.stop ⟨(), (), [], 22⟩ .refused) (atQuota 8)).state.localState .quota = 8 := by cbv
example : (wholeHandler (.stop ⟨(), (), [], 22⟩ .refused) (atQuota 8)).state.stoppedAt =
    some ⟨(), (), [], 22⟩ := by cbv

end Tests.RoleResources
