import Examples.TablePhysical.Admission
import Tools.DeclarationAudit

/-! Admission of actual physical candidates, including a different provider and
stopped effects. Native host faults are tested at the Rust ownership boundary. -/
set_option autoImplicit false
namespace Tests.TablePhysicalAdmission
open TableProtocol Zkc.Source Zkc.Realization PhaseAdmission
open TableProtocol.Admission

abbrev context : List Ty := [.residual .seven 1, .point .seven]

def source : RawRegion Ty Protocol.Operation :=
  .letOp (.base (.evaluate .seven 1)) [0, 1]
    (.bind .boolean (.letOp .send [0, 0] (.ret 0))
      (.letOp .draw [] (.ret 2)))

def checked : TablePhysical.Checked context (.scalar .seven) source
    (TablePhysical.propose .lazy source) :=
  (TablePhysical.check context (.scalar .seven) source
    (TablePhysical.propose .lazy source)).toOption.get (by decide)

def certificate : Certificate Phase := .next (.bind (.next .terminal) (.next .terminal))

/-- An arbitrary provider, retained physical store and captured input environment
are permitted: admission does not depend on the deterministic trace fixture. -/
theorem actual_calls {S E : Type} (provider : PIR.Handler Protocol.protocolInterface S E)
    (env : Environment Value context) (state : S)
    (physical : TablePhysical.State (Phase × S)) (states : (.ready, state) = physical.logical) :
    ∀ before call, Sum.inl (before, call) ∈
      (TablePhysical.Admission.run provider checked.physical (TablePhysical.inputs env) physical).events →
      interaction.enabled before call :=
  checked.calls_permitted checked.physical checked.targetDecoded certificate [.ready] [.ready]
    (by decide) provider env (TablePhysical.inputs env) .ready state physical states
    (TablePhysical.inputs_related env _ physical) ⟨.ready, by simp, rfl⟩

theorem actual_return {S E : Type} (provider : PIR.Handler Protocol.protocolInterface S E)
    (env : Environment Value context) (state : S) (value : TablePhysical.Value (.scalar .seven))
    (returned : (TablePhysical.Admission.run provider checked.physical (TablePhysical.inputs env)
      {logical := (.ready, state)}).outcome = .returned value) :
    Covered summaryLaws [.ready]
      (TablePhysical.Admission.run provider checked.physical (TablePhysical.inputs env)
        {logical := (.ready, state)}).state.logical.1 :=
  checked.return_permitted checked.physical checked.targetDecoded certificate [.ready] [.ready]
    (by decide) provider env (TablePhysical.inputs env) .ready state _ rfl
    (TablePhysical.inputs_related env _ _) ⟨.ready, by simp, rfl⟩ value returned

/-- False is a typed send reply. A stopped draw changes provider state and emits
an event, while retaining the sent phase. The fixture handler does neither. -/
def alternate : PIR.Handler Protocol.protocolInterface Nat Nat
  | .base _, state => ⟨.returned false, state + 1, [10]⟩
  | .send _ _, state => ⟨.returned false, state + 1, [20]⟩
  | .draw, state => ⟨.stopped .exhausted, state + 7, [30]⟩

def send : PIR.Execution (TablePhysical.State (Phase × Nat))
    (Sum (Phase × Protocol.Call) Nat) (TablePhysical.Value .boolean) :=
  TablePhysical.invoke (PIR.ExecutionPath.handler interaction alternate) .send
    (.cons (.immediate 2) (.cons (.immediate 5) .nil)) {logical := (.ready, 0)}

example : send.outcome = .returned false := rfl
example : send.state.logical = (.sent, 1) := rfl
example : send.events = [.inl (.ready, .send 2 5), .inr 20] := rfl

def failedDraw := TablePhysical.invoke (PIR.ExecutionPath.handler interaction alternate)
  .draw .nil send.state

example : failedDraw.outcome = .stopped .exhausted := rfl
example : failedDraw.state.logical = (.sent, 8) := rfl
example : failedDraw.events = [.inl (.sent, .draw), .inr 30] := rfl

-- A missing scalar reference fails before entering the logical provider.
def missingOperand := TablePhysical.invoke (PIR.ExecutionPath.handler interaction alternate)
  .send (.cons (.reference 0) (.cons (.immediate 5) .nil))
  ({logical := (.ready, 0)} : TablePhysical.State (Phase × Nat))

example : missingOperand.outcome = .stopped .refused := rfl
example : missingOperand.state.logical = (.ready, 0) := rfl
example : missingOperand.events = [] := rfl

end Tests.TablePhysicalAdmission
-- A module is not in its own environment while it elaborates, so it cannot
-- audit itself; Tests/Audit.lean covers the Tests family from a module that
-- imports them all.
run_cmd Tools.DeclarationAudit.check [`Examples.TablePhysical.Admission] "TABLE-PHYSICAL-ADMISSION-AUDIT-PASS"
