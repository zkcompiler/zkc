import Examples.TablePhysical.Admission
import Tools.DeclarationAudit

/-! Changed candidates retain original-source admission and full executions.
These controls exercise alias substitution and refuse unsupported deletions,
including dormant code. The laws quantify over arbitrary providers and inputs.
-/

set_option autoImplicit false
namespace Tests.TableOptimization
open TableProtocol Zkc.Source Zkc.Realization PhaseAdmission
open TableProtocol.Admission

abbrev context : List Ty := [.scalar .seven, .scalar .seven, .residual .seven 1, .point .seven]

def source : RawRegion Ty Protocol.Operation :=
  .letOp .linear [0, 0, 1]
    (.letOp (.base (.evaluate .seven 1)) [3, 4]
      (.letOp .send [0, 1] (.letOp .draw [] (.ret 3))))

def optimized : RawRegion Ty Protocol.Operation :=
  .letOp (.base (.evaluate .seven 1)) [2, 3]
    (.letOp .send [0, 1] (.letOp .draw [] (.ret 3)))

example : source ≠ optimized := by decide

def checked : TablePhysical.Checked context (.scalar .seven) source
    (TablePhysical.propose .materialized optimized) :=
  (TablePhysical.check context (.scalar .seven) source
    (TablePhysical.propose .materialized optimized)).toOption.get (by decide)

def certificate : Certificate Phase := .next (.next (.next (.next .terminal)))

/-- The certificate belongs to the original body; a certificate for the shorter
candidate is not silently substituted for its source obligations. -/
example : checkRegion policy checked.logical certificate [.ready] = some [.ready] := by decide
example : checkRegion policy checked.logical (.next (.next (.next .terminal))) [.ready] = none := by decide

theorem calls {S E : Type} (provider : PIR.Handler Protocol.protocolInterface S E)
    (env : Environment Value context) (state : S)
    (physical : TablePhysical.State (Phase × S)) (states : (.ready, state) = physical.logical) :
    ∀ before call, Sum.inl (before, call) ∈
      (TablePhysical.Admission.run provider checked.physical (TablePhysical.inputs env) physical).events →
      interaction.enabled before call :=
  checked.calls_permitted checked.physical checked.targetDecoded certificate [.ready] [.ready]
    (by decide) provider env (TablePhysical.inputs env) .ready state physical states
    (TablePhysical.inputs_related env _ physical) ⟨.ready, by simp, rfl⟩

theorem complete {S E : Type} (provider : PIR.Handler Protocol.protocolInterface S E)
    (env : Environment Value context) (state : S) :
    TablePhysical.representation.Results (ty := .scalar .seven)
      (fun event : E => [event]) (fun event => [event])
      state ({logical := state} : TablePhysical.State S)
      ((checked.logical.denote Protocol.meaning env).run provider state)
      ((checked.physical.denote TablePhysical.meaning (TablePhysical.inputs env)).run
        (TablePhysical.handler provider) {logical := state}) :=
  checked.correct provider checked.physical checked.targetDecoded env (TablePhysical.inputs env)
    state _ rfl (TablePhysical.inputs_related env _ _)

def accepts (source candidate : RawRegion Ty Protocol.Operation) : Bool :=
  (TablePhysical.check context (.scalar .seven) source
    (TablePhysical.propose .lazy candidate)).isOk

-- A first alias exposes the identical endpoints of the next interpolation.
example : accepts (.letOp .linear [0, 0, 1] (.letOp .linear [0, 1, 2] (.ret 0)))
    (.ret 0) = true := by decide

-- Equal types or equal values in one invocation are not variable identity.
example : accepts (.letOp .linear [0, 1, 1] (.ret 0)) (.ret 0) = false := by decide

-- A dead partial evaluation, a failed call and the draw effect may not disappear.
example : accepts source (.letOp .send [0, 0] (.letOp .draw [] (.ret 2))) = false := by decide
example : accepts (.letOp (.base (.abortWrite .seven)) [0] (.ret 1)) (.ret 0) = false := by decide
example : accepts (.letOp .draw [] (.ret 1)) (.ret 0) = false := by decide

-- The loop count is irrelevant to checking an authored body for this rule.
example : accepts
    (.iterate 0 (.scalar .seven) 0 (.letOp .linear [0, 1, 2] (.ret 0)) (.ret 0))
    (.iterate 0 (.scalar .seven) 0 (.ret 0) (.ret 0)) = false := by decide
example : accepts
    (.bind (.scalar .seven) (.letOp .linear [0, 0, 1] (.ret 0))
      (.letOp .linear [0, 0, 2] (.ret 0)))
    (.bind (.scalar .seven) (.ret 0) (.ret 0)) = true := by decide

end Tests.TableOptimization
-- A module is not in its own environment while it elaborates, so it cannot
-- audit itself; Tests/Audit.lean covers the Tests family from a module that
-- imports them all.
run_cmd Tools.DeclarationAudit.check [`Zkc.Compiler.RegionFolding,
  `Examples.TableProtocol.Optimization] "TABLE-OPTIMIZATION-AUDIT-PASS"
