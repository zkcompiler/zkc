import Examples.SourcePlan
import Zkc.Source.Bounds
import Zkc.Compiler.Bounds

set_option autoImplicit false

namespace Tests.SourcePlan

open Zkc.Source Zkc.Compiler SourcePlanExample

example : (run true 1).outcome = .returned (2, 4, 4) := by decide
example : (run true 1).state = 3 := by decide
example : (run true 1).events = [1, 2, 3] := by decide

example : (run true 0).outcome = .stopped .abort := by decide
example : (run true 0).state = 1 := by decide
example : (run true 0).events = [0] := by decide
example : (run false 1).outcome = .stopped .reject := by decide
example : (run false 1).state = 0 := by decide
example : (run false 1).events = [] := by decide

example : (checkDirect source (lower source).erase).isSome = true := by decide

/-- Same-typed positions are not interchangeable, even though both form valid code. -/
def swapped : RawProgram Ty Op :=
  .letOp (.subtract .five) [3, 2]
    (.letOp (.negate .seven) [5]
      (.branch 2
        (.iterate 3 .natural 3
          (.letOp .record [0] (.letOp .increment [0] (.ret 0)))
          (.letOp .pack [2, 1, 0] (.ret 0)))
        (.stop .reject)))

example : (swapped.elaborate context .summary (language := language)).toOption.isSome = true := by decide
example : (checkDirect source swapped).isNone = true := by decide
example : (checkDirect source (.stop .reject)).isNone = true := by decide

example : decodeVariable context (.field .seven) 2 = .error (.invalidOperand 2 (.field .seven)) := by rfl
example : decodeVariable context .natural 8 = .error (.invalidOperand 8 .natural) := by rfl

/-- Even a dormant branch must have valid operand references. -/
example : (RawProgram.branch 0 (.stop .reject) (.ret 99) : RawProgram Ty Op).elaborate
    context .summary (language := language) = .error (.invalidOperand 99 .summary) := by rfl

example : bindInputs "prover" declarations (supplied true 1) = .ok (values true 1) := by rfl
example : (bindInputs "verifier" declarations (supplied true 1)).toOption.isNone = true := by decide
example : (bindInputs "prover" declarations ((supplied false 1).take 4)).toOption.isNone = true := by decide
example : (bindInputs "prover" (declarations ++ declarations) (supplied true 1)).toOption.isNone = true := by decide

/-- A certificate covers all inputs and arbitrary stateful handlers, not one fixture run. -/
theorem checked_execution {candidate : RawProgram Ty Op} (checked : CheckedPlan source candidate)
    (env : Environment meaning.Value context) (state : Nat) :
    checked.plan.run meaning handler env state = (source.denote meaning env).run handler state :=
  checked.correct meaning handler env state

-- JSON round trips are runtime controls of the source and plan tools.
-- The kernel-checked round trips concern typed source and plan erasure.

example : (checkCandidate request candidate (language := language)).toOption.isSome = true := by decide
example : metadataError request { candidate with format := 2 } = some .formatVersion := by decide
example : metadataError request { candidate with semantics := "future" } = some .semanticsVersion := by decide
example : metadataError request { candidate with capabilities := ["native-cost"] } =
    some .unsupportedCapability := by decide
example : metadataError request { candidate with realization := "generated-code" } =
    some .unsupportedRealization := by decide
example : metadataError request { candidate with rule := "unproved-rewrite" } = some .unsupportedRule := by decide
example : metadataError request { candidate with claim := { completeExecution with scope := "one-input" } } =
    some .unsupportedClaim := by decide
example : metadataError request { candidate with context := { candidate.context with role := "verifier" } } =
    some .contextMismatch := by decide
example : metadataError request { candidate with requirements := [⟨"extra", "1"⟩] } =
    some .unapprovedRequirement := by decide
example : metadataError { request with permittedRequirements := [⟨"extra", "1"⟩] }
    { candidate with requirements := [⟨"extra", "1"⟩] } = some .unsupportedRequirement := by decide

def operationBound : Op → Nat
  | .record => 1
  | _ => 0

theorem operationBound_valid (op : Op) (args : Values Value (arguments op)) :
    PIR.Within (operationBound op) (meaning.operation op args) := by
  cases op with
  | subtract domain =>
    cases domain <;> cases args with
    | cons a tail => cases tail with
      | cons b tail => cases tail; trivial
  | negate domain =>
    cases domain <;> cases args with
    | cons a tail => cases tail; trivial
  | increment =>
    cases args with
    | cons n tail => cases tail; trivial
  | record =>
    cases args with
    | cons n tail => cases tail; exact fun _ => trivial
  | pack =>
    cases args with
    | cons a tail => cases tail with
      | cons b tail => cases tail with
        | cons n tail => cases tail; trivial

example : source.callBound operationBound = 3 := by decide

/-- The public call bound holds for every environment, including failed executions. -/
theorem source_bound (env : Environment meaning.Value context) :
    PIR.Within 3 (source.denote meaning env) :=
  source.denote_within meaning operationBound operationBound_valid env

end Tests.SourcePlan
