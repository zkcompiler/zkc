module

public import ZkcSecurity.Bindings.Source.LoopContracts
public import ZkcSecurityExamples.Sumcheck.SourcePairGoals
public import ZkcSecurityExamples.Sumcheck.SourcePublicGoals
public import ZkcSecurityExamples.Sumcheck.SourcePairCompanions
public import ZkcSecurityExamples.Sumcheck.SourcePublicCompanions
public meta import ZkcSecurityTools.SourceProperties.Assembly

public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TestsSecurity.SourcePropertyCompanions

open Lean Elab Command in
run_cmd do
  for name in [
      `ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small,
      `ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.two,
      `ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_no,
      `ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no,
      `ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_cost,
      `ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_cost] do
    if (← getEnv).contains name then
      throwError "the independent external author module imported a consumer: {name}"

-- These are explicitly owned fixture identities, not inferred source hashes.
@[zkc "SourcePropertyControl/residual"]
theorem residual (n : Nat) : n + 0 = n := Nat.add_zero n

@[zkc "SourcePropertyControl/truth"]
theorem truth : True := True.intro

-- This external author module imports goals and mathematics, never consumers.
-- Its client imports both it and the goal modules, without a dependency cycle.
open ZkcSecurity.Realizations.Sumcheck in
@[zkc "SourcePropertyModules/small"]
theorem externalSmallPair : SourcePairInstallations.small_goal :=
  SourcePairInstallations.Companions.small

open ZkcSecurity.Realizations.Sumcheck in
@[zkc "SourcePropertyModules/two"]
theorem externalTwoPair : SourcePairInstallations.two_goal :=
  SourcePairInstallations.Companions.two

open ZkcSecurity.Realizations.Sumcheck in
@[zkc "SourcePropertyModules/small_no"]
noncomputable def externalSmallNo : SourcePublicInstallations.small_no_goal :=
  SourcePublicInstallations.Companions.small_no

open ZkcSecurity.Realizations.Sumcheck in
@[zkc "SourcePropertyModules/two_no"]
noncomputable def externalTwoNo : SourcePublicInstallations.two_no_goal :=
  SourcePublicInstallations.Companions.two_no

open ZkcSecurity.Realizations.Sumcheck in
@[zkc "SourcePropertyModules/small_cost"]
theorem externalSmallCost : SourcePublicInstallations.small_cost_goal :=
  SourcePublicInstallations.Companions.small_cost

open ZkcSecurity.Realizations.Sumcheck in
@[zkc "SourcePropertyModules/two_cost"]
theorem externalTwoCost : SourcePublicInstallations.two_cost_goal :=
  SourcePublicInstallations.Companions.two_cost

section HeaderOnly
universe u
variable (unused : Type) (premise : True)
include premise

companion_goal headerOnly for theorem absentConsumer {α : Type u} (x : α) (h : x = x) : x = x
companion_goal valueHeaderOnly for def absentValue {α : Type u} (x : α) : { y : α // y = x }

end HeaderOnly

/-- error: companion_goal requires an explicit independently fixed type -/
#guard_msgs in
companion_goal inferredHeader for def absentInferred

open Lean Meta Elab Command ZkcTools.Companions in
run_cmd do
  for (goal, declaration, proof, body) in [
      (``headerOnly, `TestsSecurity.SourcePropertyCompanions.printedProof, true,
        "by intro premise α x h; have _ := premise; exact h"),
      (``valueHeaderOnly, `TestsSecurity.SourcePropertyCompanions.printedValue, false,
        "by intro unused premise α x; exact ⟨x, rfl⟩")] do
    let header ← liftTermElabM <| goalHeader goal declaration proof
    let .ok parsed := Parser.runParserCategory (← getEnv) `command
      ("set_option linter.unusedVariables false in\n" ++ header ++ body)
      | throwError "the goal header printer did not produce an ordinary Lean declaration"
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) <|
      elabCommand parsed
    unless (← getConstInfo declaration).type == (← getConstInfo goal).value! do
      throwError "a generated polymorphic or dependent header changed its fixed type"

companion_goal generatedResidual in
theorem generatedResidualProof {α : Type} (x : α) (premise : x = x) : x = x := by
  exact premise

proof_wanted unfinished (n : Nat) : n + 0 = n
attribute [zkc "SourcePropertyControl/unfinished"] unfinished

example : (3 : Nat) + 0 = 3 :=
  source_property "SourcePropertyControl/application" companions
    ["SourcePropertyControl/residual" [3]] via (Nat.add_zero 3)

open Lean Meta Elab Command Term ZkcTools.Companions ZkcSecurity.Tools.SourceProperties in
run_elab do
  unless !(← getEnv).contains `TestsSecurity.SourcePropertyCompanions.absentConsumer do
    throwError "header-only mode declared a dummy consumer or proof"
  let expected ← elabTerm (← `(term| (3 : Nat) + 0 = 3)) none
  let fallback : DefaultMethod := ⟨"valid-fallback", ← `(term| rfl)⟩
  let (selected, _) ← attempt
    { identity := "SourcePropertyControl/application"
      selections := #[⟨"SourcePropertyControl/residual", #[← `(term| 3)]⟩] }
    expected #[]
  unless (match selected with | .discharged _ _ _ => true | _ => false) do
    throwError "the component companion was not selected"
  let (pending, pendingReport) ← attempt
    { identity := "SourcePropertyControl/application"
      selections := #[⟨"SourcePropertyControl/unfinished", #[← `(term| 3)]⟩,
        ⟨"SourcePropertyControl/residual", #[← `(term| 3)]⟩] }
    expected #[fallback]
  unless (match pending with | .openObligation _ _ => true | _ => false) do
    throwError "a default replaced an explicitly unfinished component"
  unless (pendingReport.getObjValAs? String "expected_type").toOption ==
      some (toString (← withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr expected))) do
    throwError "the report changed the independently fixed expected type"
  let (invalid, _) ← attempt
    { identity := "SourcePropertyControl/application"
      selections := #[⟨"SourcePropertyControl/residual", #[← `(term| 3)]⟩,
        ⟨"SourcePropertyControl/truth", #[]⟩] }
    (Lean.mkConst ``True) #[⟨"truth", ← `(term| True.intro)⟩]
  unless (match invalid with | .refused _ _ => true | _ => false) do
    throwError "a default hid an invalid explicit component"
  let missingType ← elabTerm (← `(term|
    ZkcSecurity.Source.LoopContracts.Paired
      (carriers := Zkc.Source.Structured.uniformCarriers Unit Unit)
      (scope := ⟨0, 1, []⟩)
      (fun (state index : Nat) => PIR.Process.done (state + index))
      (fun (state _index : Nat) => PIR.Process.done state))) none
  let (missing, missingReport) ← attempt
    { identity := "SourcePropertyControl/missing-loop-invariant"
      responsibility := "typed repeat invariant step" }
    missingType #[⟨"unavailable", ← `(term| True.intro)⟩]
  unless (match missing with | .openObligation _ attempts => attempts.size == 1 | _ => false) do
    throwError "missing mathematics did not remain an open authoring obligation"
  unless (missingReport.getObjValAs? String "expected_type").toOption ==
      some (toString (← withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr missingType))) do
    throwError "the missing typed loop contract was reported at a different type"
  unless (missingReport.getObjValAs? String "identity").toOption ==
      some "SourcePropertyControl/missing-loop-invariant" do
    throwError "a search path replaced the supplied template identity"
  unless (missingReport.getObjVal? "source_span").toOption == some Json.null do
    throwError "an unavailable source location was invented"
  unless (missingReport.getObjValAs? String "status_scope").toOption ==
      some "authoring only; receipt audit remains authoritative" do
    throwError "an open authoring obligation became a canonical receipt"
  let staleGoalRefused ← try
    let _ ← attempt { identity := "SourcePropertyControl/stale-goal", goal := some ``generatedResidual }
      (mkConst ``True) #[⟨"otherwise-valid", ← `(term| True.intro)⟩]
    pure false
  catch _ => pure true
  unless staleGoalRefused do
    throwError "a supplied goal changed the full independently fixed telescope"

end TestsSecurity.SourcePropertyCompanions
