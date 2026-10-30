module

public import ZkcSecurity.Bindings.Source.LoopContracts
public meta import ZkcSecurityTools.SourceProperties.Assembly

public section
set_option autoImplicit false
namespace TestsSecurity.SourcePropertyCompanions

-- These are explicitly owned fixture identities, not inferred source hashes.
@[zkc "SourcePropertyControl/residual"]
theorem residual (n : Nat) : n + 0 = n := Nat.add_zero n

@[zkc "SourcePropertyControl/truth"]
theorem truth : True := True.intro

proof_wanted unfinished (n : Nat) : n + 0 = n
attribute [zkc "SourcePropertyControl/unfinished"] unfinished

example : (3 : Nat) + 0 = 3 :=
  source_property "SourcePropertyControl/application" companions
    ["SourcePropertyControl/residual" [3]] via (Nat.add_zero 3)

open Lean Meta Elab Command Term ZkcTools.Companions ZkcSecurity.Tools.SourceProperties in
run_elab do
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

end TestsSecurity.SourcePropertyCompanions
