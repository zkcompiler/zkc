import ZkcSecurityExamples.Sumcheck.SourcePairInstallations
import ZkcSecurityExamples.Sumcheck.SourcePublicInstallations
import ZkcSecurityTools.SourceProperties.Assembly
import TestsSecurity.SourcePropertyCompanions
import ZkcSecurityExamples.Sumcheck.SourcePairGoals
import ZkcSecurityExamples.Sumcheck.SourcePublicGoals

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Lean Meta Elab Command Term ZkcTools.Companions ZkcSecurity.Tools.SourceProperties
open ZkcExamples.Structured.SumcheckSourceSelections

-- The imported assembly modules consume ordinary companions from independent
-- modules. These local aliases exercise explicit selection at the same types.
private theorem smallPair : ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small_goal :=
  @ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small
private theorem twoPair : ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.two_goal :=
  @ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.two
private noncomputable def smallNo : ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_no_goal :=
  @ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_no
private noncomputable def twoNo : ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no_goal :=
  @ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no
private theorem smallCost : ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_cost_goal :=
  @ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_cost
private theorem twoCost : ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_cost_goal :=
  @ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_cost

-- All controls use the independently generated original root type. In
-- particular, the wrong candidate never supplies the type being tested.
private meta def checkConsumer (sourceSyntax : TSyntax `term) (label : String)
    (goal original proof wrongProof : Name) : TermElabM Unit := do
  let subject ← sourceIdentity (← elabTerm sourceSyntax (some (mkConst ``Zkc.Source.Structured.Program)))
  let identity := subject.implementationKey label
  let .ok key := Json.parse identity | throwError "noncanonical companion key"
  unless key.compress == identity do throwError "companion key is not compact canonical JSON"
  let expected := (← getConstInfo goal).value!
  unless !expected.hasFVar && !expected.hasMVar do throwError "generated source goal is not closed"
  unless !expected.getUsedConstants.contains original && !expected.getUsedConstants.contains proof do
    throwError "a generated source goal depends on its own companion"
  unless (← getConstInfo original).type == expected do
    throwError "a generated consumer changed its original stored declaration type"
  let proofSyntax ← `(term| @$(mkIdent proof))
  let fallback : DefaultMethod := ⟨"existing-checked-consumer", proofSyntax⟩
  let request : Request := {
    identity := subject.implementationKey (label ++ "-missing-control")
    goal := some goal, subject := some subject }
  let (completed, _) ← attempt request expected #[fallback]
  unless (match completed with | .discharged _ _ _ => true | _ => false) do
    throwError "the original consumer no longer proves its generated goal: {proof}"
  forallTelescope (n := TermElabM) expected fun parameters resultType => do
    let (missing, row) ← attempt request resultType #[]
    unless (match missing with | .openObligation _ _ => true | _ => false) do
      throwError "missing source mathematics did not remain open"
    let .ok context := (row.getObjVal? "context").bind Json.getArr?
      | throwError "missing real source telescope"
    unless context.size == parameters.size && parameters.size > 5 do
      throwError "the real source report lost premises"
    unless (row.getObjVal? "source_span").toOption == some Json.null do
      throwError "a nonexistent original source span was invented"
    unless (row.getObjVal? "source_identity").toOption == some (toJson subject) do
      throwError "the retained Entry identity was lost"
    unless (row.getObjValAs? String "goal_declaration").toOption == some goal.toString do
      throwError "the authoritative real source goal was lost"
    unless (row.getObjValAs? String "goal_module").toOption.any (·.endsWith "Goals") do
      throwError "a missing companion did not identify its importable goal module"
    unless (row.getObjValAs? String "stub_text").toOption.any (·.contains goal.getString!) do
      throwError "a missing companion did not supply a usable alias-based stub"
  -- A valid fallback is available, but a present wrong explicit companion
  -- must refuse before that fallback or the correct template can run.
  let wrongIdentity := subject.implementationKey (label ++ "-wrong-control")
  modifyEnv fun environment => registrations.addEntry environment ⟨wrongIdentity, wrongProof⟩
  let (wrong, wrongRow) ← attempt
    { request with selections := #[⟨wrongIdentity, #[]⟩] } expected #[fallback]
  unless (match wrong with | .refused _ attempts => attempts.size == 1 | _ => false) do
    throwError "a wrong real source companion fell back to a valid consumer"
  unless (wrongRow.getObjValAs? String "closed_expected_type").toOption ==
      some (toString (← withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr expected))) do
    throwError "a wrong candidate changed the independently fixed root type"
  -- Ordinary registered proofs are also accepted at that same fixed type.
  let explicitIdentity := subject.implementationKey (label ++ "-explicit-control")
  modifyEnv fun environment => registrations.addEntry environment ⟨explicitIdentity, proof⟩
  let (selected, _) ← attempt { request with selections := #[⟨explicitIdentity, #[]⟩] } expected #[]
  unless (match selected with | .discharged _ _ _ => true | _ => false) do
    throwError "a real source companion was not selected at its original type"
  let (imported, _) ← attempt
    { request with identity := identity, selections := #[⟨identity, #[]⟩] } expected #[]
  unless (match imported with | .discharged _ _ _ => true | _ => false) do
    throwError "the imported ordinary companion was not registered for generated assembly"
  let (external, _) ← attempt { request with
    selections := #[⟨"SourcePropertyModules/" ++ original.getString!, #[]⟩] } expected #[]
  unless (match external with | .discharged _ _ _ => true | _ => false) do
    throwError "an external author module could not prove the independent imported goal"
  for declaration in [original, proof, goal] do
    for dependency in ← collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "nonstandard axiom in an actual source consumer: {dependency}"
  logInfo m!"source property controls checked: {subject.owner}/{label}"

run_elab do
  let small ← sourceIdentity (← elabTerm (← `(term| source .small)) none)
  let two ← sourceIdentity (← elabTerm (← `(term| source .twoSums)) none)
  unless small.owner == "sumcheck::Sumcheck" && two.owner == "sums::TwoSums" &&
      small.symbol != two.symbol && small.capture.startsWith "sha256:" do
    throwError "source identity differs from the retained original declarations"
  let missingOrigin ← Term.withoutErrToSorry <| elabTerm (← `(term|
    ({ source .small with snapshot :=
      { (source .small).snapshot with definitions :=
        (source .small).snapshot.definitions.map fun
          | .function function => .function { function with origin := none }
          | definition => definition } } : Zkc.Source.Structured.Program))) none
  let refused ← try
    let _ ← sourceIdentity missingOrigin
    pure false
  catch _ => pure true
  unless refused do throwError "a missing retained origin was replaced by an invented source identity"

run_elab do
  checkConsumer (← `(term| source .small)) "honest-pair"
    ``ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small_goal
    ``ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small ``smallPair ``smallNo

run_elab do
  checkConsumer (← `(term| source .twoSums)) "honest-pair"
    ``ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.two_goal
    ``ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.two ``twoPair ``twoNo

run_elab do
  checkConsumer (← `(term| source .small)) "public-rejection"
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_no_goal
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_no ``smallNo ``smallPair

run_elab do
  checkConsumer (← `(term| source .twoSums)) "public-rejection"
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no_goal
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no ``twoNo ``twoPair

run_elab do
  checkConsumer (← `(term| source .small)) "public-cost"
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_cost_goal
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_cost ``smallCost ``smallPair

run_elab do
  checkConsumer (← `(term| source .twoSums)) "public-cost"
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_cost_goal
    ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_cost ``twoCost ``twoPair


-- Exercise the real term integration and its automatic binder substitution.
-- Only the registered companion can discharge these attempts.
example : ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small_goal := by
  unfold ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small_goal
  repeat intro
  exact source_property for (source .small) :
    ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small_goal
    with "honest-pair" companions [] via True.intro

noncomputable example : ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no_goal := by
  unfold ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no_goal
  repeat intro
  exact source_property for (source .twoSums) :
    ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no_goal
    with "public-rejection" companions [] via True.intro
