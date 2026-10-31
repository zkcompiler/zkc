import ZkcTools.Companions.Report

set_option autoImplicit false
open Lean ZkcTools.Companions

private def first : Stub := ⟨"Sumcheck/round/honest.entry", `sumcheck_entry, `Generated.Sumcheck.entry, .proof⟩
private def contract : Stub := ⟨"Sumcheck/round", `sumcheck_contract, `Generated.Sumcheck.contract, .value⟩
private def original := "-- Authored text must remain unchanged.\n"
private def once := (appendStubs original #[first]).toOption.getD "refused"
#guard original.isPrefixOf once
#guard (appendStubs once #[first]).toOption == some once
#guard (appendStubs once #[first, contract]).toOption.any (once.isPrefixOf ·)
#guard (contract.render.toOption.getD "").contains "-- noncomputable def"
#guard !(contract.render.toOption.getD "").contains "\nnoncomputable def"
#guard (appendStubs original #[first, { first with goal := `Different.goal }]).toOption.isNone
#guard (appendStubs original #[first, { contract with declaration := first.declaration }]).toOption.isNone
#guard ({ first with declaration := .str .anonymous "bad\nname" } : Stub).render.toOption.isNone
-- A later regeneration cannot overwrite an existing proof or stale goal.
#guard (appendStubs once #[{ first with goal := `Changed.goal }]).toOption == some once

open Lean Elab Command Term Meta in
run_elab do
  let expected := Lean.mkConst ``True
  let result ← assemble #[] expected #[⟨"wrong-type", ← `(term| (0 : Nat))⟩]
  let record ← report {
    identity := "Sumcheck/round/honest.entry"
    responsibility := "family mathematics"
    expected
    source := some ⟨"sumcheck.zkc", 12, 3, 19, 4⟩
    stub := some ⟨"SumcheckCompanion.lean", 8⟩ } result
  unless (record.getObjValAs? String "status").toOption == some "open" do
    throwError "an unsupported obligation did not remain open"
  unless (record.getObjValAs? String "identity").toOption == some "Sumcheck/round/honest.entry" do
    throwError "a proof-search address replaced the source identity"
  unless (record.getObjVal? "default_attempts").toOption.any fun value =>
      value.getArr?.toOption.any (·.size == 1) do
    throwError "the default refusal was not reported"

-- Generated scaffolding really parses and elaborates, including keyword names.
def Generated.Sumcheck.entry : Prop := True

/-- The hypothesis must remain visible even though the conclusion's expression
does not contain its proof variable. -/
def Generated.withPremise : Prop := ∀ (α : Type) (x : α), x = x → x = x
def Generated.withoutPremise : Prop := ∀ (α : Type) (x : α), x = x

universe u v
section GeneratedGoal
variable (unused : Type v) (α : Type u) [Inhabited α] (premise : True)
include premise

companion_goal Generated.polymorphic in
theorem generatedPolymorphic {β : Type v} (x : β) (h : x = x) : x = x := by
  run_tac Lean.Elab.Tactic.withMainContext do
    validateGoal (← Lean.Elab.Tactic.getMainTarget) ``Generated.polymorphic
  have _included := premise
  exact h
end GeneratedGoal

/-- error: companion_goal requires a single theorem or definition -/
#guard_msgs in
companion_goal unsupportedGoal in
example : True := True.intro

/-- error: companion_goal requires an explicit independently fixed type -/
#guard_msgs in
companion_goal inferredGoal in
def inferredValue := 1

open Lean Elab Command Term Meta in
run_elab do
  let expected ← mkFreshExprMVar (some (mkSort .zero))
  let refused ← try
    validateGoal expected ``Generated.withPremise
    pure false
  catch _ => pure true
  unless refused do throwError "an unresolved expected proposition was accepted"

-- A dependent let is retained as a let, rather than an extra proof premise.
open Lean Elab Command Term Meta in
run_elab do
  let goal ← whnf (mkConst ``Generated.withPremise)
  forallTelescope goal fun binders _ => do
    withLetDecl `copy (← inferType binders[1]!) binders[1]! fun copy => do
      let expected ← mkEq copy binders[1]!
      let row ← report {
        identity := "ReportControl/dependent-let", responsibility := "mathematics", expected }
        (.openObligation "missing lemma" #[])
      let .ok context := (row.getObjVal? "context").bind Json.getArr?
        | throwError "missing dependent-let context"
      unless context.size == 4 && (context.back!.getObjVal? "value").toOption != some Json.null do
        throwError "a dependent let was lost from the full telescope"
      unless (row.getObjValAs? String "closed_expected_type").toOption.any (·.contains "let") do
        throwError "a let dependency was replaced by an unconstrained parameter"

open Lean Elab Command Term Meta in
run_elab do
  let goal ← whnf (mkConst ``Generated.withPremise)
  forallTelescope goal fun binders expected => do
    let request : Obligation := {
      identity := "ReportControl/dependent-premise"
      responsibility := "family mathematics"
      expected
      goal := some ``Generated.withPremise }
    let record ← report request (.openObligation "author lemma required" #[])
    let .ok context := (record.getObjVal? "context").bind Json.getArr?
      | throwError "missing reported local telescope"
    unless context.size == binders.size && context.size == 3 do
      throwError "the report dropped a dependent parameter or premise"
    unless (record.getObjValAs? String "goal_declaration").toOption ==
        some "Generated.withPremise" do
      throwError "the checked goal declaration was omitted"
    let refused ← try
      let _ ← report { request with goal := some ``Generated.withoutPremise }
        (.openObligation "author lemma required" #[])
      pure false
    catch _ => pure true
    unless refused do
      throwError "a generated goal with a different premise telescope was accepted"

open Lean Elab Command Term Meta in
run_cmd do
  let wanted : Stub := { first with declaration := .str .anonymous "match" }
  let .ok text := wanted.render | throwError "valid generated stub was refused"
  for line in text.splitOn "\n" do
    unless line.isEmpty || line.startsWith "--" do
      let .ok parsed := Parser.runParserCategory (← getEnv) `command line
        | throwError "generated proof stub did not parse"
      elabCommand parsed
  liftTermElabM do
    let result ← resolve #[⟨wanted.identity, #[]⟩] (Lean.mkConst ``True)
    unless (match result with | .incomplete _ _ _ => true | _ => false) do
      throwError "a generated unfinished stub did not remain open"
