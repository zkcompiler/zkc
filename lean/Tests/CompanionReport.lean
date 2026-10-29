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
