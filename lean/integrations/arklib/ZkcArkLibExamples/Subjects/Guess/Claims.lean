module

public import ZkcSecurityTools.ClaimConstruction
public import ZkcArkLibExamples.Subjects.Guess.Registration
public meta import ZkcArkLibExamples.Subjects.Guess.Registration

@[expose] public section

/-! Generated source requests and typed receipts. Regenerate with `lean/bridges/subject.py --write`. Typed library exports fix the subject and registry; source requests select the property and method. -/

namespace ZkcSecurity.Examples.Subjects.Guess
open Zkc.Claims ZkcSecurity.Tools.ClaimConstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact source request; attachment and method are separate. -/
def request0Data : Wire.Request :=
{
  subject := ⟨"sha256:dea6164686baa075f96720ff33aa38d59a239c82625cad71284ae69a1144ad49", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", .compiledIdeal, [⟨"constructed-participant", "sha256:71e385628aa6bd7e9907e81864a8db7636f1c326a5b103e2813f2bb9c8c3ee2a"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .importedLanguage "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748" ⟨⟨"languages.guess", 0⟩, []⟩
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 1)) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))
  capabilities := []
}

def request0Method : Option Wire.Application := some ⟨⟨"fs.keyed_soundness", 0⟩, []⟩

claim_request request0Data using Registration.library method request0Method

/-- Exact source request; attachment and method are separate. -/
def request1Data : Wire.Request :=
{
  subject := ⟨"sha256:dea6164686baa075f96720ff33aa38d59a239c82625cad71284ae69a1144ad49", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", .compiledIdeal, [⟨"constructed-participant", "sha256:71e385628aa6bd7e9907e81864a8db7636f1c326a5b103e2813f2bb9c8c3ee2a"⟩]⟩
  property := ⟨"soundness", 0⟩
  parameters := none
  model := ⟨⟨"models.fiat_shamir", 0⟩, [(some "level", (.reference "levels.ideal")), (some "statement", (.reference "statements.adaptive")), (some "oracle", (.application "oracles.random" (some 0) [(none, (.reference "construction.provider"))])), (some "queries", (.reference "Q")), (some "budget_symbol", (.reference "Q")), (some "validator_cost", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))]))), (some "application", (.reference "application"))]⟩
  target := .importedLanguage "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748" ⟨⟨"languages.guess", 0⟩, []⟩
  accept := ⟨true, 0, 1, []⟩
  quantity := .charged [("challenge", (.binary .div (.natural 1) (.application "cardinality" none [(none, (.reference "bls12-381.fr"))])))]
  capabilities := []
}

def request1Method : Option Wire.Application := some ⟨⟨"fs.keyed_charged", 0⟩, []⟩

claim_request request1Data using Registration.library method request1Method

end ZkcSecurity.Examples.Subjects.Guess
