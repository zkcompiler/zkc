import ZkcFormalTests.WrittenSubject

/-! Check imported author interfaces on modules issued from small source programs. -/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject

namespace WrittenGoalAuthors

private def multiSource := "module probes
use zkc::security::{soundness}
relation Accepts(x: bool; flag: bool, n: nat): x and (flag or n == 0)
relation Matches(x: bool; flag: bool): x == flag
protocol Check roles(P,V)(claim: bool @(P,V), flag: bool @P, right: bool @(P,V), n: nat @P):
    guard @V right
spec for Check:
    proves @V explicit: Accepts(right; flag, n)
    proves @V short: Accepts(right)
    proves @V reflected: Matches(right; flag)
scheme S = Check:
    prover P
    construction interactive
goal mapped = soundness(S, clause = explicit)
goal omitted = soundness(S, clause = short)
goal equality = soundness(S, clause = reflected)
"

private def statements (source : String) (labels : List String)
    (ports : Array String) : IO Statements := do
  let first :: _ := labels | throw <| IO.userError "expected a goal selector"
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" source⟩
    ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly first)
  let claims ← IO.ofExcept (goalClaims root labels)
  unless claims.inputs == ports do throw <| IO.userError s!"unexpected deployed ports for {labels}"
  return ⟨claims, claims.functionsBeforeRoot⟩

-- Both applications are checked against the same positional conclusion. In particular a
-- permutation of equal-typed visible inputs must preserve which value is sent to the relation.
private def aliasCall (label keyword other binders otherInput : String) := s!"
example (h : {label}Claim) : {label}Claim := by
  intro path {binders} rejected
  fail_if_success have _ := h ({other} := value)
  exact h ({keyword} := value) {otherInput} path hfirst hsecond rejected
"

private def aliases (work : System.FilePath) (source short qualified encoded : String)
    (ports : Array String) (ordinal natural binders otherInput : String) (space : String) :
    IO (List (IO Unit)) := do
  let mut results := []
  for (order, suffix) in [([short, qualified], "ShortFirst"), ([qualified, short], "LongFirst")] do
    let name := space ++ suffix
    let s ← statements source order ports
    let m ← IO.ofExcept (s.claimsModule name)
    unless m.refusals.isEmpty do throw <| IO.userError s!"{name}: {m.refusals}"
    let issued ← startLakeLean work name m.text (text := false)
    let calls := aliasCall short ordinal natural binders otherInput ++
      aliasCall encoded natural ordinal binders otherInput
    let client ← startLakeLean work (name ++ "Client")
      (s!"import {name}\nnamespace {name}Client\nopen {name}\n" ++
        s!"example : written'origins.inputNames = {reprStr ports} := rfl\n" ++ calls ++ s!"end {name}Client\n")
      (text := false)
    results := results ++ [do
      acceptedByLean name (← issued)
      acceptedByLean (name ++ "Client") (← client)]
  return results

def run (work : System.FilePath) (hashSource client : String) : IO Unit := do
  let multiPorts := #["claim", "flag", "right", "n"]
  let impossible ← IO.ofExcept ((← statements multiSource ["equality"] multiPorts)
    |>.claimsModule "AuthorEquality")
  unless impossible.refusals.isEmpty do throw <| IO.userError s!"equality: {impossible.refusals}"
  let equality ← startLakeLean work "AuthorEquality" impossible.text (text := false)

  let mut hash := hashSource
  for (before, after) in [("goal good =", "goal input_b ="), ("(b: bool @(P,V)", "(bCaps: bool @(P,V)"),
      ("guard @V b", "guard @V bCaps"), ("Holds(b, xs)", "Holds(bCaps, xs)")] do
    hash ← replaceOnce hash before after
  let hashCalls ← aliases work hash "input_b" "mixed::input_b" "goal'mixed'58''58'input'95'b"
    #["bCaps", "xs"] "port0" "input_bCaps" "value hfirst xs hsecond" "(input_xs := xs)" "AuthorHash"
  let alpha := (multiSource.replace "right" "alphaCaps").replace "goal mapped =" "goal input_alpha ="
  let alphaCalls ← aliases work alpha "input_alpha" "probes::input_alpha"
    "goal'probes'58''58'input'95'alpha" #["claim", "flag", "alphaCaps", "n"] "port2" "input_alphaCaps"
    "claim hfirst value hsecond" "(input_claim := claim)" "AuthorAlpha"
  let audited := ["noEqualityReceipt"]
  let requests := String.join (audited.map (s!"#print axioms AuthorClient.{·}\n"))
  let externalClient ← startLakeLean work "AuthorClient" (client ++ "\n" ++ requests)
  acceptedByLean "AuthorEquality" (← equality)
  for check in hashCalls ++ alphaCalls do check
  let (ok, output) ← externalClient
  acceptedOutput "AuthorClient" ok output audited allowed

end WrittenGoalAuthors

#eval show IO Unit from do
  let hash ← IO.FS.readFile "fixtures/hash-relation.zkc"
  let client ← IO.FS.readFile "checks/WrittenGoalAuthors.lean.in"
  IO.FS.withTempDir fun work => WrittenGoalAuthors.run work hash client
