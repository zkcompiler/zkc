import ZkcFormalTests.WrittenSubject

/-! Check imported author interfaces on modules issued from small source programs. -/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject

namespace WrittenGoalAuthors

private def guardSource := "module truth
use zkc::security::{soundness}
relation IsSet(bit: bool): bit
protocol Check roles(P,V)(hidden: bool @P, x: bool @(P,V), y: bool @(P,V)):
    guard @V x
spec for Check:
    proves @V IsSet(x)
scheme Checked = Check:
    prover P
    construction interactive
goal sound = soundness(Checked)
"

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

private def emptySource := "module empty
use zkc::security::{soundness}
relation Never(): false
protocol Check roles(V,P)():
    guard @V false
spec for Check:
    proves @V Never()
scheme S = Check:
    prover P
    construction interactive
goal emptyGoal = soundness(S)
"

private def guardProof := "
theorem identityLaw (x : Bool) : functionResult (t := .bool)
    (fnMeaning model installed soundMember (.cons x .nil)) = some x := by kernel_rfl

theorem sound_witnessed : soundWitnessed := sound_witnessed_of false trivial true trivial (identityLaw false)
"

private def multiProof (label : String) := s!"
theorem {label}_witnessed : {label}Witnessed :=
  {label}_witnessed_of true trivial false trivial (fun b n _ _ => acceptsLaw false b n)
"

private def acceptsLaw := "
theorem acceptsLaw (x b : Bool) (n : Nat) : functionResult (t := .bool)
    (fnMeaning model installed mappedMember (.cons x (.cons b (.cons n .nil)))) =
      some (x && (b || (n == 0))) := by kernel_rfl
"

private def emptyProof := "
theorem neverLaw : functionResult (t := .bool) (fnMeaning model installed emptyGoalMember .nil) =
    some false := by kernel_rfl
theorem emptyGoal_witnessed : emptyGoalWitnessed := emptyGoal_witnessed_of neverLaw
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

private def issue (s : Statements) (name proof : String) : IO Written.Module := do
  let m ← IO.ofExcept (s.module name { text := proof })
  unless m.refusals.isEmpty do throw <| IO.userError s!"{name}: {m.refusals}"
  return m

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
  let ports := #["hidden", "x", "y"]
  let good ← issue (← statements guardSource ["sound"] ports) "AuthorGuard" guardProof
  let swapped ← replaceOnce guardSource "proves @V IsSet(x)" "proves @V IsSet(y)"
  let wrong ← issue (← statements swapped ["sound"] ports) "AuthorSwap" ""
  let multiPorts := #["claim", "flag", "right", "n"]
  let multi ← issue (← statements multiSource ["mapped", "omitted"] multiPorts)
    "AuthorMulti" (acceptsLaw ++ multiProof "mapped" ++ multiProof "omitted")
  let empty ← issue (← statements emptySource ["emptyGoal"] #[]) "AuthorEmpty" emptyProof
  let impossible ← IO.ofExcept ((← statements multiSource ["equality"] multiPorts)
    |>.claimsModule "AuthorEquality")
  unless impossible.refusals.isEmpty do throw <| IO.userError s!"equality: {impossible.refusals}"
  let equality ← startLakeLean work "AuthorEquality" impossible.text (text := false)
  let swap ← addStated work wrong
  let proofs ← [(good, guardProof), (multi, acceptsLaw ++ multiProof "mapped" ++ multiProof "omitted"),
      (empty, emptyProof)].mapM fun (m, body) => do
    let names := (m.published.map (·.1.getString!)).filter (·.endsWith "_met")
    let closings := (m.proof.splitOn "\n").filter fun line =>
      names.any fun n => line.startsWith s!"theorem {n} :"
    startLemmas work m.space m (body ++ "\n".intercalate closings) names

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
  let audited := ["disagreement", "refuted", "zeroMet", "zeroHelper", "mappedMet", "mappedHelper",
    "omittedMet", "omittedHelper", "emptyMet", "emptyHelper", "publicNames", "noEqualityReceipt", "fromGoal", "fromResult"]
  let requests := String.join (audited.map (s!"#print axioms AuthorClient.{·}\n"))
  let externalClient ← startLakeLean work "AuthorClient" (client ++ "\n" ++ requests)
  swap.accepted "AuthorSwap"
  for check in proofs do check
  acceptedByLean "AuthorEquality" (← equality)
  for check in hashCalls ++ alphaCalls do check
  let (ok, output) ← externalClient
  acceptedOutput "AuthorClient" ok output audited allowed

end WrittenGoalAuthors

#eval show IO Unit from do
  let hash ← IO.FS.readFile "fixtures/hash-relation.zkc"
  let client ← IO.FS.readFile "checks/WrittenGoalAuthors.lean.in"
  IO.FS.withTempDir fun work => WrittenGoalAuthors.run work hash client
