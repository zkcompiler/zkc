import ZkcFormalTests.WrittenSubject
import Zkc.Tools.Frontend.WrittenGoals
import Zkc.Tests.Frontend.SyntaxHarness

/-! Read independently chosen source coordinates through the actual imported publication.
The controls change the issuance. Their clients keep the original source and selectors. -/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend
open PrintedPackageSupport ZkcFormalTests.WrittenSubject

private abbrev Requests := List (String × String)
private abbrev Check := IO Unit

private def expect {α : Type} [BEq α] [Repr α] (what : String) (actual expected : α) : IO Unit :=
  unless actual == expected do throw (IO.userError s!"{what}: got {repr actual}, expected {repr expected}")

private def simple (ns : List String) : Requests := ns.map fun n => (n, n)

private def statements (root : AdmittedRoot) (selectors : List String) : IO Statements := do
  let raw ← IO.ofExcept (goalClaims root selectors)
  expect "original occurrences" (raw.goals.map (·.goal)) selectors
  return ⟨raw, raw.functionsBeforeRoot⟩

private def readSource (src : String) (req : Requests) : IO Statements := do
  let (first, _) :: _ := req | throw (IO.userError "empty request")
  statements (← IO.ofExcept (goalRoot src first)) (req.map Prod.fst)

private def publication (m : Module) (labels : List String) : IO Unit := do
  let suffixes := [("_installed", "Claim"), ("_sound", "Goal"), ("_result", "Result"),
    ("_met", "Witnessed")]
  let name := fun (s : String) => Lean.Name.str m.space.toName s
  expect "published theorem/proposition pairs" m.published (labels.flatMap fun l =>
    suffixes.map fun (t, p) => (name (l ++ t), name (l ++ p)))

private def issued (work : System.FilePath) (file space body : String) (thms : List String := []) :
    IO Check := do
  let pending ← startLakeLean work file body (text := false)
  return do
    let (ok, out) ← pending
    acceptedOutput space ok out thms allowed

private def client (file space checks : String) : String :=
  s!"import {file}\nimport ZkcFormalTests.WrittenBinding\nopen ZkcFormal.Written\n" ++
    s!"namespace {space}\n{checks}\nend {space}\n"

private def eqn (lhs rhs : String) : String := s!"example : {lhs} = {rhs} := rfl\n"

private def atGoal (i : Nat) := s!"(written'subject.goalAt ⟨{i}, by decide⟩)"

private def coordinates (i place key : Nat) (xs : List Nat) (ws : Option (List Nat)) : String :=
  eqn s!"ZkcFormalTests.WrittenBinding.operands {atGoal i}"
    s!"({place}, {key}, {xs.length}, {reprStr xs}, {reprStr ws})"

private def refs (label : String) (i d : Nat) (fees : Bool) :=
  s!"run_cmd ZkcFormalTests.WrittenBinding.checkReferences (← Lean.getCurrNamespace) {reprStr label} {i} {d} {fees}\n"

private def sizes (goals decisions : Nat) :=
  eqn "written'subject.goals.size" (toString goals) ++
    eqn "written'subject.clauses.size" (toString decisions)

private def roles (root prover verifier : Nat) :=
  eqn "(written'root.entry.header.key.number, written'root.prover.val, written'root.verifier.val)"
    s!"({root}, {prover}, {verifier})"

private def fields (i : Nat) (args : List Nat) (table ceiling : String) :=
  eqn s!"{atGoal i}.fields" s!"⟨{reprStr args}, {table}, {ceiling}⟩"

private def flat (root : Nat) (draws := "[]") := s!"⟨[.flat ⟨{root}⟩ {draws} []]⟩"

private def full (work : System.FilePath) (space src : String) (req : Requests)
    (gold : String) : IO (Module × Check) := do
  let s ← readSource src req
  let m ← IO.ofExcept (s.module space {})
  expect space m.refusals []
  publication m ((req.map Prod.snd).eraseDups)
  let check ← issued work m.statementsName.toString space m.statements m.stated
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req true)
  let indices := List.range (s.claims.goals.map (·.declaration)).eraseDups.length
  let lookups := indices.map fun i => s!"written'goalAt{i}"
  let equations := String.join ((indices.zip lookups).map fun (i, thm) =>
    s!"example : {atGoal i} = written'goal{i} := {thm}\n#print axioms {thm}\n")
  let compare ← issued work (space ++ "Source") space
    (client m.statementsName.toString space (original ++ gold ++ equations)) lookups
  return (m, check *> compare)

/-- The public caps of fact-only routes have one declaration per spelling, including aliases.
Read their names in order, and count the separate canonical fields and located functions. -/
private def checkLayout (text : String) (labels : List String) (rows functions : Nat) : IO Unit := do
  let names := (text.splitOn "\n").filterMap fun line => match line.splitOn " " with
    | "noncomputable" :: "def" :: n :: _ => some n
    | "def" :: n :: _ | "abbrev" :: n :: _ => some n
    | _ => none
  expect "public cap names" (names.filter (·.endsWith "Caps")) (labels.map (· ++ "Caps"))
  expect "one group of fields per declaration" (names.filter (·.startsWith "written'fields")).length rows
  expect "located functions" (names.filter (·.startsWith "written'fn")).length functions

private def qualifiedLeft := "goal'operands'58''58'left"
private def aliases : Requests :=
  [("left", "left"), ("operands::left", qualifiedLeft), ("left", "left"),
   ("left_again", "left_again"), ("right", "right")]

private def aliasCase (work : System.FilePath) (src : String) (reverse : Bool) :
    IO (Module × Check) := do
  let (space, req, selections, ports) := if reverse then
      ("Backward", aliases.reverse, [("right",0,0), ("left_again",1,1), ("left",2,1),
        (qualifiedLeft,2,1)], [(1,3),(0,2),(0,2)])
    else ("Forward", aliases, [("left",0,0), (qualifiedLeft,0,0), ("left_again",1,0),
        ("right",2,1)], [(0,2),(0,2),(1,3)])
  let gold := sizes 3 2 ++ roles 1 0 1 ++ String.join (ports.zipIdx.map fun ((p,x),i) =>
    coordinates i p 0 [x] (some [0]) ++ fields i [] (flat 1) "none")
  let (m, check) ← full work space src req
    (gold ++ String.join (selections.map fun (l,i,d) => refs l i d true))
  let s ← readSource src req
  let labels := selections.map Prod.fst
  checkLayout m.statements labels 3 1
  let claims ← IO.ofExcept (s.claimsModule (space ++ "Claims"))
  let coverage ← IO.ofExcept (s.coverageModule (space ++ "Coverage"))
  let ceilings ← IO.ofExcept (s.ceilingModule (space ++ "Ceilings"))
  expect "alias coverage names" coverage.theorems (labels.map (· ++ "_covered"))
  for (plain, functions) in [(claims,1), (coverage,0), (ceilings,0)] do
    expect "alias route refusals" plain.refusals []
    checkLayout plain.text labels 3 functions
  let claimsName := space ++ "Claims"
  let claimModule ← issued work claimsName claimsName claims.text claims.theorems
  let compare ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req false)
  let claimClient ← issued work (claimsName ++ "Source") claimsName
    (client claimsName claimsName compare)
  return (m, check *> claimModule *> claimClient)

/-- Match each failure to a unique command in the unchanged source consumer and check the
diagnostic on that line. A malformed mutant, failed import, or additional error fails the test. -/
private def checkMutant (work : System.FilePath) (m : Module) (tag changed original : String)
    (failures : List (String × String)) : IO Check := do
  let file := tag ++ ".Stated"
  let check ← issued work file m.space changed m.stated
  let body := client file m.space original
  let checkFile := tag ++ "Source"
  let pending ← startLakeLean work checkFile body (text := false)
  return do
    check
    let (ok, log) ← pending
    expect s!"{tag}: consumer accepted" ok false
    let errors := (log.splitOn "\n").filter fun l => l.contains ": error:" || l.contains ": error("
    expect s!"{tag}: diagnostic count\n{log}" errors.length failures.length
    for (command, reason) in failures do
      let [(_, i)] := (body.splitOn "\n").zipIdx.filter fun (line, _) => line.contains command
        | throw (IO.userError s!"{tag}: expected one consumer command containing {command}")
      unless errors.any (fun e => e.contains s!"{checkFile}.lean:{i+1}:" && e.contains reason) do
        throw (IO.userError s!"{tag}: expected {reason} on {command}\n{log}")

private def controls (work : System.FilePath) (m : Module) (src : String) : IO (List Check) := do
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src aliases true)
  let mutate := replaceOnce m.statements
  let run := fun tag body => checkMutant work m tag body original
  let changed ← mutate "left_againClaim : Prop := left_againClaimOf"
    "left_againClaim : Prop := leftClaimOf"
  let refAt := fun (l : String) => s!"checkReferences (← Lean.getCurrNamespace) {reprStr l} "
  let wrong := fun want got => s!"expected the reference {m.space}.{want}, found {got}"
  let claim ← run "Redirect" changed [(refAt "left_again", wrong "left_againClaimOf" "leftClaimOf")]
  let slot (i d f : Nat) := s!"written'slot{i} : Zkc.Subject.GoalSlot written'clauses.size := ⟨⟨{d}, by decide⟩, written'fields{f}⟩"
  let swapped ← mutate (slot 0 0 0) (slot 0 0 1)
  let swapped ← replaceOnce swapped (slot 1 0 1) (slot 1 0 0)
  let swap ← run "SwapFields" swapped [
    (refAt "left", wrong "written'fields0" "written'fields1"),
    (refAt qualifiedLeft, wrong "written'fields0" "written'fields1"),
    (refAt "left_again", wrong "written'fields1" "written'fields0")]
  -- Only the right decision uses the fourth port. Both candidate ports are shared Booleans.
  let third := "(Member.tail (Member.tail Member.head))"
  let fourth := s!"(Member.tail {third})"
  let moved ← mutate s!"⟨⟨_, {fourth}⟩, by decide +kernel" s!"⟨⟨_, {third}⟩, by decide +kernel"
  let operand ← run "MoveOperand" moved [(s!"WrittenBinding.operands {atGoal 2}", "Type mismatch")]
  -- Route left_again to a new physical copy. All three dereferenced goals keep their values.
  let table := "⟨2, fun i => (if i.val < 1 then written'decision0 else written'decision1)⟩"
  let dupTable := "⟨3, fun i => (if i.val < 1 then written'decision0 else " ++
    "(if i.val < 2 then written'decision1 else written'decision2))⟩"
  let marker := "noncomputable def written'clauses :"
  let decl := "noncomputable def written'decision"
  let [_, tail] := m.statements.splitOn (decl ++ "0 :")
    | throw (IO.userError "expected decision 0")
  let [body, _] := tail.splitOn (decl ++ "1 :") | throw (IO.userError "expected decision 1")
  let dup ← mutate marker (decl ++ "2 :" ++ body ++ marker)
  let dup ← replaceOnce dup table dupTable
  let dup ← replaceOnce dup (slot 1 0 1) (slot 1 2 1)
  let dup ← replaceOnce dup "⟨written'decision0, written'fields1⟩" "⟨written'decision2, written'fields1⟩"
  let duplicate ← run "DuplicateRow" dup [("⟨1, by decide⟩).clause.val", "Type mismatch"),
    (refAt "left_again", wrong "written'decision0" "written'decision2"),
    ("written'subject.clauses.size =", "Type mismatch")]
  return [claim, swap, operand, duplicate]

private def aliasChecks (work : System.FilePath) : IO Unit := do
  let src ← IO.FS.readFile "fixtures/written-decisions.zkc"
  let (m, forward) ← aliasCase work src false
  let (_, backward) ← aliasCase work src true
  let mutants ← controls work m src
  forward
  backward
  mutants.forM id

private def occurrences := "module coordinates
use zkc::security::{soundness}
relation First(a: bool, b: bool, c: bool; w: bool, u: bool): a
protocol Check roles(V,P)(secret: bool @P, x: bool @(P,V), y: bool @(V,P), second: bool @P):
    guard @V x
spec for Check:
    proves @V a: First(y, x, x; secret, second)
    proves @V b: First(x, y, x; second, secret)
    proves @V copy: First(y, x, x; secret, second)
    proves @V short: First(y, x, x)
scheme Checked = Check:
    prover P
    construction interactive
goal left = soundness(Checked, clause = a)
goal right = soundness(Checked, clause = b)
goal twin = soundness(Checked, clause = copy)
goal again = soundness(Checked, clause = a)
goal short = soundness(Checked, clause = short)
"

private def tenancy := "module tenancy
use zkc::security::{soundness}
relation Holds(bit: bool): bit
section <spec e: nat>:
    protocol Check roles(P,V)(x: bool @(P,V)):
        z <- draw index<2> from V to P
        guard @V x
    spec for Check:
        charge sites.z <= 1 / (e + 1)
        proves @V first: Holds(x)
        proves @V clone: Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal a = soundness(Checked, clause = first, spec e = 1) <= 1
goal b = soundness(Checked, clause = first, spec e = 3) <= 1/2
goal c = soundness(Checked, clause = clone, spec e = 1) <= 1
"

private def zero := "module zero
use zkc::security::{soundness}
relation No(): false
protocol Check roles(V,P)():
    guard @V false
spec for Check:
    proves @V No()
scheme Checked = Check:
    prover P
    construction interactive
goal z = soundness(Checked)
"

private def countSource : IO String := do
  let blocks := readBlocks (← IO.FS.readFile "../../language/conformance/layer-b.txt")
  let some src := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing Count N-GL2a")
  return src

private def coordinateChecks (work : System.FilePath) : IO Unit := do
  let add := fun name src labels gold => Prod.snd <$> full work name src (simple labels) gold
  let count ← add "CountRows" (← countSource) ["loose","strict"]
    (sizes 2 2 ++ roles 1 0 1 ++ coordinates 0 0 3 [0] (some []) ++
     coordinates 1 0 4 [0] (some []) ++ fields 0 [4] (flat 1 "[⟨⟨0⟩, 3, 8, 1⟩]") "none" ++
     fields 1 [1] (flat 1 "[⟨⟨0⟩, 3, 4, 1⟩]") "none")
  let shared ← add "ChargedRows" tenancy ["a","b","c"] (sizes 3 2 ++ String.join
    ([(1,1,2,"some (1/1)"), (1,3,4,"some (1/2)"), (2,1,2,"some (1/1)")].zipIdx.map
      fun ((place,e,den,cap),i) => coordinates i place 0 [0] (some []) ++
        fields i [e] (flat 1 s!"[⟨⟨0⟩, 1, {den}, 1⟩]") cap))
  let reps ← add "Occurrences" occurrences ["left","right","twin","again","left"]
    (sizes 4 3 ++ roles 1 1 0 ++ String.join ([
      (0,0,[2,1,1],[0,3]), (1,1,[1,2,1],[3,0]), (2,2,[2,1,1],[0,3]),
      (3,0,[2,1,1],[0,3])].map fun (i,p,x,w) => coordinates i p 0 x (some w)) ++
      refs "again" 3 0 true)
  let short ← add "ShortWitness" occurrences ["short"] (coordinates 0 3 0 [2,1,1] none)
  let slots ← IO.FS.readFile "fixtures/written-decisions.zkc"
  let mapped ← add "WitnessPorts" slots ["left","other_witness","implicit_witness"]
    (coordinates 0 0 0 [2] (some [0]) ++ coordinates 1 3 0 [2] (some [1]) ++
      coordinates 2 2 0 [2] none ++ eqn "leftClaim" "other_witnessClaim")
  let mut bare := []
  for (name,src,p,v) in [("EmptyRoles",zero,1,0),
      ("TurnedRoles",(zero.replace "prover P" "prover V").replace "@V" "@P",0,1)] do
    let raw ← readSource src (simple ["z"])
    expect "raw zero-input scheme" (raw.claims.inputs.size, raw.claims.prover, raw.claims.verifier)
      (0,p,v)
    let req := simple ["z"]
    let (m, good) ← full work name src req (roles 1 p v ++ coordinates 0 0 0 [] (some []))
    bare := good :: bare
    if name == "EmptyRoles" then
      let flipped ← replaceOnce m.statements "abbrev proverRole : Role := 1" "abbrev proverRole : Role := 0"
      let flipped ← replaceOnce flipped "abbrev verifierRole : Role := 0" "abbrev verifierRole : Role := 1"
      let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req true)
      let bad ← checkMutant work m "SwappedRoles" flipped original
        [("(written'root.prover.val, written'root.verifier.val)", "Type mismatch")]
      bare := bad :: bare
  (count :: shared :: reps :: short :: mapped :: bare).forM id

/-- Both tables pay 1/2 in total. Moving the fields to the sibling's cap table changes
which draw pays each fee. Check the complete source tree at the affected goal. -/
private def capChecks (work : System.FilePath) : IO Unit := do
  let src ← replaceOnce tenancy "        guard @V x"
    "        t <- draw index<2> from V to P\n        guard @V x"
  let src ← replaceOnce src "charge sites.z <= 1 / (e + 1)"
    "charge sites.z <= e / 8\n        charge sites.t <= (4 - e) / 8"
  let req := simple ["a","b"]
  let draws := fun (z t : Nat) => flat 1 s!"[⟨⟨0⟩, {z}, 8, 1⟩, ⟨⟨1⟩, {t}, 8, 1⟩]"
  let (m, check) ← full work "EqualTotals" src req
    (fields 0 [1] (draws 1 3) "some (1/1)" ++ fields 1 [3] (draws 3 1) "some (1/2)" ++
     "example : aCaps.budget = bCaps.budget := a_budget.trans b_budget.symm\n")
  let swapped ← replaceOnce m.statements "⟨[3], written'caps1," "⟨[3], written'caps0,"
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req true)
  let bad ← checkMutant work m "ChangedCapTree" swapped original
    [(s!"{atGoal 1}.fields.caps =", "Type mismatch")]
  check
  bad

private def reduction := "module reduceexample
use zkc::security::{soundness}
relation Holds(b: bool): b
protocol C roles(P,V)(b: bool @(P,V)) -> r: bool @(P,V):
    return b
spec for C:
    reduces @V red: Holds(b) to Holds(r)
    proves @V pos: Holds(b)
scheme S = C:
    prover P
    construction interactive
goal red = soundness(S, clause = red)
goal pos = soundness(S, clause = pos)
"

private def refusal {α : Type} (why : String) (result : Except String α) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"expected refusal: {why}")
  | .error actual => expect "route diagnostic" actual why

private def factModule (work : System.FilePath) (name : String) (m : PlainModule)
    (labels : List String) (goals functions : Nat) (diagnostics : List String := []) : IO Check := do
  checkLayout m.text labels goals functions
  expect name m.refusals diagnostics
  issued work name name m.text m.theorems

private def routeEdges (work : System.FilePath) : IO Unit := do
  let red ← readSource reduction (simple ["red","pos"])
  let why := "red: the goal reads a `reduces` clause. The statement of a reduction " ++
    "is about a return on which the reduced statement is true, and is not issued yet"
  refusal why (red.module "Reduction" {})
  refusal why (red.claimsModule "Reduction")
  let covered ← IO.ofExcept (red.coverageModule "RedCoverage")
  expect "reduction coverage" covered.theorems ["red_covered","pos_covered"]
  let r ← factModule work "RedCoverage" covered ["red","pos"] 2 0
  let c ← factModule work "RedCeilings" (← IO.ofExcept (red.ceilingModule "RedCeilings"))
    ["red","pos"] 2 0
  let src := (← countSource) ++ "\ngoal low = soundness(Checked, spec e = 1) <= 0\n"
  let req := simple ["low","loose"]
  let low ← readSource src req
  let why := "GL4: the goal `low` states the ceiling 0, and the total of its charges is 3/4"
  refusal why (low.module "Low" {})
  refusal why (low.ceilingModule "Low")
  let l ← factModule work "LowClaims" (← IO.ofExcept (low.claimsModule "LowClaims"))
    ["low","loose"] 2 2
  let covered ← IO.ofExcept (low.coverageModule "LowCoverage")
  expect "low-ceiling coverage" covered.theorems ["low_covered","loose_covered"]
  let v ← factModule work "LowCoverage" covered ["low","loose"] 2 0
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req false)
  let check ← issued work "LowSource" "LowClaims" (client "LowClaims" "LowClaims" original)
  [r,c,l,v,check].forM id

private def hashDiagnostic (label : String) :=
  label ++ ": no interpretation of row (.inl (Zkc.Vocabulary.RowKey.hash (Zkc.Vocabulary.Hash.sha256)))"

/-- Exercise the same command handler used by written-goals, including its occurrence reports,
exit code, canonical directories and both files of each surviving publication. -/
private def cli (work : System.FilePath) (file : String) (selectors paths : List String)
    (success : List Bool) : IO Unit := do
  let assembly ← Driver.assembleFiles (← source file []) ["../../libraries"]
  let results := (issueSoundnessGoals assembly selectors).toList
  expect "CLI occurrences" (results.map (·.selector)) selectors
  expect "CLI canonical paths" (results.map (·.path)) (paths.map some)
  expect "CLI decisions" (results.map (·.outcome.isOk)) success
  let out := work / "published"
  let (report, code) ← IO.FS.withIsolatedStreams <| Zkc.Tools.Frontend.writtenGoals
    { files := #[file], libraries := #["../../libraries"], output := some out, goals := selectors.toArray }
  expect "CLI exit code" code (if success.all id then 0 else 1)
  let mut dirs := []
  let mut lines := []
  for (result,path) in results.zip paths do
    let prefix_ := s!"{result.selector} -> {path}: "
    match result.outcome with
    | .error why =>
      unless why.startsWith (file ++ ":") && why.endsWith (": " ++ hashDiagnostic "bad") do
        throw (IO.userError s!"expected a located SHA-256 refusal for canonical bad, got {why}")
      lines := lines ++ [prefix_ ++ "refused: " ++ why]
    | .ok ok =>
      let m := ok.publication
      let [g] := ok.statements.claims.goals | throw (IO.userError "expected one CLI goal")
      let dir := out / m.space
      expect "CLI statements" (← IO.FS.readFile (dir / "Stated.lean")) m.statements
      expect "CLI challenge" (← IO.FS.readFile (dir / "Challenge.lean")) m.challenge
      expect "CLI goal files" ((← dir.readDir).toList.map (·.fileName) |>.mergeSort)
        ["Challenge.lean", "Stated.lean"]
      dirs := dirs ++ [m.space]
      lines := lines ++ [prefix_ ++ s!"issued {m.space}.Challenge (scheme {ok.statements.claims.schemeName}, " ++
        s!"root {ok.statements.claims.root}, relation {g.relation}, spec {g.specification})"]
  expect "CLI ordered reports" report (String.join (lines.map (· ++ "\n")))
  expect "CLI distinct publication directories" ((← out.readDir).toList.map (·.fileName) |>.mergeSort)
    dirs.eraseDups.mergeSort

private def mixedChecks (work : System.FilePath) : IO Unit := do
  let file := "fixtures/hash-relation.zkc"
  let selectors := ["bad", "good", "bad", "mixed::bad"]
  let assembly ← Driver.assembleFiles (← source file []) ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly "good")
  let s ← statements root selectors
  expect "mixed raw relation keys" (s.claims.goals.map (·.relation)) [3,2,3,3]
  let omitted := ["bad","bad","mixed::bad"].map hashDiagnostic
  let m ← IO.ofExcept (s.module "MixedFull" {})
  publication m ["good"]
  expect "mixed full refusals" m.refusals omitted
  checkLayout m.statements ["good"] 1 1
  let fullCheck ← issued work m.statementsName.toString m.space m.statements m.stated
  let plain ← IO.ofExcept (s.claimsModule "MixedClaims")
  let claims ← factModule work "MixedClaims" plain ["good"] 1 1 omitted
  let cov ← IO.ofExcept (s.coverageModule "MixedCoverage")
  expect "mixed coverage theorems" cov.theorems ["good_covered"]
  let coverage ← factModule work "MixedCoverage" cov ["good"] 1 0 omitted
  let labels := ["bad","good","goal'mixed'58''58'bad"]
  let ceil ← IO.ofExcept (s.ceilingModule "MixedCeilings")
  let ceilings ← factModule work "MixedCeilings" ceil labels 2 0
  let mut clients := []
  for (mod,space,fees) in [(m.statementsName.toString,m.space,true), ("MixedClaims","MixedClaims",false)] do
    let data := sizes 1 1 ++ roles 6 0 1 ++ refs "good" 0 0 fees ++
      coordinates 0 0 2 [0,1] (some []) ++ fields 0 [0] (flat 6) "none"
    let standard := s!"StandardInterpretation.model {atGoal 0} StandardInterpretation.draws"
    let properties := ["ClaimOf","Claim","Goal","Result","Witnessed"] ++ (if fees then ["Judged"] else [])
    let meaning := String.join (properties.map fun p =>
      eqn ("good" ++ p) (s!"ZkcFormal.Written.Goal.{p} {standard}" ++
        (if p == "Result" then " StandardInterpretation.covers" else "")))
    clients := clients ++ [← issued work (space ++ "Source") space (client mod space (data ++ meaning))]
  let facts := String.join ((labels.zip [(1,3), (0,2), (1,3)]).map fun (l,arg,k) =>
    eqn (l ++ "Argument0") (toString arg) ++ eqn (l ++ "Key.number") (toString k) ++
      eqn (l ++ "Caps") (flat 6))
  let ceilingValues ← issued work "MixedCeilingSource" "MixedCeilings"
    (client "MixedCeilings" "MixedCeilings" facts)
  let allBad := ["bad","bad","mixed::bad"]
  let bad ← statements root allBad
  let diagnostic := "\n".intercalate (allBad.map hashDiagnostic)
  refusal diagnostic (bad.module "AllBad" {})
  refusal diagnostic (bad.claimsModule "AllBad")
  refusal diagnostic (bad.coverageModule "AllBad")
  cli work file selectors ["mixed::bad","mixed::good","mixed::bad","mixed::bad"]
    [false,true,false,false]
  (fullCheck :: claims :: coverage :: ceilings :: ceilingValues :: clients).forM id

#eval IO.FS.withTempDir aliasChecks
#eval IO.FS.withTempDir coordinateChecks
#eval IO.FS.withTempDir capChecks
#eval IO.FS.withTempDir routeEdges
#eval IO.FS.withTempDir mixedChecks
#eval do
  let selectors := aliases.map Prod.fst
  let paths := ["operands::left","operands::left","operands::left","operands::left_again","operands::right"]
  for (order, targets) in [(selectors, paths), (selectors.reverse, paths.reverse)] do
    IO.FS.withTempDir fun w => cli w "fixtures/written-decisions.zkc" order targets (List.replicate 5 true)
