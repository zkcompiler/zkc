import ZkcFormalTests.WrittenSubject
import Zkc.Tools.Frontend.WrittenGoals
import Zkc.Tests.Frontend.SyntaxHarness

/-! Read independently chosen source coordinates through the actual imported publication.
The controls change the issuance. Their clients keep the original source and selectors. -/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend
open PrintedPackageSupport ZkcFormalTests.WrittenSubject

private abbrev Check := IO Unit

example (a b : GoalClaims) (_g : {g // g ∈ b.goals}) : SubjectLayout a := by
  fail_if_success exact SubjectLayout.ofGoals a [_g]
  exact SubjectLayout.ofGoals a

example (a b : Statements) (_foreign : SubjectLayout b.claims) : String := by
  fail_if_success exact a.factsOf _foreign
  exact a.factsOf (SubjectLayout.ofGoals a.claims)

private def expect {α : Type} [BEq α] [Repr α] (what : String) (actual expected : α) : IO Unit :=
  unless actual == expected do throw (IO.userError s!"{what}: got {repr actual}, expected {repr expected}")

private def statements (root : AdmittedRoot) (selectors : List String) : IO Statements := do
  let raw ← IO.ofExcept (goalClaims root selectors)
  expect "original occurrences" (raw.goals.map (·.goal)) selectors
  return ⟨raw⟩

private def readSource (src : String) (selectors : List String) : IO Statements := do
  let first :: _ := selectors | throw (IO.userError "empty request")
  statements (← IO.ofExcept (goalRoot src first)) selectors

/-- The published theorems of rows whose declarations have the qualified names `paths`, in the
order of the rows: `sound` and `met` under the name space and the components of each path. -/
private def published (p : Publication) (paths : List String) : IO Unit :=
  expect "published theorems" p.published (paths.flatMap fun path =>
    let row := (path.splitOn "::").foldl (fun n c => Lean.Name.str n c) p.space.toName
    [.str row "sound", .str row "met"])

private def issued (work : System.FilePath) (file space body : String) (thms : List String := []) :
    IO Check := do
  let pending ← startLakeLean work file body (text := false)
  return do
    let (ok, out) ← pending
    acceptedOutput space ok out thms allowed

private def client (file space checks : String) : String :=
  s!"import {file}\nimport ZkcFormalTests.WrittenBinding\n" ++
    s!"namespace {space}\n{checks}\nend {space}\n"

private def eqn (lhs rhs : String) : String := s!"example : {lhs} = {rhs} := rfl\n"

private def atGoal (i : Nat) := s!"(written'subject.goals.get ⟨{i}, by decide⟩)"

private def coordinates (i place key : Nat) (xs : List Nat) (ws : Option (List Nat)) : String :=
  eqn s!"ZkcFormalTests.WrittenBinding.operands (written'subject.clauses.get {atGoal i}.clause)"
    s!"({place}, {key}, {xs.length}, {reprStr xs}, {reprStr ws})"

private def refs (i d relation : Nat) :=
  s!"run_cmd ZkcFormalTests.WrittenBinding.checkReferences (← Lean.getCurrNamespace) {i} {d} {relation}\n"

private def sizes (goals decisions : Nat) :=
  eqn "written'subject.goals.size" (toString goals) ++
    eqn "written'subject.clauses.size" (toString decisions)

private def roles (root prover verifier : Nat) :=
  eqn "(written'root.entry.header.key.number, written'root.prover.val, written'root.verifier.val)"
    s!"({root}, {prover}, {verifier})"

private def fields (i : Nat) (args : List Nat) (table : String) (bound : Nat × Nat) (ceiling := false) :=
  let number := s!"⟨{bound.1}, {bound.2}, by decide⟩"
  eqn s!"{atGoal i}.fields" (s!"⟨{reprStr args}, " ++
    (if ceiling then s!".ceiling {number} (some {table})" else s!".total {table} {number}") ++ "⟩")

private def flat (root : Nat) (draws := "[]") := s!"⟨[.flat ⟨{root}⟩ {draws} []]⟩"

private def full (work : System.FilePath) (space src : String) (req : List String)
    (paths : List String) (gold : String) : IO (Publication × Check) := do
  let s ← readSource src req
  let m ← IO.ofExcept (s.publication space)
  expect space m.refusals []
  published m paths
  let check ← issued work m.dataName.toString space m.data m.stated
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req)
  let compare ← issued work (space ++ "Source") space
    (client m.dataName.toString space (original ++ gold)) []
  return (m, check *> compare)

/-- Count the groups of fields of the data module, one per declaration, and its located
functions. -/
private def checkLayout (text : String) (rows functions : Nat) : IO Unit := do
  let names := (text.splitOn "\n").filterMap fun line => match line.splitOn " " with
    | "noncomputable" :: "def" :: n :: _ => some n
    | "def" :: n :: _ | "abbrev" :: n :: _ => some n
    | _ => none
  expect "one group of fields per declaration" (names.filter (·.startsWith "written'fields")).length rows
  expect "located functions" (names.filter (·.startsWith "written'fn")).length functions

/-- Five selectors of three declarations: three of them select `left`, which is one row. -/
private def aliases : List String :=
  ["left", "operands::left", "left", "left_again", "right"]

private def aliasCase (work : System.FilePath) (src : String) (reverse : Bool) :
    IO (Publication × Check) := do
  let rows := ["operands::left", "operands::left_again", "operands::right"]
  let (space, req, rows, selections, ports) := if reverse then
      ("Backward", aliases.reverse, rows.reverse, [(0,0), (1,1), (2,1)], [(1,3),(0,2),(0,2)])
    else ("Forward", aliases, rows, [(0,0), (1,0), (2,1)], [(0,2),(0,2),(1,3)])
  let gold := sizes 3 2 ++ roles 1 0 1 ++ String.join (ports.zipIdx.map fun ((p,x),i) =>
    coordinates i p 0 [x] (some [0]) ++ fields i [] (flat 1) (0, 1))
  let (m, check) ← full work space src req rows
    (gold ++ String.join (selections.map fun (i,d) => refs i d 0))
  checkLayout m.data 3 1
  return (m, check)

/-- Match each failure to a unique command in the unchanged source consumer and check the
diagnostic on that line. A malformed mutant, failed import, or additional error fails the test. -/
private def checkMutant (work : System.FilePath) (m : Publication) (tag changed original : String)
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

private def controls (work : System.FilePath) (m : Publication) (src : String) : IO (List Check) := do
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src aliases)
  let mutate := replaceOnce m.data
  let run := fun tag body => checkMutant work m tag body original
  let refAt := fun (i : Nat) => s!"checkReferences (← Lean.getCurrNamespace) {i} "
  let wrong := fun want got => s!"expected the reference {m.space}.{want}, found {got}"
  let twin (tag body want got : String) :=
    run tag body [(refAt 1, wrong want got)]
  let cap ← twin "RedirectFieldCap"
    (← mutate "number := .total written'caps1 written'bound1 }" "number := .total written'caps0 written'bound1 }")
    "written'caps1" "written'caps0"
  -- The fields of `left_again` name the bound of `left`: the two bounds are equal, and the
  -- reference is another goal's.
  let boundRef ← twin "RedirectFieldBound"
    (← mutate "number := .total written'caps1 written'bound1 }" "number := .total written'caps1 written'bound0 }")
    "written'bound1" "written'bound0"
  -- The bound of `left_again` is another number than its source gives.
  let boundValue ← run "OtherBound"
    (← mutate "written'bound1 : Zkc.Subject.Bound := ⟨0, 1, by decide⟩"
      "written'bound1 : Zkc.Subject.Bound := ⟨1, 2, by decide⟩")
    [(s!"({atGoal 1}.fields.number.bound.numerator,", "Type mismatch")]
  -- The fields of `left_again` say that the source writes its bound, and the goal writes none: a
  -- challenge would then not hold the bound to the table.
  let flipped ← run "FlippedCeiling"
    (← mutate "number := .total written'caps1 written'bound1 }" "number := .ceiling written'bound1 (some written'caps1) }")
    [(s!"{atGoal 1}.fields.number.written =", "Type mismatch")]
  -- The row of `left_again` has the path of `left`, and then another property than its goal names.
  let otherPath ← run "OtherPath"
    (← mutate "\"left_again\"], property :=" "\"left\"], property :=")
    [("⟨1, by decide⟩).path", "Type mismatch")]
  let otherProperty ← run "OtherProperty"
    (← mutate "property := Zkc.Security.Property.soundness, clause := ⟨0, by decide⟩, fields := written'fields1 }"
      "property := Zkc.Security.Property.completeness, clause := ⟨0, by decide⟩, fields := written'fields1 }")
    [("⟨1, by decide⟩).property", "Type mismatch")]
  -- A slot is printed with named fields; its clause and its fields are its last two.
  let slot (d : Nat) (f : String) := s!"clause := ⟨{d}, by decide⟩, fields := written'fields{f} }"
  let swapped ← mutate (slot 0 "0") (slot 0 "'")
  let swapped ← replaceOnce swapped (slot 0 "1") (slot 0 "0")
  let swapped ← replaceOnce swapped (slot 0 "'") (slot 0 "1")
  let swap ← run "SwapFields" swapped [
    (refAt 0, wrong "written'fields0" "written'fields1"),
    (refAt 1, wrong "written'fields1" "written'fields0")]
  -- Only the right decision uses the fourth port. Both candidate ports are shared Booleans.
  let third := "(Member.tail (Member.tail Member.head))"
  let fourth := s!"(Member.tail {third})"
  let moved ← mutate s!"⟨⟨_, {fourth}⟩, by decide +kernel" s!"⟨⟨_, {third}⟩, by decide +kernel"
  let operand ← run "MoveOperand" moved [(s!"WrittenBinding.operands (written'subject.clauses.get {atGoal 2}.clause)", "Type mismatch")]
  -- Route left_again to a new physical copy. All three dereferenced goals keep their values.
  let table := "⟨2, fun i => (if i.val < 1 then written'decision0 else written'decision1)⟩"
  let dupTable := "⟨3, fun i => (if i.val < 1 then written'decision0 else " ++
    "(if i.val < 2 then written'decision1 else written'decision2))⟩"
  let marker := "noncomputable def written'clauses :"
  let decl := "noncomputable def written'decision"
  let [_, tail] := m.data.splitOn (decl ++ "0 :")
    | throw (IO.userError "expected decision 0")
  let [body, _] := tail.splitOn (decl ++ "1 :") | throw (IO.userError "expected decision 1")
  let dup ← mutate marker (decl ++ "2 :" ++ body ++ marker)
  let dup ← replaceOnce dup table dupTable
  let dup ← replaceOnce dup (slot 0 "1") (slot 2 "1")
  let duplicate ← run "DuplicateRow" dup [("⟨1, by decide⟩).clause.val", "Type mismatch"),
    (refAt 1, s!"{m.space}.written'slot1 must select the decision 0"),
    ("written'subject.clauses.size =", "Type mismatch")]
  -- The selector of the table of decisions with a threshold that sends both indexes to the first
  -- decision, and with a comparison in another order that sends both to the second: the data
  -- control runs a selector at each index.
  let selector (tag changed refusal : String) : IO Check := do
    let file := tag ++ ".Stated"
    let check ← issued work file m.space (← replaceOnce m.data table changed) m.stated
    let pending ← startLakeLean work (tag ++ "Shape") (s!"import {file}\nimport ZkcFormalTests.PublicationControl\n\n#data_module {file} of {m.space}.written'subject\n") (text := false)
    return do
      check
      let (ok, log) ← pending
      expect s!"{tag}: the data control accepted the selector" ok false
      expect s!"{tag}: the data control refused the selector for another reason\n{log}" (log.contains refusal) true
  let threshold ← selector "SelectorThreshold"
    "⟨2, fun i => (if i.val < 2 then written'decision0 else written'decision1)⟩"
    "written'decision1 at the index 1"
  let ordered ← selector "SelectorOrder"
    ("⟨2, fun i => (@ite _ (@LT.lt Nat ⟨fun a b => b < a⟩ i.val 1) (Nat.decLt 1 i.val) " ++
      "written'decision0 written'decision1)⟩")
    "written'decision0 at the index 0"
  return [cap, boundRef, boundValue, flipped, otherPath, otherProperty, swap, operand, duplicate, threshold, ordered]

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
goal a = soundness(Checked, clause = first, spec e = 1) <= 3/4
goal b = soundness(Checked, clause = first, spec e = 3) <= 1/2
goal c = soundness(Checked, clause = clone, spec e = 1) <= 3/4
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

/-- Two deployed schemes have the same short name, installed program, and roles. An
independent reader must still identify the declaration selected by the original goal. -/
private def schemeOwners (work : System.FilePath) : IO Unit := do
  let left := "module pair
use zkc::security::{soundness}
relation No(): false
protocol C roles(V,P)():
    guard @V false
spec for C:
    proves @V No()
module Left:
    pub scheme S = C:
        prover P
        construction interactive
module Right:
    pub scheme S = C:
        prover P
        construction interactive
goal target = soundness(Left::S)
"
  let right ← replaceOnce left "soundness(Left::S)" "soundness(Right::S)"
  -- two selectors of one declaration, which is one row
  let req := ["target", "pair::target"]
  let (m, leftCheck) ← full work "LeftScheme" left req ["pair::target"]
    (eqn "written'origins.schemePath" (reprStr "pair::Left::S"))
  let (_, rightCheck) ← full work "RightScheme" right req ["pair::target"]
    (eqn "written'origins.schemePath" (reprStr "pair::Right::S"))
  let comparison ← startSourceComparison work "QualifiedSource" (Module.ofPublication m) left req
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer right req)
  let crossed ← checkMutant work m "CrossedScheme" m.data original
    [("written'origins.schemePath =", "Type mismatch")]
  leftCheck
  rightCheck
  crossed
  let (ok, log) ← comparison
  acceptedOutput "qualified source selectors" ok log [] allowed

/-- The file module catalog::Pair and a nested Pair in catalog both contain S. Both
schemes select exactly the same protocol, roles and goal spelling through real imports. -/
private def importedScheme (work : System.FilePath) : IO Unit := do
  let issue (tag selector : String) (definingModule : Array String) := do
    let entry := "module catalog\nuse catalog::Pair::{C, S}\nuse zkc::security::{soundness}\n" ++
      "module Pair:\n    pub scheme S = C:\n        prover P\n        construction interactive\n" ++
      s!"goal target = soundness({selector})\n"
    let assembly ← Driver.assembleFiles ⟨"catalog.zkc", Syntax.parseString "catalog.zkc" entry⟩
      ["fixtures/scheme-origin", "../../libraries"]
    let #[result] := issueSoundnessGoals assembly ["target"] | throw (IO.userError "expected one issue")
    expect "original goal" result.path (some "catalog::target")
    let m := (← IO.ofExcept result.outcome).publication
    let original ← IO.ofExcept (admitSoundnessGoal assembly "target")
    let readback ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumerAt original ["target"])
    let check ← issued work tag m.space m.data m.stated
    let gold := eqn "written'origins.schemeFileModule" (reprStr definingModule) ++
      eqn "written'origins.schemePath" (reprStr "catalog::Pair::S")
    let observed ← issued work (tag ++ "Client") m.space (client tag m.space (readback ++ gold))
    return (m, readback, check *> observed)
  let (nested, nestedSource, checkNested) ← issue "NestedIssued" "Pair::S" #["catalog"]
  let (flat, flatSource, checkFlat) ← issue "ImportedIssued" "S" #["catalog", "Pair"]
  expect "canonical goal namespace" nested.space flat.space
  let mismatch := [("written'origins.schemeFileModule =", "Type mismatch")]
  let crossNested ← checkMutant work nested "ExpectImported" nested.data flatSource mismatch
  let crossFlat ← checkMutant work flat "ExpectNested" flat.data nestedSource mismatch
  [checkNested, checkFlat, crossNested, crossFlat].forM id

private def countSource : IO String := do
  let blocks := readBlocks (← IO.FS.readFile "../../language/conformance/layer-b.txt")
  let some src := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing Count N-GL2a")
  return src

private def coordinateChecks (work : System.FilePath) : IO Unit := do
  let add := fun name src selectors rows gold => Prod.snd <$> full work name src selectors rows gold
  let count ← add "CountRows" (← countSource) ["loose","strict"] ["t::loose","t::strict"]
    (sizes 2 2 ++ roles 1 0 1 ++ coordinates 0 0 3 [0] (some []) ++
     coordinates 1 0 4 [0] (some []) ++ fields 0 [4] (flat 1 "[⟨⟨0⟩, 3, 8, 1⟩]") (3, 8) ++
     fields 1 [1] (flat 1 "[⟨⟨0⟩, 3, 4, 1⟩]") (3, 4))
  let shared ← add "ChargedRows" tenancy ["a","b","c"] ["tenancy::a","tenancy::b","tenancy::c"] (sizes 3 2 ++ String.join
    ([(1,1,2,(3, 4)), (1,3,4,(1, 2)), (2,1,2,(3, 4))].zipIdx.map
      fun ((place,e,den,cap),i) => coordinates i place 0 [0] (some []) ++
        fields i [e] (flat 1 s!"[⟨⟨0⟩, 1, {den}, 1⟩]") cap (ceiling := true)))
  let reps ← add "Occurrences" occurrences ["left","right","twin","again","left"]
    ["coordinates::left","coordinates::right","coordinates::twin","coordinates::again"]
    (sizes 4 3 ++ roles 1 1 0 ++ String.join ([
      (0,0,[2,1,1],[0,3]), (1,1,[1,2,1],[3,0]), (2,2,[2,1,1],[0,3]),
      (3,0,[2,1,1],[0,3])].map fun (i,p,x,w) => coordinates i p 0 x (some w)) ++
      refs 3 0 0)
  let short ← add "ShortWitness" occurrences ["short"] ["coordinates::short"] (coordinates 0 3 0 [2,1,1] none)
  let slots ← IO.FS.readFile "fixtures/written-decisions.zkc"
  let mapped ← add "WitnessPorts" slots ["left","other_witness","implicit_witness"]
    ["operands::left","operands::other_witness","operands::implicit_witness"]
    (coordinates 0 0 0 [2] (some [0]) ++ coordinates 1 3 0 [2] (some [1]) ++
      coordinates 2 2 0 [2] none)
  let mut bare := []
  for (name,src,p,v) in [("EmptyRoles",zero,1,0),
      ("TurnedRoles",(zero.replace "prover P" "prover V").replace "@V" "@P",0,1)] do
    let raw ← readSource src ["z"]
    expect "raw zero-input scheme" (raw.claims.inputs.size, raw.claims.prover, raw.claims.verifier)
      (0,p,v)
    let req := ["z"]
    let (m, good) ← full work name src req ["zero::z"] (roles 1 p v ++ coordinates 0 0 0 [] (some []))
    bare := good :: bare
    if name == "EmptyRoles" then
      let flipped ← replaceOnce m.data "abbrev proverRole : Role := 1" "abbrev proverRole : Role := 0"
      let flipped ← replaceOnce flipped "abbrev verifierRole : Role := 0" "abbrev verifierRole : Role := 1"
      let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req)
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
  let req := ["a","b"]
  let draws := fun (z t : Nat) => flat 1 s!"[⟨⟨0⟩, {z}, 8, 1⟩, ⟨⟨1⟩, {t}, 8, 1⟩]"
  let (m, check) ← full work "EqualTotals" src req ["tenancy::a","tenancy::b"]
    (fields 0 [1] (draws 1 3) (3, 4) (ceiling := true) ++ fields 1 [3] (draws 3 1) (1, 2) (ceiling := true))
  let redirect := fun (text : String) =>
    replaceOnce text "specification := [3], number := .ceiling written'bound1 (some written'caps1) }" "specification := [3], number := .ceiling written'bound1 (some written'caps0) }"
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req)
  -- The fields of `b` name the table of `a`, whose total is the same and whose draws pay other fees.
  let inconsistent ← checkMutant work m "InconsistentCap" (← redirect m.data) original
    [(s!"{atGoal 1}.fields.number.caps =", "Type mismatch"),
     ("checkReferences (← Lean.getCurrNamespace) 1 ",
       "expected the reference EqualTotals.written'caps1, found written'caps0")]
  -- A consistent re-emission pays the sibling's fees but keeps the requested arguments and
  -- the common total. Redirect its now equal table reference as a second, independent fault.
  let constant ← replaceOnce src "sites.z <= e / 8" "sites.z <= 1 / 8"
  let constant ← replaceOnce constant "sites.t <= (4 - e) / 8" "sites.t <= 3 / 8"
  let other ← readSource constant req
  let other ← IO.ofExcept (other.publication m.space)
  let bad ← checkMutant work m "ChangedCapTree" (← redirect other.data) original
    [(s!"{atGoal 1}.fields.number.caps =", "Type mismatch"),
     ("checkReferences (← Lean.getCurrNamespace) 1 ",
       "expected the reference EqualTotals.written'caps1, found written'caps0")]
  check
  inconsistent
  bad

/-- Two clauses select one function. Inlining an equal entry in only the second clause
still gives the same values, but loses the reference to the shared function. -/
private def sharedFunction (work : System.FilePath) : IO Unit := do
  let req := ["a", "b", "c"]
  let s ← readSource tenancy req
  let m ← IO.ofExcept (s.publication "SharedFunction")
  let changed ← replaceOnce m.data
    "written'application1 : Zkc.Subject.ShortApplication written'root :=\n  ⟨written'fn0, ⟨1, by decide +kernel⟩"
    "written'application1 : Zkc.Subject.ShortApplication written'root :=\n  ⟨⟨header0, member'fn0, found'fn0⟩, ⟨1, by decide +kernel⟩"
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer tenancy req)
  let bad ← checkMutant work m "InlineFunction" changed original
    [("checkReferences (← Lean.getCurrNamespace) 2 ", "expected the reference SharedFunction.written'fn0")]
  -- The same function entry, reached through the source's names by way of a private helper of
  -- the module: the values are the same, and a statement over this short application
  -- would read the origins.
  let through ← replaceOnce m.data
    ("noncomputable def written'application1 : Zkc.Subject.ShortApplication written'root :=\n" ++
      "  ⟨written'fn0, ⟨1, by decide +kernel⟩")
    ("private noncomputable def entryByNames : Zkc.Subject.FunctionEntry subjectPackage :=\n" ++
      "  (fun (_ : Zkc.Subject.RootOrigins written'root) => written'fn0) written'origins\n" ++
      "noncomputable def written'application1 : Zkc.Subject.ShortApplication written'root :=\n" ++
      "  ⟨entryByNames, ⟨1, by decide +kernel⟩")
  let reaching ← checkMutant work m "ApplicationReach" through original
    [("checkReferences (← Lean.getCurrNamespace) 2 ",
      "the short application SharedFunction.written'application1 reaches SharedFunction.written'origins")]
  -- The same function entry again, reached through a bound: a short application is the same at
  -- every bound, and a statement over this one would read a goal's number.
  let bounded ← replaceOnce m.data
    ("noncomputable def written'application1 : Zkc.Subject.ShortApplication written'root :=\n" ++
      "  ⟨written'fn0, ⟨1, by decide +kernel⟩")
    ("def written'bound9 : Zkc.Subject.Bound := ⟨1, 2, by decide⟩\n" ++
      "private noncomputable def entryAtBound : Zkc.Subject.FunctionEntry subjectPackage :=\n" ++
      "  (fun (_ : Zkc.Subject.Bound) => written'fn0) written'bound9\n" ++
      "noncomputable def written'application1 : Zkc.Subject.ShortApplication written'root :=\n" ++
      "  ⟨entryAtBound, ⟨1, by decide +kernel⟩")
  let reachingBound ← checkMutant work m "ApplicationBound" bounded original
    [("checkReferences (← Lean.getCurrNamespace) 2 ",
      "the short application SharedFunction.written'application1 reaches SharedFunction.written'bound9")]
  -- The bound again under an alias of its type: the declaration is told by what its type is.
  let aliased ← replaceOnce m.data
    ("noncomputable def written'application1 : Zkc.Subject.ShortApplication written'root :=\n" ++
      "  ⟨written'fn0, ⟨1, by decide +kernel⟩")
    ("abbrev BoundAlias := Zkc.Subject.Bound\ndef written'bound9 : BoundAlias := ⟨1, 2, by decide⟩\n" ++
      "private noncomputable def entryAtBound : Zkc.Subject.FunctionEntry subjectPackage :=\n" ++
      "  (fun (_ : Zkc.Subject.Bound) => written'fn0) written'bound9\n" ++
      "noncomputable def written'application1 : Zkc.Subject.ShortApplication written'root :=\n" ++
      "  ⟨entryAtBound, ⟨1, by decide +kernel⟩")
  let reachingAlias ← checkMutant work m "ApplicationAlias" aliased original
    [("checkReferences (← Lean.getCurrNamespace) 2 ",
      "the short application SharedFunction.written'application1 reaches SharedFunction.written'bound9")]
  bad
  reaching
  reachingBound
  reachingAlias

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

private def routeEdges (work : System.FilePath) : IO Unit := do
  let red ← readSource reduction ["red","pos"]
  let why := "red: the goal reads a `reduces` clause. The statement of a reduction " ++
    "is about a return on which the reduced statement is true, and is not issued yet"
  refusal why (red.publication "Reduction")
  -- A ceiling below the total of the charges is issued: the row's bound is the ceiling.
  let src := (← countSource) ++ "\ngoal low = soundness(Checked, spec e = 1) <= 0\n"
  let req := ["low","loose"]
  let low ← IO.ofExcept ((← readSource src req).publication "Low")
  expect "low-ceiling refusals" low.refusals []
  published low ["t::low","t::loose"]
  let data ← issued work low.dataName.toString low.space low.data low.stated
  let original ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumer src req)
  let reader ← issued work "LowSource" low.space (client low.dataName.toString low.space
    (original ++ fields 0 [1] (flat 1 "[⟨⟨0⟩, 3, 4, 1⟩]") (0, 1) (ceiling := true)))
  [data, reader].forM id

private def hashDiagnostic (goal : String) :=
  goal ++ ": no interpretation of row (.inl (Zkc.Vocabulary.RowKey.hash (Zkc.Vocabulary.Hash.sha256)))"

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
      expect "CLI data module" (← IO.FS.readFile (dir / "Stated.lean")) m.data
      expect "CLI challenge" (← IO.FS.readFile (dir / "Challenge.lean")) m.challenge
      expect "CLI views module" (← IO.FS.readFile (dir / "Views.lean")) m.views
      expect "CLI fees module" (← IO.FS.readFile (dir / "Fees.lean")) m.fees
      expect "CLI goal files" ((← dir.readDir).toList.map (·.fileName) |>.mergeSort)
        ["Challenge.lean", "Fees.lean", "Stated.lean", "Views.lean"]
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
  let m ← IO.ofExcept (s.publication "MixedFull")
  published m ["mixed::good"]
  expect "mixed full refusals" m.refusals omitted
  checkLayout m.data 1 1
  let fullCheck ← issued work m.dataName.toString m.space m.data m.stated
  let data := sizes 1 1 ++ roles 6 0 1 ++ refs 0 0 2 ++
    coordinates 0 0 2 [0,1] (some []) ++ fields 0 [0] (flat 6) (0, 1) ++
    eqn "stored2.key.number" "2"
  let reader ← issued work (m.space ++ "Source") m.space (client m.dataName.toString m.space data)
  let allBad := ["bad","bad","mixed::bad"]
  let bad ← statements root allBad
  let diagnostic := "\n".intercalate (allBad.map hashDiagnostic)
  refusal diagnostic (bad.publication "AllBad")
  cli work file selectors ["mixed::bad","mixed::good","mixed::bad","mixed::bad"]
    [false,true,false,false]
  [fullCheck, reader].forM id

#eval IO.FS.withTempDir aliasChecks
#eval IO.FS.withTempDir coordinateChecks
#eval IO.FS.withTempDir schemeOwners
#eval IO.FS.withTempDir importedScheme
#eval IO.FS.withTempDir capChecks
#eval IO.FS.withTempDir sharedFunction
#eval IO.FS.withTempDir routeEdges
#eval IO.FS.withTempDir mixedChecks
#eval do
  let selectors := aliases
  let paths := ["operands::left","operands::left","operands::left","operands::left_again","operands::right"]
  for (order, targets) in [(selectors, paths), (selectors.reverse, paths.reverse)] do
    IO.FS.withTempDir fun w => cli w "fixtures/written-decisions.zkc" order targets (List.replicate 5 true)
