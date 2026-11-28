import Zkc.Frontend.Driver.Files
import Zkc.Frontend.Driver.Session
import Zkc.Frontend.Written.Export
import Zkc.Frontend.Written.Goals
import Zkc.Tests.Frontend.SyntaxHarness

namespace Zkc.Tests.Frontend
open Zkc.Frontend

namespace WrittenSelectionReads

private def input (file text : String) : SourceInput := ⟨file, Syntax.parseString file text⟩

-- Only the scheme reads Size<2>. The protocol has no module parameter or module read.
private def library (body : String) : String := "module sizes
pub interface Sized:
    nat N
    def valid(x: bool) -> bool
pub module Size<n: nat>: Sized:
    nat N = n
    def valid(x): " ++ body ++ "
pub relation Holds(x: bool): x
pub protocol Work<n: nat> roles(P,V)(x: bool @(P,V)):
    guard @V x
spec for Work:
    proves @V Holds(x)
"

private def entry := "module caller
use sizes::{Work, Size}
use zkc::security::{soundness}
scheme Checked = Work<Size<2>::N>:
    prover P
    construction interactive
goal selected = soundness(Checked)
"

private def loader (body : String) (path : Array String) : Id (Option SourceInput) :=
  if path == #["sizes"] then some (input "sizes.zkc" (library body)) else none

private def assembly (text : String := entry) (body : String := "x")
    (other : Array SourceInput := #[]) : Assembly :=
  Id.run <| assemble (#[input "caller.zkc" text] ++ other) (loader body)

private def printed (root : Written.AdmittedRoot) : String :=
  (Written.package (root.emission.package ⟨[], [], [], [], []⟩)).text

private def sizeCheck (state : Compile.State) : Option (Except Interrupt Unit) :=
  state.checkedModules.toList.findSome? fun (key, result) =>
    if state.program.nameOf key.declaration == "Size" && key.arguments == #[.natural 2] then
      some result
    else none

private def expectRefusal {α : Type} (result : Except String α) (fragments : List String) :
    TestM Unit := do
  let .error message := result | failure s!"expected a refusal containing {fragments}"
  expectTrue (fragments.all (fun part => message.contains part)) s!"expected {fragments} in {message}"

private def admitByNumber (input : Assembly) : Except String Written.AdmittedRoot := do
  let state ← Written.sourceState input
  let #[id] := state.roots | throw "expected one numbered root"
  Written.admitInstance state id default

private def rootReads : TestM Unit := do
  let ok := assembly
  let .ok sole := Written.admitSource ok | failure "the sole root did not admit"
  let .ok numbered := admitByNumber ok | failure "the numbered root did not admit"
  let .ok named := Written.admitSoundnessGoal ok "selected" | failure "the named root did not admit"
  let session := Id.run <| (Driver.Session.start vocabulary).compile
    #[input "caller.zkc" entry] (loader "x")
  let #[(_, pkg)] := session.admitRoots.held | failure "expected one ordinary root package"
  expectTrue ([session.state, sole.state, numbered.state, named.state].all fun s => (sizeCheck s).any (·.isOk))
    "ordinary, sole, numbered and named admission must all check Size<2>"
  expectTrue (sole.id == named.id && printed numbered == printed sole && printed sole == printed named &&
      printed sole == (Written.package pkg.toSourcePackage).text)
    "validating the scheme read changed the deployed package"

  let bad := assembly entry "(x, x)"
  expectRefusal (admitByNumber bad) ["TY5", "sizes.zkc", "Size<n = 2>"]
  expectRefusal (Written.admitSource bad) ["TY5", "sizes.zkc", "Size<n = 2>"]
  expectRefusal (Written.admitSoundnessGoal bad "selected") ["TY5", "sizes.zkc", "Size<n = 2>"]

  -- Both schemes close to Work<2>, but only one reads the invalid Size<2>.
  let siblings := assembly (entry ++ "scheme Direct = Work<2>:
    prover P
    construction interactive
goal direct = soundness(Direct)
") "(x, x)"
  let .ok direct := Written.admitSoundnessGoal siblings "direct"
    | failure "the direct scheme inherited a sibling's validation failure"
  expectTrue (sizeCheck direct.state).isNone "the direct scheme checked the sibling's Size<2>"
  expectRefusal (Written.admitSoundnessGoal siblings "selected") ["TY5", "Size<n = 2>"]

  -- The explicit directive is global, even when the selected scheme itself has no read.
  let directives := assembly (entry.replace "Work<Size<2>::N>" "Work<2>" ++
    "// instantiate: Work<2>\n// instantiate: Size<2>\n") "(x, x)"
  let .error message := Written.admitSoundnessGoal directives "selected"
    | failure "the named goal ignored an explicit directive"
  expectTrue (message.startsWith "sizes.zkc:7:" && message.contains "WK-TYPE" &&
      message.contains "TY5" && message.contains "caller.zkc:9)")
    s!"the directive lost its failing member location, rule or request chain: {message}"

private def soundnessNames : TestM Unit := do
  let brokenGoal := "goal broken = soundness(MissingScheme)\n"
  let mixed := assembly (entry ++ brokenGoal)
  let .ok root := Written.admitSoundnessGoal mixed "caller::selected"
    | failure "a sibling's unresolved goal blocked named root admission"
  let .ok clean := Written.admitSoundnessGoal assembly "selected"
    | failure "expected the healthy control root"
  expectTrue (printed root == printed clean) "the unrelated goal changed the package"
  expectRefusal (Written.admitSoundnessGoal mixed "broken") ["NL3", "MissingScheme"]
  expectRefusal (Written.goalClaims root ["selected", "broken"]) ["NL3", "MissingScheme"]
  let #[bad, good, alias_] := Written.issueSoundnessGoals mixed ["broken", "selected", "caller::selected"]
    | failure "expected one decision per selector"
  expectRefusal bad.outcome ["NL3", "MissingScheme"]
  let .ok g := good.outcome | failure "batch issuance of selected failed"
  let .ok a := alias_.outcome | failure "batch issuance of the canonical name failed"
  expectTrue (good.path == some "caller::selected" && good.path == alias_.path &&
      g.publication.data == a.publication.data &&
      g.publication.challenge == a.publication.challenge)
    "canonical and short names produced different challenges"

  let other := input "other.zkc" ("module other\nuse zkc::security::{soundness}\n" ++
    "goal selected = soundness(MissingScheme)\n")
  let ambiguous := assembly entry "x" #[other]
  expectRefusal (Written.admitSoundnessGoal ambiguous "selected")
    ["WK-GOAL", "ambiguous", "caller::selected", "other::selected"]
  expectRefusal (Written.exportSelected ambiguous (.goal "selected") true)
    ["WK-GOAL", "ambiguous", "caller::selected", "other::selected"]
  expectTrue (Written.admitSoundnessGoal ambiguous "caller::selected").isOk
    "the unique qualified selector did not admit"
  expectRefusal (Written.admitSoundnessGoal ambiguous "other::selected") ["NL3", "MissingScheme"]

  -- A nested declaration and a file module can give two declarations one canonical path.
  let nested := entry ++ "module Inner:\n    goal same = soundness(Checked)\n"
  let sibling := input "inner.zkc" ("module caller::Inner\nuse zkc::security::{soundness}\n" ++
    "goal same = soundness(MissingScheme)\n")
  let collision := assembly nested "x" #[sibling]
  for name in ["caller::Inner::same", "Inner::same"] do
    let reason := ["WK-GOAL", "ambiguous canonical path caller::Inner::same"]
    expectRefusal (Written.admitSoundnessGoal collision name) reason
    expectRefusal (Written.exportSelected collision (.goal name) true) reason

  let global := assembly (entry ++ brokenGoal ++ "relation Bad(x: bool): MissingGlobal(x)\n")
  expectRefusal (Written.admitSoundnessGoal global "selected") ["NL3", "MissingGlobal"]
  let #[globalResult] := Written.issueSoundnessGoals global ["selected"]
    | failure "expected one shared refusal"
  expectRefusal globalResult.outcome ["NL3", "MissingGlobal"]
  expectRefusal (Written.admitSource mixed) ["NL3", "MissingScheme"]

private def forkNames (repository : Repository) : TestM Unit := do
  let file := repository.examples / "chaum_pedersen.zkc"
  let text ← IO.FS.readFile file
  let read (extra : String) := Driver.assembleFiles (input file.toString (text ++ extra))
    [repository.libraries, repository.examples, repository.examples / "support"]
  let clean ← read ""
  let mixed ← read "\ngoal spare = special_soundness(MissingScheme, stage = written)\n"
  let .ok expected := Written.exportSelected clean (.goal "fork") true
    | failure "expected the example's fork export"
  let .ok actual := Written.exportSelected mixed (.goal "chaum_pedersen::fork") true
    | failure "an unresolved sibling blocked the example's fork export"
  expectTrue (actual == expected) "an unrelated name refusal changed the emitted fork theorem"
  expectRefusal (Written.exportSelected mixed (.goal "spare") true) ["NL3", "MissingScheme"]
  expectRefusal (Written.exportSelected mixed (.scheme "SameLogProof") true) ["NL3", "MissingScheme"]
  let global ← read "\nrelation Bad(x: bool): MissingGlobal(x)\n"
  expectRefusal (Written.exportSelected global (.goal "fork") true) ["NL3", "MissingGlobal"]

end WrittenSelectionReads

def writtenSelectionReadsSuite (repository : Repository) : TestM Unit := do
  WrittenSelectionReads.rootReads
  WrittenSelectionReads.soundnessNames
  WrittenSelectionReads.forkNames repository

end Zkc.Tests.Frontend
