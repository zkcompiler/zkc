import ZkcFormalTests.WrittenSubject
import Zkc.Tests.Frontend.SyntaxHarness

/-!
The forms of a subject's programs, with their equations, on the issued subjects.

For each source the issuer's data module is built, and `publish_forms` declares, for every
definition in the subject's reach (the root's deciding role, the function of each clause's
relation, and what their forms call), its form and the equation that the form is the reading of
the definition's meaning, whose proof is one application of the library's theorem; each is
registered. The check compares the register's rows with the rows that it expects of the source,
and asks that every equation rests on `propext` and `Quot.sound` at most: a form holds for
every model. Every form has passed the producer's check that it is type-correct as a tactic
compares types.

The sources between them have a loop with a carried value (Guess), a choice with a guard in each
arm (Either), a stepped loop written out as blocks (Steps), two applications of a protocol that
calls a function (Twice), a protocol that two callers apply, which has one form (Nested), a
callee whose roles are bound in another order (Swapped), one that is also passed a value that
both roles hold (Seen), a chain of values each used twice (Chain), a loop of a role that
collects (Gather), a vector of scalars drawn and three applications of a function over matrices (Freivalds), and the
conformance corpus's count of near-zero entries (Count). Two controls: a construct that the
walk does not read (a `match` on a variant) refuses the subject's forms by its name; and a data
module whose headers are not marked reducible gives a form that fits its places only by
unfolding them, which the producer's check refuses.

With `ZKC_WORK` naming a folder the check's project is kept there.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace ProgramForms

def guess : String :=
  "module t\nuse zkc::security::{soundness}\nsection <n: nat>:\n" ++
  "    relation Holds(claim: bool): claim\n" ++
  "    protocol Guess roles(P, V)(claim: bool @(P, V), guess: index<8> @P):\n" ++
  "        mut hit = false\n        for i in 0..n:\n" ++
  "            g <- send guess from P to V\n            r <- draw index<8> from V to P\n" ++
  "            hit := hit or (r == g)\n        guard @V claim or hit\n" ++
  "    spec for Guess:\n        proves @V Holds(claim)\n        charge sites.r <= 1 / 8\n" ++
  "scheme Checked = Guess<3>:\n    prover P\n    construction interactive\n" ++
  "goal guessing = soundness(Checked, stage = written)\n"

def either : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Either roles(P, V)(claim: bool @(P, V), first: index<8> @P, second: index<4> @P):\n" ++
  "    if claim:\n" ++
  "        a <- send first from P to V\n        x <- draw index<8> from V to P\n" ++
  "        guard @V x == a\n" ++
  "    else:\n" ++
  "        b <- send second from P to V\n        guard @V b != 3\n" ++
  "        y <- draw index<4> from V to P\n        guard @V y == b\n" ++
  "spec for Either:\n    proves @V Holds(claim)\n    charge sites.x <= 1 / 8\n" ++
  "    charge sites.y <= 1 / 4\n" ++
  "scheme Checked = Either:\n    prover P\n    construction interactive\n" ++
  "goal either = soundness(Checked, stage = written)\n"

def stepped : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Steps roles(P, V)(claim: bool @(P, V)):\n" ++
  "    for i in 0..3:\n        r <- draw index<i + 2> from V to P\n        guard @V r != 0\n" ++
  "    guard @V claim\n" ++
  "spec for Steps:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 4\n" ++
  "scheme Checked = Steps:\n    prover P\n    construction interactive\n" ++
  "goal stepped = soundness(Checked, stage = written)\n"

def twice : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "def same(a: index<4>, b: index<4>) -> bool: a == b\n" ++
  "protocol Round roles(P, V)(sent: index<4> @P) -> (hit: bool @(P, V), drawn: index<4> @(P, V)):\n" ++
  "    x <- send sent from P to V\n    r <- draw index<4> from V to P\n" ++
  "    return (same(r, x), r)\n" ++
  "spec for Round:\n    charge sites.r <= 1 / 4\n" ++
  "protocol Twice roles(P, V)(claim: bool @(P, V), first: index<4> @P, second: index<4> @P):\n" ++
  "    a <- Round(first)\n    b <- Round(second)\n" ++
  "    guard @V claim or a.hit or b.hit\n" ++
  "spec for Twice:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Twice:\n    prover P\n    construction interactive\n" ++
  "goal twice = soundness(Checked, stage = written)\n"

/-- A callee that two callers apply: `Pair` applies `Round` twice, and the root applies `Pair`
twice. Each of `Round` and `Pair` has one form at the verifier's role, whoever applies it. -/
def nested : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "def same(a: index<8>, b: index<8>) -> bool: a == b\n" ++
  "protocol Round roles(P, V)(sent: index<8> @P) -> (hit: bool @(P, V), drawn: index<8> @(P, V)):\n" ++
  "    x <- send sent from P to V\n    r <- draw index<8> from V to P\n" ++
  "    return (same(r, x), r)\n" ++
  "spec for Round:\n    charge sites.r <= 1 / 8\n" ++
  "protocol Pair roles(P, V)(first: index<8> @P, second: index<8> @P) -> (hit: bool @(P, V), last: index<8> @(P, V)):\n" ++
  "    a <- Round(first)\n    b <- Round(second)\n" ++
  "    return (a.hit or b.hit, b.drawn)\n" ++
  "protocol Nested roles(P, V)(claim: bool @(P, V), w: index<8> @P, x: index<8> @P, y: index<8> @P, z: index<8> @P):\n" ++
  "    p <- Pair(w, x)\n    q <- Pair(y, z)\n" ++
  "    guard @V claim or p.hit or q.hit\n" ++
  "spec for Nested:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Nested:\n    prover P\n    construction interactive\n" ++
  "goal nested = soundness(Checked, stage = written)\n"

/-- A callee whose roles are bound in another order: the round names the role that draws first,
and the root's verifier plays it, so the verifier is the callee's role 0. -/
def swapped : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Round roles(B, A)(sent: index<4> @A) -> (hit: bool @(A, B), drawn: index<4> @(A, B)):\n" ++
  "    x <- send sent from A to B\n    r <- draw index<4> from B to A\n" ++
  "    return (r == x, r)\n" ++
  "spec for Round:\n    charge sites.r <= 1 / 4\n" ++
  "protocol Swapped roles(P, V)(claim: bool @(P, V), first: index<4> @P):\n" ++
  "    a <- Round(first) @(A = P, B = V)\n" ++
  "    guard @V claim or a.hit\n" ++
  "spec for Swapped:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Swapped:\n    prover P\n    construction interactive\n" ++
  "goal swapped = soundness(Checked, stage = written)\n"

/-- A value that both roles hold, passed into a callee whose roles are bound in another order:
the callee's verifier reads it in a guard. -/
def seen : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Round roles(B, A)(sent: index<4> @B, seen: bool @(A, B)) -> (hit: bool @(A, B), drawn: index<4> @(A, B)):\n" ++
  "    x <- send sent from B to A\n    r <- draw index<4> from A to B\n" ++
  "    guard @A seen or r != 7\n" ++
  "    return (r == x, r)\n" ++
  "spec for Round:\n    charge sites.r <= 1 / 4\n" ++
  "protocol Seen roles(P, V)(claim: bool @(P, V), first: index<4> @P):\n" ++
  "    a <- Round(first, claim) @(A = V, B = P)\n" ++
  "    guard @V claim or a.hit\n" ++
  "spec for Seen:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Seen:\n    prover P\n    construction interactive\n" ++
  "goal seen = soundness(Checked, stage = written)\n"

/-- A chain of values each used twice by the next: twelve bindings. Written out by
substitution, the last would hold the first four thousand times. -/
def chained : String := Id.run do
  let mut text := "module t\nuse zkc::security::{soundness}\n" ++
    "relation Holds(claim: bool): claim\n" ++
    "protocol Chain roles(P, V)(claim: bool @(P, V)):\n" ++
    "    r <- draw index<2> from V to P\n    b0 = claim or r == 1\n"
  for i in [1:13] do
    text := text ++ s!"    b{i} = b{i - 1} and b{i - 1}\n"
  return text ++ "    guard @V b12\n" ++
    "spec for Chain:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 2\n" ++
    "scheme Checked = Chain:\n    prover P\n    construction interactive\n" ++
    "goal chained = soundness(Checked, stage = written)\n"

/-- A loop of a role that collects: the positions drawn in three rounds are one sequence. -/
def gathered : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Gather roles(P, V)(claim: bool @(P, V), guess: index<8> @P):\n" ++
  "    for i in 0..3 collect (rs = r):\n" ++
  "        g <- send guess from P to V\n        r <- draw index<8> from V to P\n" ++
  "    guard @V claim or rs[0] == rs[1]\n" ++
  "spec for Gather:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 8\n" ++
  "scheme Checked = Gather:\n    prover P\n    construction interactive\n" ++
  "goal gathered = soundness(Checked, stage = written)\n"

/-- A source with a choice among the alternatives of a variant, which the walk does not read
yet: on one side a position is heard and one is drawn, on the other nothing happens. -/
def sided : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "enum Side:\n    Left\n    Right\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Sided roles(P, V)(claim: bool @(P, V), side: Side @(P, V), first: index<4> @P):\n" ++
  "    mut hit = false\n" ++
  "    match side:\n" ++
  "        case Left:\n" ++
  "            a <- send first from P to V\n            x <- draw index<4> from V to P\n" ++
  "            hit := x == a\n" ++
  "        case Right:\n            ()\n" ++
  "    guard @V claim or hit\n" ++
  "spec for Sided:\n    proves @V Holds(claim)\n    charge sites.x <= 1 / 4\n" ++
  "scheme Checked = Sided:\n    prover P\n    construction interactive\n" ++
  "goal sided = soundness(Checked, stage = written)\n"

/-- The source of Freivalds' check of a product of matrices of size two. -/
def freivalds : String :=
  "module t\n" ++
  "use zkc::security::{soundness}\n" ++
  "type F = primitive(\"bls12-381.fr\")\n" ++
  "section <n: nat>:\n" ++
  "    def apply(m: [[F; n]; n], v: [F; n]) -> [F; n]: [∑ k ∈ 0..n, m[i][k] * v[k] for i in 0..n]\n" ++
  "    relation Product(a: [[F; n]; n], b: [[F; n]; n], c: [[F; n]; n]):\n" ++
  "        ∀ i ∈ 0..n, ∀ j ∈ 0..n, (∑ k ∈ 0..n, a[i][k] * b[k][j]) == c[i][j]\n" ++
  "    protocol Freivalds roles(P, V)(a: [[F; n]; n] @(P, V), b: [[F; n]; n] @(P, V), c: [[F; n]; n] @(P, V)):\n" ++
  "        r <- draw [F; n] from V to P\n" ++
  "        guard @V apply(a, apply(b, r)) == apply(c, r)\n" ++
  "    spec for Freivalds:\n" ++
  "        proves @V Product(a, b, c)\n" ++
  "        charge sites.r <= 1 / F::Order\n" ++
  "scheme Checked = Freivalds<2>:\n    prover P\n    construction interactive\n" ++
  "goal sound = soundness(Checked)\n"

/-- The data module that the issuer writes for a goal of a source, in the name space `space`. -/
def dataOf (text goal space : String) : IO Publication := do
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" text⟩
    ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly goal)
  let claims ← IO.ofExcept (goalClaims root [goal])
  let issued ← IO.ofExcept ((⟨claims⟩ : Statements).publication space)
  unless issued.refusals.isEmpty do throw (IO.userError s!"{issued.refusals}")
  return issued

/-- A row of the register: a protocol at a role, or a function, by the key of its header. -/
inductive Row where
  | protocol (key role : Nat)
  | function (key : Nat)

/-- The line that `#registered_forms` prints for a row in the name space `space`. -/
def Row.line (space : String) : Row → String
  | .protocol key role => s!"protocol {key} role {role}: {space}.protocol{key}.role{role}.form"
  | .function key => s!"function {key}: {space}.function{key}.form"

/-- The equation of a row. -/
def Row.equation : Row → String
  | .protocol key role => s!"protocol{key}.role{role}.reads"
  | .function key => s!"function{key}.reads"

def run (corpus work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let blocks := readBlocks (← IO.FS.readFile corpus)
  let some count := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing the reference case N-GL2a")
  -- each subject with the rows that its register is to hold, in the order of the listing
  let subjects : List (String × String × String × List Row) := [
    -- the root `Guess` at the verifier; the relation `Holds`
    ("Guess", guess, "guessing", [.protocol 0 1, .function 1]),
    -- the relation `Holds`; the root `Either` at the verifier
    ("Either", either, "either", [.function 0, .protocol 1 1]),
    -- the relation `Holds`; the root `Steps` at the verifier
    ("Steps", stepped, "stepped", [.function 0, .protocol 1 1]),
    -- the relation `Holds`; the function `same`; `Round` at the verifier; the root `Twice`
    ("Twice", twice, "twice",
      [.function 0, .function 1, .protocol 2 1, .protocol 3 1]),
    -- the relation; `same`; `Round`, `Pair` and the root `Nested`, each once, at the verifier
    ("Nested", nested, "nested",
      [.function 0, .function 1, .protocol 2 1, .protocol 3 1, .protocol 4 1]),
    -- the relation; `Round` at its role 0, which the root's verifier plays; the root `Swapped`
    ("Swapped", swapped, "swapped", [.function 0, .protocol 1 0, .protocol 2 1]),
    -- the relation; `Round` at its role 1, which the root's verifier plays; the root `Seen`
    ("Seen", seen, "seen", [.function 0, .protocol 1 1, .protocol 2 1]),
    -- the relation `Holds`; the root `Chain` at the verifier
    ("Chain", chained, "chained", [.function 0, .protocol 1 1]),
    -- the relation `Holds`; the root `Gather` at the verifier
    ("Gather", gathered, "gathered", [.function 0, .protocol 1 1]),
    -- the root `Freivalds` at the verifier; the function `apply`; the relation `Product`
    ("Freivalds", freivalds, "sound", [.protocol 1 1, .function 2, .function 3]),
    -- the root `Count` at the verifier; the relation `NearZero`
    ("Count", count, "loose", [.protocol 1 1, .function 3])]
  for (space, text, goal, rows) in subjects do
    let issued ← dataOf text goal space
    discard <| SubjectProject.add project issued.dataName issued.data .statements
    discard <| SubjectProject.add project s!"{space}Forms".toName
      (s!"import {issued.dataName}\nimport ZkcFormal.Form.Publish\n\nopen Zkc.Core\n" ++
        s!"namespace {space}\n\npublish_forms written'subject\n\n#registered_forms installed\n\n" ++
        "\n".intercalate (rows.map fun row => s!"#print axioms {row.equation}") ++
        s!"\n\nend {space}\n")
      .statements
  let control ← dataOf sided "sided" "Sided"
  discard <| SubjectProject.add project control.dataName control.data .statements
  discard <| SubjectProject.add project `SidedForms
    (s!"import {control.dataName}\nimport ZkcFormal.Form.Publish\n\nopen Zkc.Core\n" ++
      "namespace Sided\n\npublish_forms written'subject\n\nend Sided\n") .statements
  -- A second control: the data module of Twice without the lines that mark its headers
  -- reducible. The types of a definition's inputs and results are then not read by a tactic,
  -- and the producer refuses the form before the kernel sees it.
  let bare ← dataOf twice "twice" "Bare"
  let unmarked := "\n".intercalate
    ((bare.data.splitOn "\n").filter fun line => !line.startsWith "attribute [reducible] header")
  if unmarked == bare.data then
    throw (IO.userError "Bare: the data module has no line that marks a header reducible")
  discard <| SubjectProject.add project bare.dataName unmarked .statements
  discard <| SubjectProject.add project `BareForms
    (s!"import {bare.dataName}\nimport ZkcFormal.Form.Publish\n\nopen Zkc.Core\n" ++
      "namespace Bare\n\npublish_forms written'subject\n\nend Bare\n") .statements
  for (space, _, _, rows) in subjects do
    let (ok, output) ← SubjectProject.result project s!"{space}Forms".toName
    unless ok do throw (IO.userError s!"{space}: the forms of the subject are refused\n{output}")
    let listing := "registered forms:\n" ++ "\n".intercalate (rows.map (·.line space)) ++ "\n"
    unless (output ++ "\n").contains listing do
      throw (IO.userError s!"{space}: the register does not hold the expected rows\n{output}")
    for row in rows do
      let rests := s!"'{space}.{row.equation}' depends on axioms: [propext, Quot.sound]"
      unless output.contains rests do
        throw (IO.userError
          s!"{space}: the equation {row.equation} does not rest on propext and Quot.sound alone\n{output}")
    IO.println s!"{space}: {rows.length} forms registered, each with its equation accepted"
  -- A control: a construct that the walk does not read refuses the subject's forms, and the
  -- refusal names the construct.
  let (ok, output) ← SubjectProject.result project `SidedForms
  if ok then throw (IO.userError "Sided: forms were published of a program with a construct that the walk does not read")
  unless output.contains "the walk does not read a choice among the alternatives of a variant" &&
      output.contains "`Instr.cases`" do
    throw (IO.userError s!"Sided: the refusal does not name the construct\n{output}")
  IO.println "Sided: refused (a choice among the alternatives of a variant is named as not read)"
  let (ok, output) ← SubjectProject.result project `BareForms
  if ok then throw (IO.userError "Bare: forms were published over headers that a tactic does not read")
  unless output.contains "is not type-correct as a tactic compares types" do
    throw (IO.userError s!"Bare: the refusal is not the producer's check of the form's types\n{output}")
  IO.println "Bare: refused (a form over headers that are not reducible fails the producer's check of its types)"

end ProgramForms

#eval show IO Unit from do
  let corpus := "../../language/conformance/layer-b.txt"
  match ← IO.getEnv "ZKC_WORK" with
  | some work => ProgramForms.run corpus work
  | none => IO.FS.withTempDir (ProgramForms.run corpus)
