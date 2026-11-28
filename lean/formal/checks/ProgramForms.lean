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
calls a function (Twice), a vector of scalars drawn and three applications of a function over
matrices (Freivalds), and the conformance corpus's count of near-zero entries (Count). A
control has a construct that the walk does not read (a `match` on a variant): its forms are
refused, and the refusal names the construct.

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
    ("Guess", guess, "guessing", [.protocol 0 1, .function 1]),
    ("Either", either, "either", [.function 0, .protocol 1 1]),
    ("Steps", stepped, "stepped", [.function 0, .protocol 1 1]),
    ("Twice", twice, "twice",
      [.function 0, .function 1, .protocol 2 1, .protocol 3 1]),
    ("Freivalds", freivalds, "sound", [.protocol 1 1, .function 2, .function 3]),
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

end ProgramForms

#eval show IO Unit from do
  let corpus := "../../language/conformance/layer-b.txt"
  match ← IO.getEnv "ZKC_WORK" with
  | some work => ProgramForms.run corpus work
  | none => IO.FS.withTempDir (ProgramForms.run corpus)
