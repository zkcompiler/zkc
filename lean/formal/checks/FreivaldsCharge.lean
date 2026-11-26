import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import ZkcFormalTests.WrittenSubject
import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace FreivaldsCharge

/-- The source, with a clause, with ports written in front of the three matrices, and with the
product of an entry and a coordinate that `apply` adds up. -/
def source (clause : String) (front : String := "") (product : String := "m[i][k] * v[k]") :
    String :=
  "module t\n" ++
  "use zkc::security::{soundness}\n" ++
  "type F = primitive(\"bls12-381.fr\")\n" ++
  "section <n: nat>:\n" ++
  s!"    def apply(m: [[F; n]; n], v: [F; n]) -> [F; n]: [∑ k ∈ 0..n, {product} for i in 0..n]\n" ++
  "    relation Product(a: [[F; n]; n], b: [[F; n]; n], c: [[F; n]; n]):\n" ++
  "        ∀ i ∈ 0..n, ∀ j ∈ 0..n, (∑ k ∈ 0..n, a[i][k] * b[k][j]) == c[i][j]\n" ++
  s!"    protocol Freivalds roles(P, V)({front}a: [[F; n]; n] @(P, V), b: [[F; n]; n] @(P, V), c: [[F; n]; n] @(P, V)):\n" ++
  "        r <- draw [F; n] from V to P\n" ++
  "        guard @V apply(a, apply(b, r)) == apply(c, r)\n" ++
  "    spec for Freivalds:\n" ++
  s!"        proves @V {clause}\n" ++
  "        charge sites.r <= 1 / F::Order\n" ++
  "scheme Checked = Freivalds<2>:\n    prover P\n    construction interactive\n" ++
  "goal sound = soundness(Checked)\n"

/-- What the check asserts of what the frontend read of a source of the subject: the goal
selects the root; it reads the clause `proves @V Product(…)` with the given operands, decided
by the verifier of the scheme, on the ports of the protocol, which are the three matrices after
those written in front; the relation is applied to the given inputs of the deployed header; the
goal gives no proof argument. The standard interpretation samples the scalar vector. -/
def reading (operands : List String) (inputs : Array Nat) (front : Array String := #[]) :
    Reading where
  goals := ["sound"]
  ports := front ++ #["a", "b", "c"]
  clause := ⟨"proves", none, "V", "Product", operands, []⟩
  operands := inputs

/-- An action of the check that must end in a refusal. -/
def refuses (title : String) (action : IO Unit) : IO Unit := do
  let refused ← (do action; pure false) <|> pure true
  unless refused do throw (IO.userError s!"{title}: not refused")

def run (work : System.FilePath) : IO Unit := do
  let inOrder := reading ["a", "b", "c"] #[0, 1, 2]
  let written ← read (source "Product(a, b, c)") inOrder
  let stated := written.statements
  let goal ← written.goal
  unless stated.claims.root == 1 && (stated.claims.verifier, stated.claims.prover) == (1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")
  unless stated.functions == [("apply", 2)] do
    throw (IO.userError s!"the root calls other functions than `apply`: {stated.functions}")
  let order := Zkc.Vocabulary.Field.bls12381Fr.order
  unless goal.caps == ⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, order, 1⟩] [])]⟩ do
    throw (IO.userError "the table of caps is not one over the order of the scalar field, on the draw of the root, once")

  -- The operands exchanged: the package and the charge are what they were, and the relation is
  -- applied to the ports in another order.
  let exchanged ← read (source "Product(b, a, c)") (reading ["b", "a", "c"] #[1, 0, 2])
  unless exchanged.package == written.package do
    throw (IO.userError "exchanging the operands of the clause changed the package of the claims")

  -- A charge of half the source's, in the source: the program is what it was, and the cap of
  -- the draw is half.
  let halved ← read (← replaceOnce (source "Product(a, b, c)") "charge sites.r <= 1 / F::Order"
    "charge sites.r <= 1 / (2 * F::Order)") inOrder
  unless halved.package == written.package &&
      (halved.goals.map (·.caps)) == [⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 2 * order, 1⟩] [])]⟩] do
    throw (IO.userError "the halved charge changed the package, or is not half at the draw")

  -- The product computed another way: the vector is read before the matrix, and a term is
  -- added that cancels. The deployed function is another, and what the goal claims is the same.
  let rewritten ← read (source "Product(a, b, c)" (product := "v[k] * m[i][k] + (v[k] - v[k])"))
    inOrder
  -- A sum where the product stands: another function, which is not the product of a matrix
  -- and a vector.
  let summed ← read (source "Product(a, b, c)" (product := "v[k] + m[i][k]")) inOrder
  for (title, altered) in [("computed another way", rewritten), ("replaced by a sum", summed)] do
    if altered.package == written.package then
      throw (IO.userError s!"the product {title}: the package is what it was")
    unless (altered.goals.map fun goal => (goal.statement, goal.caps)) ==
        [(goal.statement, goal.caps)] do
      throw (IO.userError s!"the product {title}: the goal claims something else")

  -- The actual coverage theorem is about the goal's own two keys.
  let badCoverage ← startLakeLean work "CoverageControl"
    ((← IO.ofExcept (written.statements.coverageModule "CoverageControl")).text.replace
      "covers stored rootKey soundKey = true" "covers stored ⟨999⟩ soundKey = true")

  -- The reading of Lean's output: a report of axioms that stands twice is not read.
  let report := "'Freivalds.sound_covered' depends on axioms: [propext]\n"
  acceptedOutput "Freivalds" true report ["sound_covered"] allowed
  refuses "a report of axioms printed again"
    (acceptedOutput "Freivalds" true
      (report ++ "'Freivalds.sound_covered' does not depend on any axioms\n") ["sound_covered"] allowed)
  -- The lookup at the altered root key has no definition.
  let (ok, output) ← finishLean badCoverage
  if ok then throw (IO.userError "Lean accepted coverage at an absent root")
  unless output.contains "StandardInterpretation.covers stored" && output.contains "is false" do
    throw (IO.userError s!"the coverage control was refused for another reason\n{output}")

end FreivaldsCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    FreivaldsCharge.run work
