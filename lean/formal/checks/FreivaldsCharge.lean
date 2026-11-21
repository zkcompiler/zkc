import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project

/-!
Freivalds' check of a matrix product, judged within the charge that its source declares.

The subject is `Freivalds<2>`: the verifier draws a vector `r` of two scalars and returns when
`apply(a, apply(b, r)) == apply(c, r)`, where `apply` is the product of a matrix and a vector;
its relation `Product(a, b, c)` holds when the product of `a` and `b` is `c`; its charge on the
draw is `1 / F::Order`. It is the second subject of a written soundness goal, and differs from
`Count<8>` in what the proof has to read: a function that the verifier calls three times, a
relation of three nested loops, a draw of a sequence of scalars, and a charge that depends on
the size of the field.

The check reads the source with the frontend and writes modules on which Lean is run.

- The proof module has the printed package of what the goal claims and, around the text of
  `FreivaldsCharge.lean.in`, what `Written.Statements` writes: the facts, with those of the
  function that the root calls under its name in the source; that the arithmetic model covers
  the package; the transfers; the claim `soundClaim`; and the goal `sound_sound` for every
  admitted program. The claim is over the arithmetic model on every field that can be sampled
  and has at least as many elements as the scalar field of the source
  (`scalarFieldModelText`). The text proves the claim. It says what `apply` and `Product`
  compute, each loop taken by an invariant (`walk_loop`); the verifier is walked once, its
  three calls taken by the law of `apply` (`walk_compute`), and is judged never to return
  within the budget of the charge on matrices whose product differs; against every service
  that draws each coin by the sampler of its law, it returns with probability at most the
  total of the charge. The hypotheses are met over the scalar field of the source, on the zero
  matrices and a matrix with one entry.
- The comparison module has the same printed package and the frontend: the program by names
  and the association that Lean reads from the package are those that the frontend gives to
  admission for the claims.

What the source says and the proof module takes as given is asserted here against the source:
the clause that the goal reads and the ports that the relation is applied to.

Four controls are refused by Lean, each for the theorems that depend on what it changes: the
operands of the relation exchanged in the clause (`Product(b, a, c)`: the claim is then about
another product, and the text does not prove it); a charge of half the source's; the claim
without the hypothesis on the size of the field; and the coverage of the package by the
standard model, which has no sampler for a sequence of scalars.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace FreivaldsCharge

/-- The source, with a clause. -/
def source (clause : String) : String :=
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
  s!"        proves @V {clause}\n" ++
  "        charge sites.r <= 1 / F::Order\n" ++
  "scheme Checked = Freivalds<2>:\n    prover P\n    construction interactive\n" ++
  "goal sound = soundness(Checked)\n"

/-- What the check reads of a source: what its goal claims, with what the statement needs. -/
structure Subject where
  text : String
  statements : Statements

/-- The printed package of the claims. -/
def Subject.package (s : Subject) : String := (Written.package s.statements.package).text

def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- A source read: the goal selects the root; it reads the clause `proves @V Product(…)` with
the given operands, decided by the verifier of the scheme, on the three ports of the protocol;
it gives no proof argument; and it has a charge on the draw `r`. -/
def read (text : String) (operands : List String) : IO Subject := do
  let c ← IO.ofExcept (goalRoot text "sound")
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == #["a", "b", "c"] do
    throw (IO.userError "the protocol has other ports than the three matrices")
  let claims ← IO.ofExcept (goalClaims c ["sound"])
  let [claimed] := claims.goals | throw (IO.userError "the claims are not of one goal")
  let clause ← IO.ofExcept (SourceClause.seen c "sound")
  unless clause == ⟨"proves", none, "V", "Product", operands, []⟩ do
    throw (IO.userError s!"the goal reads another clause: {repr clause}")
  unless claimed.witness == some #[] do
    throw (IO.userError "the relation has witness parameters")
  let (selected, _) ← IO.ofExcept (selectNamedGoal c.state "sound" .soundness)
  unless selected.specification.isEmpty do
    throw (IO.userError "the goal gives proof arguments")
  let charge ← IO.ofExcept (goalDrawCharge c "sound" [] "r")
  let some verifier := (← IO.ofExcept (goalClause c "sound")).role
    | throw (IO.userError "the clause has no deciding role")
  let some prover := head.roster.toList.idxOf? "P" | throw (IO.userError "the roster has no prover")
  let goal : StatedGoal :=
    { claimed, specification := selected.specification, charge, ceiling := selected.ceiling }
  return ⟨text, ⟨claims, [("verifier", verifier), ("prover", prover)], [goal],
    claims.functionsBeforeRoot⟩⟩

/-- The theorems of the proof module, whose axioms the check reads. -/
def theorems : List String := [
  "covered", "verifier.eq", "apply_law", "sound_relation", "sound_far", "walked_within",
  "walked_excludes", "meaning_walked", "returns_installed", "large_covers", "sound_installed",
  "sound_sound", "Witness.rejected", "Witness.sound_at_corner"]

/-- The claim and what rests on it. -/
def ofClaim : List String := ["sound_installed", "sound_sound", "Witness.sound_at_corner"]

/-- The proof module over a model: the package of the claims; what the frontend read, the
coverage, the transfers and the claim, all generated; the proofs written for the protocol; and
the goal for every admitted program, generated. -/
def proofModule (name : String) (s : Subject) (model : ModelText) (template : String) :
    IO String := do
  let stated := s.statements
  let claims ← IO.ofExcept (stated.claimTexts model)
  let closings ← IO.ofExcept (stated.closings model)
  return packageHeader ["Zkc.Formal.Walk", "Zkc.Formal.OracleProcess",
      "Zkc.Formal.Written.LawSamplers", "Zkc.Formal.Written.SiteAllowance",
      "Zkc.Formal.Written.FunctionMeaning", "Zkc.Formal.Written.ArithmeticDraws",
      "Zkc.Formal.Written.FixedSequences", "Zkc.Formal.Written.ScalarField",
      "Mathlib.Data.Matrix.Mul"] ++
    s!"namespace {name}\n" ++ s.package ++ Statements.opens ++ stated.facts ++ "\n" ++
    Statements.coverage model ++ stated.transfers ++ claims ++ template ++ "\n" ++ closings ++
    String.join (theorems.map (s!"#print axioms {·}\n")) ++ s!"end {name}\n"

/-- A module with the package of a subject and the one theorem that a model covers it. -/
def coverageModule (name : String) (s : Subject) (model : ModelText) : String :=
  packageHeader ["Zkc.Formal.Written.ArithmeticDraws"] ++ s!"namespace {name}\n" ++ s.package ++
  "open Zkc.Formal.Written\n" ++ Statements.coverage model ++
  s!"#print axioms covered\nend {name}\n"

def comparisonModule (name : String) (s : Subject) : String :=
  packageHeader ["Zkc.Tests.Frontend.PrintedPackageSupport"] ++ s!"namespace {name}\n" ++ s.package ++
  s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectGoalClaims {literal s.text} " ++
  s!"[\"sound\"] ({Written.associationTerm noAssociation}) stored association\nend {name}\n"

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let written ← read (source "Product(a, b, c)") ["a", "b", "c"]
  let stated := written.statements
  let [goal] := stated.goals | throw (IO.userError "the statements are not of one goal")
  unless stated.claims.root == 1 && stated.roles == [("verifier", 1), ("prover", 0)] do
    throw (IO.userError "the root and the roles of the source are not where they were")
  unless stated.functions == [("apply", 2)] do
    throw (IO.userError s!"the root calls other functions than `apply`: {stated.functions}")
  unless goal.claimed.statement == #[0, 1, 2] do
    throw (IO.userError "the relation is applied to other ports than the three matrices in order")
  let order := Zkc.Vocabulary.Field.bls12381Fr.order
  unless (goal.charge.owner.number, goal.charge.numerator, goal.charge.denominator) == (1, 1, order) &&
      goal.charge.draws == [([], ⟨0⟩)] do
    throw (IO.userError "the charge is not one over the order of the scalar field, on the draw of the root")

  -- The operands exchanged: the package and the charge are what they were, and the relation is
  -- applied to the ports in another order.
  let exchanged ← read (source "Product(b, a, c)") ["b", "a", "c"]
  unless exchanged.package == written.package do
    throw (IO.userError "exchanging the operands of the clause changed the package of the claims")
  unless (exchanged.statements.goals.map (·.claimed.statement)) == [#[1, 0, 2]] do
    throw (IO.userError "with the operands exchanged the relation is not applied to the ports exchanged")

  -- A charge of half the source's.
  let halved : Subject := { written with statements := { stated with
    goals := [{ goal with charge := { goal.charge with denominator := 2 * goal.charge.denominator } }] } }

  let proof ← startLakeLean work "Freivalds" (← proofModule "Freivalds" written scalarFieldModelText template)
  let comparison ← startLakeLean work "FreivaldsSource" (comparisonModule "FreivaldsSource" written)
  let exchangedProof ← startLakeLean work "OperandsControl"
    (← proofModule "OperandsControl" exchanged scalarFieldModelText template)
  let halvedProof ← startLakeLean work "BoundControl"
    (← proofModule "BoundControl" halved scalarFieldModelText template)
  let unassumedProof ← startLakeLean work "FieldControl"
    (← proofModule "FieldControl" written arithmeticModelText template)
  let uncoveredProof ← startLakeLean work "CoverageControl"
    (coverageModule "CoverageControl" written standardModelText)

  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  let (ok, output) ← finishLean proof
  acceptedOutput "Freivalds" ok output theorems allowed
  let (ok, output) ← finishLean comparison
  acceptedOutput "FreivaldsSource" ok output []
  -- The claim is about `b * a`: what the text says of `a * b` does not prove it. The laws of
  -- the two functions and the theorems about the verifier stand.
  expectUnproved "the operands exchanged" "OperandsControl" theorems exchangedProof ofClaim
  -- Half the charge is below what a uniform scalar pays for in a field of the source's order.
  expectUnproved "a charge of half" "BoundControl" theorems halvedProof ("large_covers" :: ofClaim)
  -- Without the hypothesis, the field may be smaller than the charge assumes.
  expectUnproved "no hypothesis on the field" "FieldControl" theorems unassumedProof ofClaim
  -- The standard model has no sampler for a sequence of scalars: the kernel decides that it
  -- does not cover the package.
  let (ok, output) ← finishLean uncoveredProof
  if ok then throw (IO.userError "Lean accepted that the standard model covers the package")
  unless output.contains "StandardModel.covers stored = true" && output.contains "is false" do
    throw (IO.userError s!"the coverage control was refused for another reason\n{output}")
  IO.println (s!"Freivalds<2> is judged within the charge of its goal (1/{order}), on the matrices on " ++
    "which the admitted relation returns false, over every field of at least that order; " ++
    "4 of 4 controls refused.")

end FreivaldsCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    FreivaldsCharge.run "checks/FreivaldsCharge.lean.in" work
