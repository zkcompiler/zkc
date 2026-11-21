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
Freivalds' check of a matrix product, judged within the table of caps that the frontend reads
for its goal from the charge of its source.

The subject is `Freivalds<2>`: the verifier draws a vector `r` of two scalars and returns when
`apply(a, apply(b, r)) == apply(c, r)`, where `apply` is the product of a matrix and a vector;
its relation `Product(a, b, c)` holds when the product of `a` and `b` is `c`; its charge on the
draw is `1 / F::Order`. It is the second subject of a written soundness goal, and differs from
`Count<8>` in what the proof has to read: a function that the verifier calls three times, a
relation of three nested loops, a draw of a sequence of scalars, and a charge that depends on
the size of the field.

The check reads the source with the frontend and writes modules on which Lean is run.

- The proof module has the printed package of what the goal claims and, around the text of
  `FreivaldsCharge.lean.in`, what `Written.Statements` writes. Before the text: the facts, with
  those of the function that the root calls under its name in the source; that the arithmetic
  model covers the package; where the walks start; the transfers; and four propositions, the
  claim about the installed program (`soundClaim`), the goal for every admitted program
  (`soundGoal`), the result with the coverage (`soundResult`), and that the hypotheses of the
  claim are met together (`soundWitnessed`). After the text: the theorems of the last three.
  The claim is over the arithmetic model on every finite field with a decidable equality that
  can be sampled and has at least as many elements as the scalar field of the source, with any
  module over it for the type of group points (`scalarFieldModelText`). The text proves the
  claim and the witness. It says what `apply` and `Product` compute, each loop taken by an
  invariant (`walk_loop`); the verifier is walked with its three calls taken by the law of
  `apply` (`walk_compute`), once for the judgment and once on a hypothesis for its converse,
  and is judged never to return within the budget of the goal's table (`soundCaps`: the root
  with the cap of its draw, once, and its three calls of `apply`, which has no charge) on
  matrices whose product differs; against every service that is no more likely to answer a coin
  within a set of replies than the sampler of the coin's law is to draw one there, it returns
  with probability at most the total of the table. On matrices whose product holds every permitted vector
  leads it to return. The hypotheses are met over the scalar field of the source, on the zero
  matrices and a matrix with one entry, and there it returns with a probability that is not
  zero.
- The comparison module has the same printed package and the frontend: the program by names
  and the association that Lean reads from the package are those that the frontend gives to
  admission for the claims.

What the source says and the proof module takes as given is asserted here against the source:
the clause that the goal reads and the ports that the relation is applied to. The operands of a
claim are inputs of the deployed header, which has no `spec` port: the same source with a
`spec` port that nothing uses in front of the matrices gives the same proof module, character
for character.

Five controls are refused by Lean, each for the theorems that depend on what it changes and at
the line that the check names: the operands of the relation exchanged in the clause
(`Product(b, a, c)`: the claim is then about another product; the text is refused where it
takes from the premise that the product of `a` and `b` differs); a charge of half the source's, written in the source (refused where the cap of the draw
is compared with what a uniform scalar pays for); the hypothesis on the size of the field
weakened to one element or more (refused where that comparison is used); and the coverage of
the package by the standard model, which has no sampler for a sequence of scalars (decided
false by the kernel). The first three show that the text does not prove the altered claim;
none of them refutes it. The fifth is a text and not a claim: one that defines again, in its
own scope, a name that the statement of the goal uses (the experiment `ReturnsWithin`, as a
proposition that always holds) and proves the claim written anew under it. Every statement of the module is a proposition defined before the
text, so the goal is not concluded from that proof.

The check trusts the text in two ways that it does not test: that it prints nothing that reads
as Lean's report of the axioms of a theorem (a report is read only where there is exactly
one), and that it declares no syntax that changes what the closing theorems mean. It refuses a
text that sets an option for debugging, one of which has the kernel skip a declaration.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace FreivaldsCharge

/-- The source, with a clause, and with ports written in front of the three matrices. -/
def source (clause : String) (front : String := "") : String :=
  "module t\n" ++
  "use zkc::security::{soundness}\n" ++
  "type F = primitive(\"bls12-381.fr\")\n" ++
  "section <n: nat>:\n" ++
  "    def apply(m: [[F; n]; n], v: [F; n]) -> [F; n]: [∑ k ∈ 0..n, m[i][k] * v[k] for i in 0..n]\n" ++
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

/-- What the check reads of a source: what its goal claims, with what the statement needs. -/
structure Subject where
  text : String
  statements : Statements

/-- The printed package of the claims. -/
def Subject.package (s : Subject) : String := (Written.package s.statements.package).text

def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- A source read: the goal selects the root; it reads the clause `proves @V Product(…)` with
the given operands, decided by the verifier of the scheme, on the ports of the protocol, which
are the three matrices after those written in front; and it gives no proof argument. The table
of caps of the goal is read with its claim. -/
def read (text : String) (operands : List String) (front : Array String := #[]) : IO Subject := do
  let c ← IO.ofExcept (goalRoot text "sound")
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == front ++ #["a", "b", "c"] do
    throw (IO.userError "the protocol has other ports than the three matrices")
  let claims ← IO.ofExcept (goalClaims c ["sound"])
  let [claimed] := claims.goals | throw (IO.userError "the claims are not of one goal")
  let clause ← IO.ofExcept (SourceClause.seen c "sound")
  unless clause == ⟨"proves", none, "V", "Product", operands, []⟩ do
    throw (IO.userError s!"the goal reads another clause: {repr clause}")
  unless claimed.witness == some #[] do
    throw (IO.userError "the relation has witness parameters")
  unless claimed.specification.isEmpty do
    throw (IO.userError "the goal gives proof arguments")
  unless (head.roster[claims.verifier]?, head.roster[claims.prover]?) == (some "V", some "P") do
    throw (IO.userError "the verifier and the prover of the scheme are not the roles V and P")
  return ⟨text, ⟨claims, claims.functionsBeforeRoot⟩⟩

/-- The theorems of the text of the proofs. -/
def ofText : List String := [
  "sound_within", "apply_law", "sound_relation", "sound_far", "returns_on_product",
  "walked_within", "walked_excludes", "returns_possible", "returns_installed", "large_covers",
  "sound_installed", "Witness.rejected", "Witness.sound_at_corner", "Witness.returns_at_corner",
  "sound_witnessed"]

/-- The claim and what rests on it. -/
def ofClaim : List String :=
  ["sound_installed", "Witness.sound_at_corner", "sound_sound", "sound_result"]

/-- The proof module over a model, as the generator assembles it: the package of the claims
and what is generated around the proofs written for the protocol, which use the fixed
sequences of the library and Mathlib's matrices. -/
def proofModule (name : String) (s : Subject) (model : ModelText) (template : String) :
    IO Module :=
  IO.ofExcept (s.statements.module model name
    { text := template, theorems := ofText
      imports := ["Zkc.Formal.Written.FixedSequences", "Mathlib.Data.Matrix.Mul"] })

/-- A text that defines again, in its own scope, a name of the library that the statement of
the goal uses, and proves the claim written anew under that name: the experiment of a bound on
returns, as a proposition that holds of everything. Before the statements of a module were
propositions defined ahead of the text, the goal that such a text published was the claim under
the text's own name, and every check passed (found by an audit, with the total of a charge as
the name). The claim written anew is not the claim that was stated, so the text is refused
where the goal is concluded from it. -/
def shadowing (s : Subject) (model : ModelText) (template : String) : IO String := do
  let [goal] := s.statements.claims.goals | throw (IO.userError "the statements are not of one goal")
  let anew ← IO.ofExcept (s.statements.claimAt model goal "installed" "rootMember" "soundMember")
  let established := template.replace "theorem sound_installed : soundClaim := by"
    "theorem sound_established : soundClaim := by"
  if established == template then
    throw (IO.userError "the text does not prove the claim under its name")
  -- what the text concludes from the claim, it concludes from the claim as it was stated
  let renamed := established.replace "  (sound_installed (F := Scalars)" "  (sound_established (F := Scalars)"
  if renamed == established then
    throw (IO.userError "the text does not use the claim at its witness")
  return renamed ++ "\n" ++
    "def ReturnsWithin {S : Sig} {H A : Type} (_ : Process S H A) (_ : Samplers S)\n" ++
    "    (_ : ∀ op, S.Reply op → Prop) (_ : A → Prop) (_ : ℝ≥0∞) : Prop := True\n\n" ++
    s!"theorem sound_installed :\n  {anew} := by\n" ++
    "  intros\n  trivial\n"

/-- A control is refused where it is meant to be: Lean's output has the line. -/
def expectReason (title : String) (task : Task (Except IO.Error (Bool × String)))
    (line : String) : IO Unit := do
  let (_, output) ← finishLean task
  unless output.contains line do
    throw (IO.userError s!"{title}: refused for another reason than `{line}`\n{output}")

/-- An action of the check that must end in a refusal. -/
def refuses (title : String) (action : IO Unit) : IO Unit := do
  let refused ← (do action; pure false) <|> pure true
  unless refused do throw (IO.userError s!"{title}: not refused")

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let written ← read (source "Product(a, b, c)") ["a", "b", "c"]
  let stated := written.statements
  let [goal] := stated.claims.goals | throw (IO.userError "the statements are not of one goal")
  unless stated.claims.root == 1 && (stated.claims.verifier, stated.claims.prover) == (1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")
  unless stated.functions == [("apply", 2)] do
    throw (IO.userError s!"the root calls other functions than `apply`: {stated.functions}")
  unless goal.statement == #[0, 1, 2] do
    throw (IO.userError "the relation is applied to other ports than the three matrices in order")
  let order := Zkc.Vocabulary.Field.bls12381Fr.order
  unless goal.caps == ⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, order, 1⟩], []⟩]⟩ do
    throw (IO.userError "the table of caps is not one over the order of the scalar field, on the draw of the root, once")

  -- The operands exchanged: the package and the charge are what they were, and the relation is
  -- applied to the ports in another order.
  let exchanged ← read (source "Product(b, a, c)") ["b", "a", "c"]
  unless exchanged.package == written.package do
    throw (IO.userError "exchanging the operands of the clause changed the package of the claims")
  unless (exchanged.statements.claims.goals.map (·.statement)) == [#[1, 0, 2]] do
    throw (IO.userError "with the operands exchanged the relation is not applied to the ports exchanged")

  -- A `spec` port in front of the matrices, which nothing uses: the operands are the same
  -- inputs of the deployed header, and the proof module is the same text.
  let fronted ← read (source "Product(a, b, c)" "spec note: bool, ") ["a", "b", "c"] #["note"]
  unless (fronted.statements.claims.goals.map (·.statement)) == [#[0, 1, 2]] do
    throw (IO.userError "with a spec port in front the relation is applied to other inputs")
  let module ← proofModule "Freivalds" written scalarFieldModelText template
  let theorems := module.theorems
  unless (← proofModule "Freivalds" fronted scalarFieldModelText template).text == module.text do
    throw (IO.userError "a spec port in front of the matrices changed the proof module")

  -- A charge of half the source's, in the source: the program is what it was, and the cap of
  -- the draw is half.
  let halved ← read ((source "Product(a, b, c)").replace "charge sites.r <= 1 / F::Order"
    "charge sites.r <= 1 / (2 * F::Order)") ["a", "b", "c"]
  unless halved.package == written.package &&
      (halved.statements.claims.goals.map (·.caps)) == [⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 2 * order, 1⟩], []⟩]⟩] do
    throw (IO.userError "the halved charge changed the package, or is not half at the draw")

  let proof ← startLakeLean work "Freivalds" module.text
  let comparison ← startLakeLean work "FreivaldsSource" (comparisonModule "FreivaldsSource" written.text ["sound"] written.package)
  let exchangedProof ← startLakeLean work "OperandsControl"
    (← proofModule "OperandsControl" exchanged scalarFieldModelText template).text
  let halvedProof ← startLakeLean work "BoundControl"
    (← proofModule "BoundControl" halved scalarFieldModelText template).text
  -- The hypothesis on the field weakened to a field of one element or more.
  let anyField : ModelText :=
    { scalarFieldModelText with hypotheses := [("large", "1 ≤ Fintype.card F")] }
  let unassumedProof ← startLakeLean work "FieldControl"
    (← proofModule "FieldControl" written anyField template).text
  let uncoveredProof ← startLakeLean work "CoverageControl"
    (written.statements.coverageModule standardModelText "CoverageControl").text
  let shadowedProof ← startLakeLean work "ShadowControl"
    (← proofModule "ShadowControl" written scalarFieldModelText
      (← shadowing written scalarFieldModelText template)).text

  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  let (ok, output) ← finishLean proof
  acceptedOutput "Freivalds" ok output theorems allowed
  -- The reading of Lean's output: a report of axioms that stands twice is not read, and a text
  -- with an option for debugging is not run.
  refuses "a report of axioms printed again"
    (acceptedOutput "Freivalds" ok
      (output ++ "'Freivalds.sound_sound' does not depend on any axioms\n") theorems allowed)
  refuses "a text with an option for debugging"
    (discard (proofModule "Freivalds" written scalarFieldModelText
      (template ++ "set_option debug.skipKernelTC true in\n")))
  let (ok, output) ← finishLean comparison
  acceptedOutput "FreivaldsSource" ok output []
  -- The claim is about `b * a`: its premise is not the one from which the text gets that the
  -- product of `a` and `b` differs. The laws of the two functions and the theorems about the
  -- verifier stand.
  expectUnproved "the operands exchanged" "OperandsControl" theorems exchangedProof ofClaim
  expectReason "the operands exchanged" exchangedProof "sound_far G a b c A B C ha hb hc rejected"
  -- The ceiling of half the charge is not one over the order: the comparison with what a
  -- uniform scalar pays for is not proved.
  expectUnproved "a charge of half" "BoundControl" theorems halvedProof ("large_covers" :: ofClaim)
  expectReason "a charge of half" halvedProof "drawCap soundCaps ="
  -- A field of one element or more is not a field of the source's order or more: the
  -- comparison of the ceiling is not available where the claim needs it.
  -- The witness of the text is of the hypothesis that was stated, so it is not a witness here.
  expectUnproved "a weaker hypothesis on the field" "FieldControl" theorems unassumedProof
    ["sound_installed", "Witness.sound_at_corner", "sound_witnessed", "sound_sound",
      "sound_result", "sound_met"]
  expectReason "a weaker hypothesis on the field" unassumedProof "large_covers large"
  -- A name of the library defined again by the text: the claim that the text then proves is not
  -- the claim that was stated before it, and the goal is not concluded from it.
  expectUnproved "a name of the statement defined again" "ShadowControl" theorems shadowedProof
    ["sound_sound", "sound_result"]
  expectReason "a name of the statement defined again" shadowedProof "sound_installed"
  -- The standard model has no sampler for a sequence of scalars: the kernel decides that it
  -- does not cover the package.
  let (ok, output) ← finishLean uncoveredProof
  if ok then throw (IO.userError "Lean accepted that the standard model covers the package")
  unless output.contains "StandardModel.covers stored = true" && output.contains "is false" do
    throw (IO.userError s!"the coverage control was refused for another reason\n{output}")
  IO.println (s!"Freivalds<2> is judged within the table of caps of its goal (the draw at 1/{order}), on the matrices on " ++
    "which the admitted relation returns false, over every field of at least that order; " ++
    "5 of 5 controls refused, each at its line.")

end FreivaldsCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    FreivaldsCharge.run "checks/FreivaldsCharge.lean.in" work
