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
  claim are met together (`soundWitnessed`); and the judgment that establishes the claim
  (`soundJudged`) with the theorem that the claim follows from it. After the text: the claim
  from the judgment that the text proved, and the theorems of the last three.
  The claim is over the arithmetic model on every finite field with a decidable equality that
  can be sampled and has at least as many elements as the scalar field of the source, with any
  module over it for the type of group points (`scalarFieldModelText`). The text proves the
  judgment and gives the witness. It says what `apply` and `Product` compute, each loop taken by an
  invariant (`walk_loop`); the verifier is walked with its three calls taken by the law of
  `apply` (`walk_law`), once for the judgment and once on a hypothesis for its converse,
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

The text follows the mathematics of the program and not its instructions. The same text,
character for character, is accepted on a source whose `apply` computes each product another
way: the vector read before the matrix, and a term added that cancels
(`v[k] * m[i][k] + (v[k] - v[k])`), which reads the vector twice more and changes every name
that the compiler gives a value. A walk reads each entry by the bounds of the loops, in
whatever order the program reads, and what is left of a step is an equation in the field,
which `ring` proves. On a source whose `apply` adds where it should multiply
(`v[k] + m[i][k]`) the same text is refused at one place, that equation, and nothing that
rests on the law of `apply` is proved.

What the source says and the proof module takes as given is asserted here against the source:
the clause that the goal reads and the ports that the relation is applied to. The operands of a
claim are inputs of the deployed header, which has no `spec` port: the same source with a
`spec` port that nothing uses in front of the matrices gives the same proof module, character
for character.

Six controls are refused by Lean, each for the theorems that depend on what it changes and at
the line that the check names: the sum for the product, above; the operands of the relation exchanged in the clause
(`Product(b, a, c)`: the claim is then about another product; the text is refused where it
takes from the premise that the product of `a` and `b` differs); a charge of half the source's, written in the source (refused where the cap of the draw
is compared with what a uniform scalar pays for); the hypothesis on the size of the field
weakened to one element or more (refused where that comparison is used); and the coverage of
the package by the standard model, which has no sampler for a sequence of scalars (decided
false by the kernel). The three after the first show that the text does not prove the
altered claim; none of them refutes it. The sixth is a text and not a claim: one that defines again, in its
own scope, a name that the judgment of the goal uses (the fees within allowances `paysWithin`,
as a policy under which every fee pays for every set of replies) and proves the judgment
written anew under it. Every statement of the module is a proposition defined before the text,
so the claim is not concluded from that proof: Lean refuses the generated conclusion at one
place, as a mismatch of types.

The check trusts the text in two ways that it does not test: that it prints nothing that reads
as Lean's report of the axioms of a theorem (a report is read only where there is exactly
one), and that it declares no syntax that changes what the closing theorems mean. It refuses a
text that sets an option for debugging, one of which has the kernel skip a declaration. That
the theorems after the text state their propositions, and not those under a hypothesis that
the text declared for its scope, is read from what Lean stored (`published`); the check of
`Guess<3>` has the control.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

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
  "walked_within", "walked_excludes", "returns_possible", "large_covers",
  "sound_judged", "Witness.rejected", "Witness.sound_at_corner", "Witness.returns_at_corner",
  "sound_witnessed"]

/-- The law of `apply` and what rests on it: the verifier is walked by that law. -/
def ofApply : List String :=
  ["apply_law", "returns_on_product", "walked_within", "walked_excludes", "returns_possible",
    "sound_judged", "sound_installed", "Witness.sound_at_corner", "Witness.returns_at_corner",
    "sound_sound", "sound_result"]

/-- The claim and what rests on it. -/
def ofClaim : List String :=
  ["sound_judged", "sound_installed", "Witness.sound_at_corner", "sound_sound", "sound_result"]

/-- The proof module over a model, as the generator assembles it: the package of the claims
and what is generated around the proofs written for the protocol, which use the fixed
sequences of the library and Mathlib's matrices. -/
def proofModule (name : String) (s : Subject) (model : ModelText) (template : String) :
    IO Module :=
  IO.ofExcept (s.statements.module model name
    { text := template, theorems := ofText
      imports := ["Zkc.Formal.Written.FixedSequences", "Mathlib.Data.Matrix.Mul"] })

/-- A text that defines again, in its own scope, a name of the library that the statement of
the goal's judgment uses, and proves the judgment written anew under that name: the fees within
allowances, as a policy under which every fee pays for every set of replies. Under it the
verifier is judged at its first effect, with no fee and every reply excluded. The judgment
written anew is not the judgment that was stated before the text, so the text is refused where
the claim is concluded from it. (An audit found the same of the claim: before the statements of
a module were propositions defined ahead of the text, a text that defined the total of a charge
again published a goal under its own name, and every check passed.) -/
def shadowing (s : Subject) (model : ModelText) (template : String) : IO String := do
  let [goal] := s.statements.claims.goals | throw (IO.userError "the statements are not of one goal")
  let anew ← IO.ofExcept (s.statements.judgedAt model goal)
  let established := template.replace "theorem sound_judged : soundJudged := by"
    "theorem sound_established : soundJudged := by"
  if established == template then
    throw (IO.userError "the text does not prove the judgment under its name")
  -- what the text concludes from the judgment, it concludes from the judgment as it was stated
  let renamed := established.replace "  (sound_claim_of_judged sound_judged (F := Scalars)"
    "  (sound_claim_of_judged sound_established (F := Scalars)"
  if renamed == established then
    throw (IO.userError "the text does not use the claim at its witness")
  return renamed ++ "\n" ++
    "def paysWithin {S : Sig} (_ : Samplers S) (_ : S.Op → ℚ≥0) :\n" ++
    "    (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop := fun _ _ _ => True\n\n" ++
    "set_option linter.unusedVariables false in\n" ++
    s!"theorem sound_judged :\n  {anew} := by\n" ++
    "  intros\n  walk_step\n" ++
    "  exact ⟨0, fun _ => True, zero_le, trivial, fun _ _ kept => (kept trivial).elim⟩\n"

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
  let halved ← read (← replaceOnce (source "Product(a, b, c)") "charge sites.r <= 1 / F::Order"
    "charge sites.r <= 1 / (2 * F::Order)") ["a", "b", "c"]
  unless halved.package == written.package &&
      (halved.statements.claims.goals.map (·.caps)) == [⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 2 * order, 1⟩], []⟩]⟩] do
    throw (IO.userError "the halved charge changed the package, or is not half at the draw")

  -- The product computed another way: the vector is read before the matrix, and a term is
  -- added that cancels. The deployed function is another, and what the goal claims is the same.
  let rewritten ← read (source "Product(a, b, c)" (product := "v[k] * m[i][k] + (v[k] - v[k])"))
    ["a", "b", "c"]
  -- A sum where the product stands: another function, which is not the product of a matrix
  -- and a vector.
  let summed ← read (source "Product(a, b, c)" (product := "v[k] + m[i][k]")) ["a", "b", "c"]
  for (title, altered) in [("computed another way", rewritten), ("replaced by a sum", summed)] do
    if altered.package == written.package then
      throw (IO.userError s!"the product {title}: the package is what it was")
    unless (altered.statements.claims.goals.map fun goal => (goal.statement, goal.caps)) ==
        [(goal.statement, goal.caps)] do
      throw (IO.userError s!"the product {title}: the goal claims something else")

  let proof ← startLakeLean work "Freivalds" module.text
  let rewrittenProof ← startLakeLean work "FreivaldsRewritten"
    (← proofModule "FreivaldsRewritten" rewritten scalarFieldModelText template).text
  let summedProof ← startLakeLean work "ProductControl"
    (← proofModule "ProductControl" summed scalarFieldModelText template).text
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
  -- The same text on the product computed another way: every theorem is proved.
  let (ok, output) ← finishLean rewrittenProof
  acceptedOutput "FreivaldsRewritten" ok output theorems allowed
  -- The same text on a sum: the equation of one step of `apply` is not one of the field, and
  -- nothing that rests on the law of `apply` is proved. The law of the relation, which does
  -- not call `apply`, stands.
  expectUnproved "a sum for the product" "ProductControl" theorems summedProof ofApply
  expectPlaces "a sum for the product" summedProof ["unsolved goals"]
  expectReason "a sum for the product" summedProof
    "M ⟨i, early_i⟩ ⟨k, early_k⟩ * w ⟨k, early_k⟩ = "
  -- The claim is about `b * a`: its premise is not the one from which the text gets that the
  -- product of `a` and `b` differs. The laws of the two functions and the theorems about the
  -- verifier stand.
  expectUnproved "the operands exchanged" "OperandsControl" theorems exchangedProof ofClaim
  expectReason "the operands exchanged" exchangedProof "sound_far G input_a input_b input_c A B C ha hb hc rejected"
  -- The ceiling of half the charge is not one over the order: the comparison with what a
  -- uniform scalar pays for is not proved.
  expectUnproved "a charge of half" "BoundControl" theorems halvedProof ("large_covers" :: ofClaim)
  expectReason "a charge of half" halvedProof "drawCap soundCaps ="
  -- A field of one element or more is not a field of the source's order or more: the
  -- comparison of the ceiling is not available where the claim needs it.
  -- The witness of the text is of the hypothesis that was stated, so it is not a witness here.
  expectUnproved "a weaker hypothesis on the field" "FieldControl" theorems unassumedProof
    ["sound_judged", "sound_installed", "Witness.sound_at_corner", "sound_witnessed",
      "sound_sound", "sound_result", "sound_met"]
  expectReason "a weaker hypothesis on the field" unassumedProof "large_covers large"
  -- A name of the library defined again by the text: the claim that the text then proves is not
  -- the claim that was stated before it, and the goal is not concluded from it.
  expectUnproved "a name of the statement defined again" "ShadowControl" theorems shadowedProof
    ["sound_installed", "sound_sound", "sound_result"]
  expectReason "a name of the statement defined again" shadowedProof
    "Type mismatch\n  sound_judged\nhas type"
  expectPlaces "a name of the statement defined again" shadowedProof
    ["Type mismatch\n  sound_judged\nhas type"]
  -- The standard model has no sampler for a sequence of scalars: the kernel decides that it
  -- does not cover the package.
  let (ok, output) ← finishLean uncoveredProof
  if ok then throw (IO.userError "Lean accepted that the standard model covers the package")
  unless output.contains "StandardModel.covers stored = true" && output.contains "is false" do
    throw (IO.userError s!"the coverage control was refused for another reason\n{output}")
  IO.println (s!"Freivalds<2> is judged within the table of caps of its goal (the draw at 1/{order}), on the matrices on " ++
    "which the admitted relation returns false, over every field of at least that order; " ++
    "the same text is accepted on a source that computes the product another way; " ++
    "6 of 6 controls refused, each at its line.")

end FreivaldsCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    FreivaldsCharge.run "checks/FreivaldsCharge.lean.in" work
