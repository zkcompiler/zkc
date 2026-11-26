# Writing a subject of a written soundness goal

A subject is a source with a soundness goal, the text of its proofs, and a check that runs Lean on the two. This page says what each of the three is, what is generated around a text, and what a text writes. The five charge checks under `lean/formal/checks/` read charges and goals from source. The direct proof in `GoalStatement.lean` supplies a text and a comparator challenge. [Status](status.md) says what the path supports and what it does not.

## The three parts

**The source** declares a protocol, the relation that its verifier decides, a contract with a `proves` clause and the charges of its draws, a scheme and a goal:

```
module t
use zkc::security::{soundness}
relation Holds(claim: bool): claim
protocol Either roles(P, V)(claim: bool @(P, V), first: index<8> @P, second: index<4> @P):
    if claim:
        a <- send first from P to V
        x <- draw index<8> from V to P
        guard @V x == a
    else:
        b <- send second from P to V
        guard @V b != 3
        y <- draw index<4> from V to P
        guard @V y == b
spec for Either:
    proves @V Holds(claim)
    charge sites.x <= 1 / 8
    charge sites.y <= 1 / 4
scheme Checked = Either:
    prover P
    construction interactive
goal either = soundness(Checked, stage = written)
```

The claim of the goal: on inputs at which no valid witness makes the relation return true, the verifier returns with probability at most the total of the charges that the root reaches along one run (here one quarter: the two draws are in the two arms of a choice, and the total takes the larger arm), against every service that draws each coin no more favourably than its law.

A fee proof supplies the judgment and a witness. A direct proof supplies the installed claim and a witness. The Operands example in `lean/formal/checks/GoalStatement.lean` uses the kernel to compute the deciding role and the relation.

A `Reading` asserts the ports of the root, the clause that each goal reads, the inputs of the deployed header that the relation is applied to, the number of proof arguments, the roles of the scheme. A reading that is not what the check asserts is an error: the text is written against it. A relation with witness parameters is not a subject yet. What else a check asserts of the reading is its own; the five checks assert the table of caps, and the check of Either also the names of its draws:

```lean
  let goal ← written.goal
  unless goal.total == 1 / 4 && (goal.caps.uses.map fun use => use.draws.map fun draw =>
      (draw.numerator, draw.denominator, draw.count)) == [[(1, 8, 1), (1, 4, 1)]] do
    throw (IO.userError "the table of caps is not the two draws at 1/8 and 1/4")
  unless goal.siteLabels.map (·.2.1) == ["x", "y"] do
    throw (IO.userError "the draws are not named `x` and `y`")
```

## What stands before the text

The source check imports the issued statements module and compares its stored program and
association with a fresh reading of the original source and goal selectors. Its package
must have those same fields and the installation used by the author's proof.

The generator (`lean/compiler/Zkc/Frontend/Written/Statement.lean`) writes the printed package and, from what the frontend read, the names that a text uses. For a goal `either` of a root with the ports above:

| Name | What it is |
| --- | --- |
| `subjectPackage` | the stored program, its association and the installation, together with proofs of elaboration and successful admission |
| `installed`, `rootMember`, `verifierRole`, `proverRole` | the program that the module installs from the package, the root in it, the two roles |
| `at_either` | transfers a property of the root and relation to the admitted program |
| `eitherMember` | the function of the relation at the goal's value, a member of `installed` |
| `calleeProgram`, `<function>Member` | the program of the definitions before the root, and in it each function that the root or a protocol that it applies calls; a law of such a function is stated there |
| `eitherCaps`, `either_budget` | the table of caps of the goal, and its budget as a number |
| `site_x`, `site_y` | each named draw of the root, under its name in the source, charged or not |
| `either_cap_x`, `either_cap_y` | the cap that the table gives each charged draw |
| `site_<a>_<d>`, `<goal>_cap_site_<a>_<d>` | a charged draw below applications and its cap, named by the numbers of the keys of the applications and of the draw in the stored program (the module's comment on the name says which) |
| `eitherJudged` | the judgment that the text proves |
| `either_witnessed_of` | the theorem that gives `eitherWitnessed` from an input at which no valid witness makes the relation return true |
| `eitherClaim`, `eitherGoal`, `eitherResult`, `eitherWitnessed` | the published propositions: the claim about the installed program, the goal for every admitted program, the result with the coverage, and that the hypotheses are met |
| `either_installed`, `either_sound`, `either_result`, `either_met` | their theorems, written after the text from `either_judged` and `either_witnessed` |

## Checking a publication

A check does not rest on Lean's acceptance of the proof module. A check writes its modules into a Lake project in its work folder (`ZkcFormalTests.SubjectProject`): the project requires the formal package, and its modules are files named by their module names. What the generator states before a text is a module of its own (`Module.statements`, named `<Name>.Stated`), which holds no text; the proof module (`Module.proof`) imports it; and the challenge of the pair (`Module.challenge`, `<Name>.Challenge`) states each published theorem over its proposition with no proof. A text is arbitrary Lean and can run a program while Lean reads it, so the project is settled in an order that leaves a text nothing to change. First the modules of the statements and the challenges are built, and the challenge of each judgment is exported by the toolchain's `leanexport`; then every other module is built, in one call of `lake build`; then a judgment exports its solutions and gives the two exports to `lake comparator`, which compares each judged theorem's statement with everything that it uses, replays the solution in the kernel and reads its axioms. Every process that reads a text, or the objects that a text's build left, runs confined (`bwrap`, which the host must have, with the profile of the comparator's own sandbox): the file system is read-only but for the project's `.lake`, the home and temporary folders and those of running services are covered, and there is no network of its own (a socket of the host whose path lies elsewhere can still be reached; `docs/status.md` says what that leaves). What a text can reach is then the objects of its build and the solution's export, which are what is judged; the exported challenge, the list of the pairs and the verdicts are beside `.lake`, where it cannot write (`checks/OutsideReading.lean` has the controls: a text that writes over each of them, and a text that replaces the objects of a pair). The checks register their modules before settling the project. Source comparisons and ceilings build with the statements. The comparator judges the accepted proof pairs and their consumers against the exported challenges. `OutsideReading.lean` submits the Honest pair and checks separately the fixtures that the comparator must refuse. `GoalClaim.lean` also checks modules assembled for tests of the generator by reading Lean's result.
