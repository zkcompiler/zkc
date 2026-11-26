# Writing a subject of a written soundness goal

A subject is a source with a soundness goal, the text of its proofs, and a check that runs Lean on the two. This page says what each of the three is, what is generated around a text, and what a text writes. The charge checks retain the sources, tables and independent lemmas for Guess, Count, Freivalds, Either and Twice. Count checks two attained probabilities. The direct proofs in `GoalStatement.lean` and `WrittenBoundGuard.lean` exercise the publication path. [Status](status.md) says what the path supports and what it does not.

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

The claim of the goal: on inputs on which the relation returns false, the verifier returns with probability at most the total of the charges that the root reaches along one run (here one quarter: the two draws are in the two arms of a choice, and the total takes the larger arm), against every service that draws each coin no more favourably than its law.

**The text** is a Lean file without a header, between `noncomputable section` and `end`. It proves, for each goal, the judgment that the generator states (`<goal>_judged : <goal>Judged`) and that the hypotheses of the claim are met at some input (`<goal>_witnessed : <goal>Witnessed`). The propositions that a module publishes are all generated before the text, and the text states none of them. What it states is its own: what the relation computes, and any law or lemma that its proofs use. The first is needed by every text, since the judgment assumes that the relation returns false and the text has to say what that means of the inputs:

```lean
theorem either_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]
    [DecidableEq G] (claim : Bool) :
    functionResult (t := .bool)
      (fnMeaning (StandardModel.model D) installed eitherMember (.cons claim .nil)) =
        some claim := by
  kernel_rfl
```

**The check** is a Lean file that reads the source with the frontend, asserts what it read, and runs Lean on the generated module. With the library of `lean/formal/ZkcFormalTests/WrittenSubject.lean` it is data:

```lean
def reading : Reading where
  goals := ["either"]
  ports := #["claim", "first", "second"]
  clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩
  operands := #[0]

```

The check reads the source, verifies the expected goal and checks the retained lemmas against its issued statements.

A subject is accepted when Lean accepts the proof module; the judgment accepts it, where its published theorems have the statements of the challenge and pass the kernel (below, "A check does not rest on Lean's acceptance"); every theorem of the statements, and every published theorem, rests on `propext`, `Classical.choice` and `Quot.sound` at most; Lean accepts the module in which the package is compared with what the frontend gives to admission (`<Name>Source`); and every control is refused as it says.

A `Reading` asserts the ports of the root, the clause that each goal reads, the inputs of the deployed header that the relation is applied to, the number of proof arguments, the roles of the scheme. A reading that is not what the check asserts is an error: the text is written against it. A relation with witness parameters is not a subject yet. What else a check asserts of the reading is its own; the five checks assert the table of caps and the names of the draws:

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
| `at_root`, `at_either` | move an author's property of the installed root, or of the root and relation together, to the members found by their keys in any admission of this package |
| `eitherMember` | the function of the relation at the goal's value, a member of `installed` |
| `calleeProgram`, `<function>Member` | the program of the definitions before the root, and in it each function that the root or a protocol that it applies calls; a law of such a function is stated there |
| `eitherCaps`, `either_budget` | the table of caps of the goal, and its budget as a number |
| `site_x`, `site_y` | each named draw of the root, under its name in the source, charged or not |
| `either_cap_x`, `either_cap_y` | the cap that the table gives each charged draw |
| `site_<a>_<d>`, `<goal>_cap_site_<a>_<d>` | a charged draw below applications and its cap, named by the numbers of the keys of the applications and of the draw in the stored program (the module's comment on the name says which); a refusal at such a draw has this name |
| `eitherJudged` | the judgment that the text proves |
| `either_witnessed_of` | the theorem that gives `eitherWitnessed` from an input on which the relation returns false |
| `eitherClaim`, `eitherGoal`, `eitherResult`, `eitherWitnessed` | the published propositions: the claim about the installed program, the goal for every admitted program, the result with the coverage, and that the hypotheses are met |
| `either_installed`, `either_sound`, `either_result`, `either_met` | their theorems, written after the text from `either_judged` and `either_witnessed` |

Each claim uses the standard interpretation. `F` is the BLS12-381 scalar field, `G` is its additive group, and `D`, `model` and `samplers` name its algebra, meaning and laws. The library proves `large` and supplies a service with `served`. Generic readback equations still allow a proof to establish a family lemma and specialize it at the source field. The kernel checks coverage from the root and relation of each issued goal. A diagnostic identifies an uncovered sort, row or law. Linked project primitives require a model before issuance.

To see a generated module, keep the working directory of a check: replace `IO.FS.withTempDir fun work =>` by a function that passes a directory of yours, and read `project/<Name>.lean` there, with Lake's logs (`stated.log`, `build.log`) and what each judgment said (`<label>.judgment.log`). The directory is empty at the start: a project is not used twice.

## The witness

**The witness** gives an input on which the relation returns false, at the standard interpretation:

```lean
theorem either_witnessed : eitherWitnessed :=
  either_witnessed_of false trivial (either_relation StandardInterpretation.D false)
```

## Controls

A control is the subject with its source or its text altered, in a module that must be refused: by Lean in the proof module, which is the default, by Lean in the module of the statements, or by the judgment where Lean accepts it (`refusal`). It names the theorems that are then left unproved and the texts of the places at which the module is refused; with `only`, it is refused at those places and at no other. The name space of a control's declarations is the subject's; its `name` is the name of its file.

A check does not rest on Lean's acceptance of the proof module. A check writes its modules into a Lake project in its work folder (`ZkcFormalTests.SubjectProject`): the project requires the formal package, and its modules are files named by their module names. What the generator states before a text is a module of its own (`Module.statements`, named `<Name>.Stated`), which holds no text; the proof module (`Module.proof`) imports it; and the challenge of the pair (`Module.challenge`, `<Name>.Challenge`) states each published theorem over its proposition with no proof. A text is arbitrary Lean and can run a program while Lean reads it, so the project is settled in an order that leaves a text nothing to change. First the modules of the statements and the challenges are built, and the challenge of each judgment is exported by the toolchain's `leanexport`; then every other module is built, in one call of `lake build`; then a judgment exports its solutions and gives the two exports to `lake comparator`, which compares each judged theorem's statement with everything that it uses, replays the solution in the kernel and reads its axioms. Every process that reads a text, or the objects that a text's build left, runs confined (`bwrap`, which the host must have, with the profile of the comparator's own sandbox): the file system is read-only but for the project's `.lake`, the home and temporary folders and those of running services are covered, and there is no network of its own (a socket of the host whose path lies elsewhere can still be reached; `docs/status.md` says what that leaves). What a text can reach is then the objects of its build and the solution's export, which are what is judged; the exported challenge, the list of the pairs and the verdicts are beside `.lake`, where it cannot write (`checks/OutsideReading.lean` has the controls: a text that writes over each of them, and a text that replaces the objects of a pair). A module is added before it is asked about (`start`, `startModule`, `startLakeLean` add; `finish` and `finishLean` ask), the first asking settles the project, and a module added after it is an error. What Lean said of a module that is built with the texts is read from Lake's log, into which a text of the same build can write: it serves a message and a control that Lean must refuse, and a proof module is accepted on its judgment only. The one exception is a module that a check assembles for a test of the generator itself (several pairs as one source, `asOne`; the modules of `GoalClaim`): it is accepted on what Lean says of it, in checks whose texts are the check's own. A module of a check that holds no text and must be accepted (the comparison of the package with the frontend, a ceiling) is built in the first step, with the statements (`startLakeLean` with `text := false`). The proof modules that a check accepts are judged in one run for the check, or, under a recipe, in one run for all its checks (`checks/Judgment.lean`), over the published theorems and the consumers that the check wrote, whose statements stand in the challenge. A text that turns the kernel's check off is accepted by Lean and refused there; so is a text that makes the theorems after it take a hypothesis. A control says where it is refused (`Control.refusal`): by Lean in the proof module (the default), by Lean in the module of the statements (what is generated does not hold of the altered source, and the text is not read), or by the judgment (`refusedOutside` states such a control apart from a subject; the check of `Either` has one; each is a run of the comparator of its own, and names what the comparator says of it, since a failure to judge is an error and no refusal). A control that alters only the text imports the subject's own statements; another has a module of statements of its own, `<Control>.Stated`. An error of a text is reported by the lines of the text (`text:<line>:<column>`). A module of one source (a comparison, a module with nothing published) goes through `startLakeLean`.

A control of a charge is a source: no caller gives a statement its table. A text is altered with `replaceOnce`, which fails when the place that it alters is gone. Where two proofs of one module meet the same refusal, `occurrences` says how often its text occurs, since a text twice among the places says only that it occurs. A control is worth what it would catch: run the check once with the control given the unaltered subject, and see that the check fails ("Lean accepted a control that must be refused").

This generator issues written soundness goals for decisions. The written knowledge generator issues knowledge claims. This generator has no reduction statement.
