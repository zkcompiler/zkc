# Writing a subject of a written soundness goal

A subject is a source with a soundness goal, the text of its proofs, and a check that runs Lean on the two. This page says what each of the three is, what the issuer and the formal library give a text, and what a text writes. The five charge checks under `lean/formal/checks/` read charges and goals from source. `WrittenViews.lean`, `WrittenFees.lean` and `GoalStatement.lean` supply texts that the comparator judges. [Status](status.md) says what the path supports and what it does not.

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

The claim of the goal: on inputs at which no valid witness makes the relation return true, the verifier returns with probability at most the goal's bound, against every service that draws each coin no more favourably than its law. The bound is the ceiling that the goal writes after `<=`, and where it writes none, the total of the charges that the root reaches along one run (here one quarter: the two draws are in the two arms of a choice, and the total takes the larger arm).

A text proves the installed bound on its view, directly or from the fee judgment on its view, and the receipt on its view; it then states the two published theorems. The texts of `lean/formal/checks/WrittenFees.lean` do it by fees (a draw followed for free, and a fee paid within its cap); those of `WrittenViews.lean` and `GoalStatement.lean` directly, with the kernel computing the deciding role and the relation.

A `Reading` asserts the ports of the root, the clause that each goal reads, the inputs of the deployed header that the relation is applied to, the number of proof arguments, the roles of the scheme. A reading that is not what the check asserts is an error: the text is written against it. The checks' `Reading` does not read a relation with witness parameters yet; the issuer does, and `checks/WrittenViews.lean` and `checks/WrittenPublish.lean` judge texts over one. What else a check asserts of the reading is its own; the five checks assert the table of caps:

```lean
  let goal ← written.goal
  unless goal.total == some (1 / 4) && (goal.caps.map fun table => table.uses.map fun use => use.draws.map fun draw =>
      (draw.numerator, draw.denominator, draw.count)) == some [[(1, 8, 1), (1, 4, 1)]] do
    throw (IO.userError "the table of caps is not the two draws at 1/8 and 1/4")
```

## What stands before the text

The issuer (`lean/compiler/Zkc/Frontend/Written/Statement.lean`, `Statements.publication`) writes four modules for the goals of a scheme, in one name space:

| Module | Holds |
| --- | --- |
| `<Name>.Stated`, the data module | the printed package and the names below; the typed subject `written'subject` with a row for each goal (the path of its declaration, its property, its deciding clause, its bound, whether the source writes the bound as a ceiling, and its table of caps where it has one) and the source names of the root. It states no proposition about the protocol and imports no module of the formal library |
| `<Name>.Challenge` | `publish_goals <Name>.written'subject`: for a goal at the path `p`, the theorems `p.sound` and `p.met` without a proof. For a goal that writes no ceiling the command first decides by the kernel that the counts of the goal's table are those of the stored program and that the table adds up to the bound, and refuses the subject where it does not. The caps of the table, which draws it charges and whether the source writes the bound are the issuer's reading of the source, which the stored program does not hold; the checks' second reading of the source compares them. The decision and the fee facts read one arithmetic (`ZkcFormal.Written.Budget`) |
| `<Name>.Views` | `publish_views <Name>.written'subject`: the named views `p.sound.view`, `p.met.view`, `p.installed.view`, each with `view_iff`; the coverage fact `p.covered`; the step `p.sound_of_installed` |
| `<Name>.Fees` | `publish_fees <Name>.written'subject`: under `p.fees`, the count, the budget, the view `judged.view` of the fee judgment, and the step `installed_of_judged`; a goal whose table does not count as the stored program, a goal whose budget is above its bound and a goal without a table have none, each with a line that says why |

The names of the data module that a text uses. No declaration is named after a name of the source: a relation and a function are named by their keys, which the views show, and a goal by its row.

| Name | What it is |
| --- | --- |
| `subjectPackage` | the stored program, its association and the installation, together with proofs of elaboration and successful admission |
| `installed`, `rootMember`, `verifierRole`, `proverRole` | the program that the module installs from the package, the root in it, the two roles |
| `member'fn<k>` | the function of the relation with the key `k` at the goal's value, a member of `installed`; a view names it where it applies the relation |
| `calleeProgram`, `member'callee<k>` | where a function stands before the root: the program of the definitions before the root, and in it the function with the key `k` that the root or a protocol that it applies calls (its comment says the function's name in the source) |
| `written'caps<i>` | the table of caps of the goal of the row `i`, where it has one; a site's cap is read from it in the fee judgment's term |
| `written'subject`, `written'application<i>`, `written'bound<i>` | the typed subject, the short application of a deciding clause and the bound of a goal |
| `written'root`, `written'fn<k>`, `written'decision<d>`, `written'clauses`, `written'slot<i>`, `written'fields<i>`, `written'origins`, `found'root`, `found'fn<k>`, `rootKey`, `rootHeader`, `header<k>` | the parts of the typed subject and of the package that the library's commands and the checks read; a text does not write them |

A goal that writes its ceiling is issued also where its root reaches what a table of caps has no place for yet (a charge on an application or an attempt; a charge on a site of an applied protocol; a charged draw, or any application, under a loop whose count is read at run time or in an attempt; a root with an `attempt` is not emitted yet, so the cases of an attempt are not reached). Its row then holds no table, the publication reports the limit (`Publication.limits`, and the goal's result line of `zkc-check written-goals`), and its proof does not go through the fee facts. A goal that writes no ceiling takes its bound from its table and is refused there. This is a limit of the written stage; the language gives each of these charges a total. An error of the source in a charge refuses either: two charges on one site, a charge that is negative or above one, a site that names no one event, a site that is a send or a sample, a path that goes through what is no application.

Two more goals are refused at the goal's line. A goal whose bound is one or more (a ceiling of one or more, or charges that add up to one or more): a probability is at most one, so the claim would hold of every verifier. A goal on a verifier with a coin that the prover does not hear (a `sample` of the verifier, in the root or in a protocol that it applies): the published statement runs the verifier against one service that answers its coins and the prover's messages alike, which is soundness for public coins only.

The charges of a contract are the source's account of its bound. The published statement binds the bound, not the charge of a site: a text may reach `sound` by the fee facts of the issued table, by a table of its own, or with no fees at all.

A text is the issuer's opening (the imports of the four modules' data, views and fees, the name space and the opened names) followed by the author's proofs. It states each published theorem itself, `theorem t.either.sound : published% written'subject t.either sound`, and closes it with `t.either.sound_of_installed`; nothing is generated after it. A published theorem is named by its goal's path, so a goal `sound` publishes `sound.sound`: the opening turns off the linter that reports a repeated component of a name (`linter.dupNamespace`), for the whole text.

## Checking a publication

A check does not rest on Lean's acceptance of the proof module. A check writes its modules into a Lake project in its work folder (`ZkcFormalTests.SubjectProject`): the project requires the formal package, and its modules are files named by their module names. The data module (`<Name>.Stated`) holds no text; the proof module imports it; and the challenge (`<Name>.Challenge`) states each published theorem with no proof. The harness's record of such a pair is `ZkcFormalTests.WrittenSubject.Module`; it holds the views and the fees module that the proof module imports, which go into a project with the proof module. A text is arbitrary Lean and can run a program while Lean reads it, so the project is settled in an order that leaves a text nothing to change. First the modules of the statements and the challenges are built, and the challenge of each judgment is exported by the toolchain's `leanexport`; then every other module is built, in one call of `lake build`; then a judgment exports its solutions and gives the two exports to `lake comparator`, which compares each judged theorem's statement with everything that it uses, replays the solution in the kernel and reads its axioms. Every process that reads a text, or the objects that a text's build left, runs confined (`bwrap`, which the host must have, with the profile of the comparator's own sandbox): the file system is read-only but for the project's `.lake`, the home and temporary folders and those of running services are covered, and there is no network of its own (a socket of the host whose path lies elsewhere can still be reached; `docs/status.md` says what that leaves). What a text can reach is then the objects of its build and the solution's export, which are what is judged; the exported challenge, the list of the pairs and the verdicts are beside `.lake`, where it cannot write (`checks/OutsideReading.lean` has the controls: a text that writes over each of them, and a text that replaces the objects of a pair). The checks register their modules before settling the project. Source comparisons build with the data modules. The comparator judges the accepted proof pairs and their consumers against the exported challenges. `OutsideReading.lean` submits the Honest pair and checks separately the fixtures that the comparator must refuse. `GoalClaim.lean` also checks modules assembled for tests of the generator by reading Lean's result.
