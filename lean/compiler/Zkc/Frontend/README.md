# Source language frontend

Run `just test-frontend` from the repository root. It builds the frontend, its tools and its tests
as whole libraries with `--iofail`. The driver checks syntax, name resolution, instances, body
typing, package admission and formatting against the source examples and conformance tables.
The recipe also runs the source-contract and generated-view suites. The driver keeps each
original assertion and reports a known failure only when the suite, case and diagnostic match
one entry in its [table](../Tests/Frontend/Main.lean). An unlisted failure fails the driver.
An unused entry also fails it and is reported for removal.

From `lean/compiler`, use `lake exe zkc-syntax check <file>` or `lake exe zkc-syntax format <file>`
for the syntax alone. Use `lake exe zkc-check types --library ../../libraries <file>` to see the
status of each root's package. The other checker commands are `names`, `resolutions`, `instances`
and `bench`. A successful core admission carries the program returned by the core.

Run `just test-interactive` for the Sumcheck and GKR certificates and `just test-written-knowledge`
for the written group proofs. The previous execution commands and derived schemes are documented
at [revision `10ed903fc`](https://github.com/zkcompiler/zkc/tree/10ed903fc22d3f20b22ff2d1bbf607a740ef0718).
See the [compiler status](../../../../docs/status.md) for current limits.

## Checking selected module members

Selecting a member such as `M<1>::helper` requires the enclosing instance `M<1>` to satisfy
its module bounds, interface conditions, applicable member definitions and laws. The frontend
records the concrete arguments after inference. A module-valued member, an argument chosen
by default, and a reference to an interface or scheme inside another module can all require
a concrete implementation. The check follows the dependencies of successful computations,
including a condition that determines that a law is inapplicable.

A concrete associated type must satisfy its declared sorts, including at a realized
application of a parameterized type member. The head of a protocol member must
agree with the interface on its roles, static parameters and bounds, ports, results,
and conditions. When a parameter is still open, the checker compares the binders in the
two declarations by position. For example, a port of type `[bool; k + 0]` matches
`[bool; k]`, and `[bool; k + 1]` differs. An open equality outside the supported
arithmetic, such as `k * k` against `k ^ 2`, leaves the consuming root waiting.

Before choosing public defaults, the ordinary checker records the declarations used by
the selected roots and their required modules. An unused public declaration still receives
its eligible defaults under SP7. Each chosen member default checks its enclosing module.
Instance numbers are part of the emitted package. When a formerly scheduled default drops
out, the checker reserves the numbers its signature and body requests contribute before
the next public request. Suppressed defaults share private results, and their request order
contains only new private requests. Private layout work publishes only these numbers. A discarded
default contributes no root, diagnostic or law obligation.
`zkc-check instances --contents` reports the signature and default-instance phases. Use
`zkc-check types` for the verdict on member bodies and packages.

If a phase stops at the instantiation-depth limit, a session ending there reports the
incomplete check. A newly selected default can give a shorter path to the same module.
When the later phase completes that check, the full session reports the settled result.
An exhaustion reached while reserving numbers for a discarded default also stays private.
If a shallow public call now succeeds, it can request a definition that the incomplete run
never reached. That first request can move the numbers of later definitions, including in a
package returned by both runs. Use the definition numbers from the package being checked.

A written goal requires the modules used by its deployed protocol, its selected relation,
and the evaluation of its proof arguments, ceiling and charges. Two goals of the same scheme
can therefore receive different results. Admission by instance number checks all selections of
that root. Admission by scheme checks the selected scheme, even when another scheme closes
to the same protocol instance. A generated input record depends on the protocol
signature. Records derived from protocol events also depend on the checked body, including
when the record is already cached. Module validation elaborates additional bodies in a private
instance table. The frontend checks the types of applicable laws under SP10 and reports their
proof obligations. The formal library owns proofs that those laws hold.

## Proof arguments at a written goal

A scheme selects a deployed protocol instance. A named goal binds that instance's
specification-only naturals in declaration order. Each application retains its own resolved
proof arguments and lexical static environment beside the emitted instruction. Following
that instruction evaluates the arguments in the caller's environment and checks the
callee's specification conjuncts. Shared parameters are inherited by scope and parameter
index. The Core application continues to reference the same deployed callee.

From `lean/formal`, run `lake lean checks/ProofArguments.lean` for the two goals from the
language conformance program. For one admitted `Count<8>`, `spec e = 4` closes the draw
charge to `3/8` and `spec e = 1` closes it to `3/4`. The same lookup follows an application
instruction from a caller. Each key in the path must identify one application in the current
caller. The interface has no iteration coordinate for an argument that needs the index of a
uniform loop. These values describe the authored charge. Certifying a false-acceptance
probability also requires a theorem for the admitted verifier.

## Issuing written soundness goals

Run the command from `lean/compiler`. Give one `--goal` for each required goal and an optional new directory for the trusted Lean sources.

```sh
lake exe zkc-check written-goals --library ../../libraries --goal good --goal bad --output issued ../formal/fixtures/hash-relation.zkc
```

The command prints one result per selector in request order and exits with status 1 if any goal was refused. Short and qualified names that select the same declaration share one issuance. Each issued goal has a separate namespace and a pair of files, `Stated.lean` for the admitted package, its members and propositions, and `Challenge.lean` for the comparator. For this example the directory contains the pair for `mixed::good`, and the diagnostic identifies the hash reached by `mixed::bad`. The output directory must be new. Long canonical paths use nested module components. Each distinct goal publishes its two files together. If writing one pair fails, its selectors report the export error, later goals are still processed, and the command exits with status 1. Issuance fixes a target. Checking a submitted proof against it is a further step.

`Written.issueSoundnessGoals` exposes the same ordered results in memory. It resolves names in one assembly, keeps name-resolution failures owned by a goal with that goal, and shares the deployed admission between goals selecting the same scheme. Each goal then instantiates its own relation and emits the package reachable from that relation and the protocol. A parse error, an invalid shared namespace or a failure of shared source compilation is reported on each request. The issued result retains the actual package, root, relation member and proof arguments. The CLI reports the canonical source path and the keys within that package. If two declarations have the same canonical path, selection reports the ambiguity for every spelling. A contract hypothesis (`requires`) can be omitted under SX7 when it reads a port inaccessible to the honest verifier. Other requirements currently receive an SX7 diagnostic because the formal claim and its satisfiability witness do not yet represent them. `Written.allGoalsIssued` computes the aggregate result.

## What goals claim, as one package

`Written.goalClaims` reads what written soundness goals of one scheme claim. It gives the
scheme with its prover and its verifier, and for each goal the clause, the relation that the
clause applies as an instance at the static values of the application and the proof values of
the goal, the operands at the statement and at the witness of the relation (the witness is
absent where the clause is written short), the proof arguments and the ceiling. The records are
made by this function alone (their constructors are private), so that a statement cannot pair a
goal with a role, an operand or a proof argument that is not its own.

An operand is an input of the deployed header, by its place there. The source's ports and the
header's inputs are two lists, since a `spec` port is erased (SX2); the place is found in the
list from which the named protocol is emitted (`Typed.ProtocolBody.deployedPorts`), and the
emitted header is compared with it. A statement operand is an input that both the prover and
the verifier of the scheme hold: the scheme's statement (SC4), of which GL3 asks every
statement argument to be a function. An input that the verifier holds alone is refused under
GL3, at the operand; a `spec` port, which GL3 admits under a fixed statement as a value that no
role holds, is refused as not issued yet. The goals of a package are of one scheme: goals of two
scheme declarations are refused, also where the schemes have one protocol and one verifier.

The relations are instantiated one after another in one state that
starts as the state of the root, so each has a key of its own, and two goals with one value
claim one relation. The package (`Typing.emitRoots`) is what the root reaches, in the order and
with the stored definitions of the root's own package, followed by what each relation adds; a
function that the protocol and a relation both call is one definition.

From `lean/formal`, run `lake lean checks/GoalClaim.lean`. It compares the stored definitions
of the claims of `Count<8>` with those of the root's package, and runs Lean on a module with
both packages: the kernel accepts that the deployed definitions come first and that the
process of each role of the root is the same in both, for every model. A statement about a
goal can therefore name one admission and find the protocol and the relation by their keys,
and what it says of the protocol is said of the deployed one.

`lake lean checks/GoalStatement.lean` asserts what a change of the source does to a statement:
a `spec` port that nothing uses, in front of the operand or behind it, leaves the operand and
the text of the claim as they are, and another port of the same type as operand changes both;
the refusals above; the verifier of each of two schemes of one protocol. It then has Lean prove
a module in which a consumer that names no generated proposition uses the published theorem at
the inputs of the source, and refuse the same consumer where the clause names the other input.

An operand of a clause that is no port is not read yet. Where a relation links a primitive that
no deployed definition links, the claims' package is over a larger vocabulary than the root's,
and the two are not compared. Such a package can be admitted. Written soundness statements
require a model, so a package linking any project primitive gets a diagnostic at issuance.

## The statements of goals

`Written.Statements` (`Written/Statement.lean`) writes the module of the goals of a scheme
(`Statements.module`: its imports, the order of its parts and the names of the theorems whose
axioms it asks for are decided there, and a check gives the text of the proofs).
Around the proofs stands, with the claims' package: the facts (the key, header and place of the root and of
each goal's relation, the header and place of each function before the root that the text names, the verifier and the prover
of the claims' scheme, each goal's proof arguments and charge), that the standard interpretation covers each goal’s reach, the transfers of a statement from the installed program to
every admitted one, and for each goal four propositions that are defined before any proof: the
claim about the installed program, the goal for every admitted program, the result (the model
covers the package, and the goal), and that the hypotheses of the claim are met together. The
claim applies the experiment of the formal library (`ReturnsWithin`,
`lean/formal/ZkcFormal/ReturnExperiment.lean`) to the process of the deciding role on its
inputs, the samplers of the model and the bound; the generator does not write which services
the bound is against or which event it is of.
For a text that establishes its claims by the judgment with fees it also writes, before the
text, the judgment of each goal (`<goal>Judged`, with named binders), the theorem that the claim
follows from it and the theorem that the hypotheses of the claim are met at inputs on which the
relation returns false, and the key of each named draw of the root under the name of its site
(`site_<name>`), with its cap where the contract charges it; the text proves the judgment, and the claim is concluded after it.
After the text of the proofs it writes the theorems of the last three from the claim and a
witness, and the comparison of a goal's total with its ceiling. A statement uses the standard interpretation. It is
bounded by the total of the goal's table of caps (`<goal>Caps.total`), which `goalClaims` reads
with the claim (`goalCaps`): the uses that the root reaches at the goal's proof arguments, each
with the caps that the contract of its definition gives its charged draws and with its calls.
The module states that the counts of the table are the stored program's and what its budget is
(`Statements.counts`); a goal whose ceiling is below the total is refused (GL4). The deciding
role, the operands, the proof arguments, the ceiling and the table are read from the claims and
from nothing that a caller gives. A
statement names the inputs of the root as the source names its ports (`input_flag`), so that a
reader sees which inputs the relation is applied to and which the deciding role is run on. A goal
whose clause is a `reduces` gets no statement yet: the statement of a reduction is about a
return on which the reduced statement is true. Under SX7, a requirement that reads an input inaccessible to the deciding role is outside
the soundness experiment. An available requirement currently prevents issuance until the claim
and its satisfiability witness can represent the hypothesis. The checks of the four subjects
(`lean/formal/checks/CountCharge.lean`, `FreivaldsCharge.lean`, `GuessCharge.lean`,
`EitherCharge.lean`, on the library `lean/formal/ZkcFormalTests/WrittenSubject.lean`) are its users;
[the page for authors](../../../../docs/written-soundness.md) says how a subject is written.
`lean/formal/checks/GoalClaim.lean` has Lean elaborate the statement of a goal whose relation
has a witness.
[Source charge lookup](Written/Charge.lean) · [Goal selection](Written/Selection.lean)
