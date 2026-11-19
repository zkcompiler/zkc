# Source language and frontend boundaries

The shared interface starts with a **resolved contract and goal** and ends with a **typed subject for a closed scheme instance**. A
property consumer should receive the exact operands, algorithm, audience, stage and events
selected by the author. Each selection that affects the theorem needs a check against the
admitted program. This extends the [security proof design](proof-architecture.md) and keeps
its separation of subject correspondence from the mathematical property.

## Language review

Three source constructs answer different questions. A protocol defines the interaction.
Its `spec` says what its named clauses mean. A `goal` selects a scheme, a property, a clause
and an experiment. For example, `knowledge SameLog(g, h, u, v) by extract` binds four
statement expressions, leaves the witness to the extractor and names source code that must
run. A written `special_soundness` goal asks about that extractor on two accepting runs.
A goal for knowledge soundness after construction needs a different experiment. The
distinction matters even if both goals select the same clause. Keep `special_soundness`
as a library name. The reference already assigns property lookup to GL1 and the relation
split to SX3 and SX6. [Source reference](../language/LANGUAGE.md) · [Library entries](../language/CORE-LIBRARY.md)

For new properties, design the library declaration and two uses before extending surface
syntax. The declaration should specify the required kinds of subjects and supported stages,
and the Lean library should interpret them. Keep common clauses as source forms with good
diagnostics. With this design, an author can select a new property over the existing views
using the existing goal syntax. Adding a genuinely new observation, such as persistent
service state visible to a particular party, still needs semantic design. An arbitrary Lean
expression in source would introduce a second naming and binding environment at the place
where the compiler most needs to track source identities. A separate Lean companion can
import the issued target and prove protocol-specific algebra there.

A source site denotes a place in the author's program. Its executions can have several
addresses. A charge or layout clause referring to one loop draw needs a policy for *all* its
realizations. The language already specifies sequential emission for stepped reductions.
A static loop needs one source site per command and a distinct address per execution. Use a
shared loop key and command key across compatible numbered blocks. The round belongs in the
block frame of the address. A call contributes its application frame. A consumer can then charge
all rounds of one draw, or open exactly the second one. Keep the origin map for diagnostics and
check that each selected address exists uniquely. A key with its frames erased cannot identify
an opening. A representation that merges fields across rounds also needs a type agreement check
after specialization.
[Source elaboration, §7.5](../language/LANGUAGE.md) · [Current address lookup](../lean/compiler/Zkc/Frontend/Emit/Root.lean)

## Frontend review

| Boundary inspected | Finding and consequence |
|---|---|
| Parser and printer | Parsing the 504 reference programs distinguishes grammar errors from later refusals. The corpus also exercises canonical printing, tree equality and comment retention. It cannot establish the static or security rules of a program that parses. |
| Scope and declarations | Whether a resolved declaration is a relation or an executable algorithm, its statement/witness split and the existence of a named loop can be checked before a goal is selected. Performing these checks in ordinary elaboration also catches malformed siblings of a selected clause. An unresolved module member needs an instance. |
| Closed instance | A relation and its extractor must agree on instantiated operand types, result tuple, role and run shape. Cost closure and simulator permissions have their own conditions. General checking of those requirements is incomplete. A successful name check gives a later phase work to do. |
| Written exporter | The resolver retains clause and goal structure, with declaration identities, binder numbers, branch boundaries and source locations. The property selects these fields directly. The ordinary FN6 binder supplies statement operands in parameter order, including named public ports. The written group consumer checks its narrower signature, view and theorem requirements at the chosen instance. |
| Views and emission | The schema derived from a closed protocol already carries typed fields and their port or event origins. The written exporter also checks the particular ports and events of a group fork. Reuse the schema when building the subject and retain an independent check that each selected observation is obtained from the admitted role execution. |

[Name resolution](../lean/compiler/Zkc/Frontend/Names/Declarations.lean) · [View derivation](../lean/compiler/Zkc/Frontend/Static/ProtocolView.lean) · [Current selection](../lean/compiler/Zkc/Frontend/Written/Selection.lean) · [Current fork binding](../lean/compiler/Zkc/Frontend/Written/Contract.lean)

The reference comparison also found a defect in the test input itself. The SC5 suite-field
mismatch referred to `zkc::suites::Poseidon2KoalaBear` without binding `zkc`. NL3 correctly
refused the name before suite compatibility could be checked. Importing the intended suite
makes the case reach the later checker. The SC5 verdict remains a later-phase requirement.
In the Schnorr split mutation, checking role eligibility before validating the relation head
produced SX6 in place of SX3. Checking the split first preserves the author's actual error.
[Reference cases](../language/conformance/README.md)

## What body typing still misses

We also ran assembly, resolution, instantiation and `Typing.typeProgram` with protocol
bodies enabled on the same reference corpus. This is a diagnostic inventory. A program
can have no diagnostic at this prefix while an instance is waiting or a scheme or goal
has yet to be checked. The independent corpus, default-instance pass, construction and
goal discharge are outside this measurement.

Of the 170 positive programs, 168 had no error through body typing and two were refused.
Of the 333 negative programs, 191 produced a listed rule, two produced a different rule
and 140 produced no error at this prefix. One further reference case is marked skipped.
Compared with the previous 504-row inventory, only the three role cases below changed. On the
separate 134-entry independent corpus all 69 positive cases had no error through this
prefix. Of 53 negative cases, 50 produced a listed rule, two produced another rule and one
produced no error. Three cases request parsing alone and nine have an underdetermined
expectation. The three corrected fact cases below also underwent Core admission, a stronger
test than counting frontend diagnostics.

| Reference cases | Diagnosis and decision |
|---|---|
| `N-TY14e`, `I-4d`, `V-F2` | P can now index the sent array after checking its length. The latter two programs produce TY4 at the shared binding, identifying V as the role with the bound and P as the role missing it. |
| `N-SC1a` | The scheme tried to close a specification-only natural. Static argument binding now identifies an ordinary named argument for that parameter as SP11. SC1 checks an explicit `spec` argument at the scheme. Omitting the argument leaves it for the goal. This belongs at instantiation, before computing a deployment identity. |
| `N-SC5a`, `V-C2` | An earlier group-operation typing diagnostic in a dependency masks the expected suite-key or goal diagnostic. Reproduce the point-by-nonzero-scalar operation in isolation and reconcile the vocabulary and its coercions before changing SC5 or GL4. |
| `N-E1`, `N-E2` | Both carried algebra examples fail to resolve multiplication on `Bound`. One expects an accepted program and the other additionally expects evaluation to falsify a law. Resolve home-module operator lookup first, then test the two law outcomes separately. |

A send keeps the wire type and all holders in the typed source and the emitted instruction.
Core analyzes each role's projection. For a sender, every successful `give` returns its
payload, and a holder-preserving `keep` exposes the same local value. A receiver's `get`
introduces a fresh value. The projection rule proves equality of the underlying held
subjects whenever it authorizes reuse. Sequence length is a function of that subject.

The measurement domain records the first length of each such subject. The numeric domain
uses this identifier both for explicit guards and for the implicit comparison between a loop
index and its upper endpoint. The sender can iterate up to the length of the sent array
and index its original array in that loop. This preserves a point such as
`length(xs) == 8`, a lower or upper bound, and a relation such as `k < length(xs)` even
when `k` is unknown. Numeric equality alone does not identify two arrays. Each role starts
with its own state, and facts learned in a single branch stay scoped to that branch.
The frontend checks the projected obligations and reports the failing source operation.
[Role projection laws](../lean/compiler/Zkc/Core/Facts/Contracts/RoleLaws.lean) · [Measurement domain](../lean/compiler/Zkc/Core/Facts/Domains/MeasurementLaws.lean)

## Joint design

| Owner | Data and checks it should own | Example of a failure it should detect |
|---|---|---|
| Language | What authors can name, scope, relation positions, roles, event identity, stage defaults and the diagnostic contract | A `knowledge` branch supplies its own witness. |
| Frontend resolver | The declaration and binder identities for each clause field. Source spans travel alongside them for diagnostics. | A function in an imported module shadows an identically spelled relation. |
| Frontend instance elaborator | Close the selected declaration and type each actual expression in its owning scope. Derive the role views and compute the source-to-emission address map. Preserve distinct states for a language error, a dependency awaiting instantiation and a valid feature awaiting implementation. | A relation expects a point from one group but the selected scheme supplies a point from another. |
| Core admission and projection | Independently check types, available inputs, event order and party projections of emitted code, including packages supplied directly to Core. | A well-named source field points to an event hidden from the selected party. |
| Formal library and companion | Define the property over this admitted subject, derive structural verification conditions from operations, and discharge the remaining mathematical or model hypotheses. | The byte-for-byte right program returns the wrong witness, or the stated theorem assumes a different sampling law. |

The parser and resolver share the constructors for clauses and goals. Their payloads change
with the phase. The parser keeps paths and role names for printing. The resolver keeps the
callee's declaration or an unresolved term, operand binders, deciding-role index, labels,
external names and simulator permissions. A tuple goal argument remains a tuple. A called
goal value retains its arguments and witness split. The source-map projection visits those
same fields. Two identical clauses in different modules can select different functions even
after that projection is erased. Static specialization remains explicit on each reference
segment until it is consumed or refused.

At a closed instance the existing group consumer checks the selected functions' signatures
and run view, emits three roots and binds their admissions in Lean. A generated equality
compares the **entire ordered returning record** of its admitted header with the expected
keys and nominal field types. An independent client supplies its own field keys, statement,
arguments and observations. A fourth recorded field would break the equality. Proving that
arbitrary views preserve observations of every execution is a separate obligation, especially
for nested loops, private choices and stopped prefixes.

For property extension, the useful precedent in MLIR is an operation interface that lets a
generic pass request specific capabilities from each operation. Here the analogue is a typed
request from a property for a view, role execution or address correspondence, with a checked
answer wherever it contributes to a theorem. An interface method alone cannot establish a
security hypothesis. [MLIR interfaces](https://mlir.llvm.org/docs/Interfaces/)

## What other languages change in this design

| Evidence | Decision for zkc |
|---|---|
| Rust lowers syntax within an owner. It can discard parentheses and assign identities to generated nodes while keeping origins for diagnostics. | Store a clause with its declaration, retain the local binder and ordered reference segments. A byte position can move and is shared by several generated nodes. Neither a byte nor a declaration number from another compilation is a portable certificate identifier. [Rust HIR](https://rustc-dev-guide.rust-lang.org/hir.html) · [AST lowering](https://rustc-dev-guide.rust-lang.org/hir/lowering.html) |
| Lean elaboration produces a term and separate information for editors. Kernel checking has its own input. | Resolve a goal in its source module. Issue the actual Lean proposition against admitted Core terms. Let a companion import it. Embedded Lean inside a clause would need a second scope, substitutions for protocol instances, and a policy for what Lean may observe. [Lean reference](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/) |
| Bend 2 has an implementation with checking and inference and a Lean development with explicit typing, evaluation and book assumptions. A Bend 3 evaluator port uses a single transition machine. A separate author report describes a conversion bug where comparing shared terms mutated a value. | Keep a fact, a role's access and a binder's identity distinct. Sharing a comparison result cannot change which operand an event denotes. The portable lesson from the evaluator is to compare alternative implementations on the same programs. Its packing and allocation decisions do not justify a new zkc runtime. The public port is evidence about an evaluator, with no dependency on a stable Bend 3 language specification. [Bend 2 implementation](https://github.com/bendlang/bend/blob/0e2f38f759cc830849e489307f3d256a7d148288/bend2/bend.ts) · [Typing and evaluation](https://github.com/bendlang/bend/blob/0e2f38f759cc830849e489307f3d256a7d148288/bend2/bendtt.lean) · [Bend 3 port](https://github.com/bendlang/bend/commit/487aec6fe5b35d2dc2c4a286385b62fd31a01f4a) · [Conversion correction](https://github.com/bendlang/bend/commit/88a7dfdae961888e90e3f8b8340815485260fb89) |
| Zippel's Chaum–Pedersen names public and witness inputs, two commitments, a challenge, a response and two verifier equations. Its knowledge analysis can fail to discover an extractor. | The concurrent projects share a research question about deriving assurance from an authored protocol. In zkc the author can name executable extraction code and the theorem checks it against the admitted verifier and relation. An algebraic analyzer could propose that code or prove residual equations. Its result would face the same independent binding checks. [Zippel example](https://github.com/eniac/zippel/blob/c968be19ad0bf08db70be0a9e844337473e55f49/examples/cp/cp.zippel) · [Zippel paper](https://www.cis.upenn.edu/~sga001/papers/zippel-sp27.pdf) |
| Owl puts information flow and refinement in the protocol language. Choreographic programming relates a global interaction to local endpoints through a projection theorem. | Express roles, observations and wire events in source and preserve their scope in the typed body. Require a correspondence to the admitted party projection. A successful global execution by itself cannot establish what a corrupt peer may see. [Owl Book](https://gancher.dev/owl-docs) · [Formal theory of choreographic programming](https://doi.org/10.1007/s10817-023-09665-3) |

## Decisions from the independent review

**Properties.** The shared Lean vocabulary owns the name, audience, clause requirement,
stages, constructions and available theorem binding. The references are checked against it.
GL3 relates the contract's deciding role to the scheme verifier. The honest-verifier experiment
makes every participating role honest. The descriptions of available hypotheses live in SX7.
A richer game needs its own quantified experiment, supported models, permissions and closed
algorithm signature. A catalog entry for unforgeability or the name of an external algorithm
does not supply the scheme, adversary, model or proof. Keep the formal package independent of
source lookup and keep Mathlib and VCVio outside the compiler dependency graph.
An external name can already have a checked source association. The Sumcheck extension and
GKR summand checks inspect the selected external name and its operands. Supplying the
semantics of the named algorithm for a particular game is a further obligation.
[Shared declarations](../lean/compiler/Zkc/Vocabulary/Security.lean) · [Formal fork](../lean/formal/Zkc/Formal/Written/Extraction.lean)

**Facts.** Section 7.1 already assigns fact acceptance to Core admission, and TY4 describes
a mutable name as its current value. Three independent expectations contradicted admission.
The guarded mutable natural, the post-loop guarded sequence and the commuted natural index
all produced admitted functions. Assigning eight before the first return, assigning an empty
sequence after the length guard, and changing the index to `2 + i` each produced a refusal.
Treat the specified rules as guarantees. A stronger certified bound is usable at the same
role and control point. The sender-local length guarantee is checked through projection and source admission.
[Fact rules](../language/LANGUAGE.md) · [Independent corpus](../language/conformance/independent/expectations.json)

**Views and services.** Comparing six source roots with Core gives three straight-line
agreements in field count, order and the shape of the types (Schnorr, Chaum–Pedersen and
the OR proof). Sumcheck, inner product and GKR expose a different boundary. Core has nested
records while frontend view derivation waits on applications or control flow. For a shared
loop, group by the same source site and index its occurrences through frames. Check nominal
types at every round before transposing records into a collection per field. Empty loops,
heterogeneous specializations and two calls to the same callee need distinct controls.
`Run`, `Received` and `Coins` describe a returning run. A failed attempt may already have
sent a commitment. A game exposing it must name a prefix including the stop and preceding
observations. The language's OR4, OR5, OR7, OR9, OR10 and §7.6 are marked superseded. Redesign
those rules with a service request, fixed handle identity and an explicit opening flow. Require
a test with two tables and a failed opening before extending the declaration of support.
[Core shapes](../lean/compiler/Zkc/Core/Program/Shape.lean) · [Source oracle boundary](../lean/compiler/Zkc/Frontend/Elab/Events.lean)

**Schemes.** Name resolution of a scheme or a successful construction-line check does not run
a deployment. Rebuild stage execution around the admitted header, Core's selection of online
roles and its statement and witness, reusing the authored suite, layout and key information.
The written group certificates check the declared endpoints through Core's online-role
selection and expose equalities for statement and witness types. The first deployment
test should run one transcript handler and check its challenge at its real address. Theorems
about Fiat–Shamir require a stated adversary, query budget and reduction. The legacy scheme
modules and descriptive examples are inputs to that redesign. Role selection still needs source elaboration for offline and ideal roles in larger schemes. [Scheme role definitions](../lean/compiler/Zkc/Core/Scheme/Roles.lean)

## Delivery and evidence

The contract representation and sender-local length checks are in production. Next exercise
the closed contract interface on a repeated draw, followed by a fixed-table opening. A deployed transcript handler and its
Fiat–Shamir security reduction each need their own acceptance evidence.

1. The resolved contract and goal now feed the written consumer. SX5 checks ownership and
   uniqueness during ordinary resolution. The compiler and both references share a checked
   property catalog. A stage may be legal in the language while its property still awaits a
   formal source binding. Test new entries with a supported and an unsupported selection.
2. Elaborate these clauses at the closed scheme instance. Move general signature, cost and
   visibility checks to their owners. Let the property library specify the supported subject
   shape and keep profile-specific restrictions visible at selection. Check an executable
   extractor and an external clause separately. Exchange the order of two same-typed ports
   and require the independent target consumer to detect the changed claim.
3. Exercise a second kind of subject before stabilizing the interface. Use a Sumcheck or GKR
   repeated draw with one named site and several realizations. Preserve order, prefix and per-round
   substitutions. Measure emitted bytes, verification conditions, checking time and memory
   across increasing round counts before choosing a shared-body representation. A group fork
   and a charged repeated draw have different proof obligations.
4. Implement the written oracle at the first missing execution boundary. The current lowered
   event retains the reader, opener, deferred flag and explicit opens. Event elaboration waits
   at the oracle. Use the actual spot-check source to test a table fixed at send, two
   distinguishable handles, a permitted opening and a false claim. Only a semantics with
   a fixed table can support this test. Defer claims about Fiat–Shamir, random-oracle
   programming and zero knowledge until their stage, service, visibility and experiment
   are available. [Current oracle lowering](../lean/compiler/Zkc/Frontend/Names/Terms.lean) · [Current elaboration boundary](../lean/compiler/Zkc/Frontend/Elab/Events.lean)

The active gate is `just test-frontend`. It checks both reference syntax and whether each
early diagnostic agrees with the specified rule. Negative programs that still pass this
prefix are counted separately. `just test-written-knowledge` checks source mutation controls
and consumes the two issued group certificates. `just test-interactive` exercises the source
reductions and oracle-name controls. Each command answers a different question about the same
pipeline. [Validation guide](development.md)
