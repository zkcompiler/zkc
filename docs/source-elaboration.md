# Source language and frontend boundaries

The next shared interface should be a **typed contract for a closed source instance**. A
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
Keep the declaration, event and part as the source identity and record the enclosing
application and iteration for each Core realization. Replacing an entire stepped reduction
with a single global event key would make distinct openings or charges indistinguishable.
The verifier of this mapping should reject a missing realization and an ambiguous match.
[Source elaboration, §7.5](../language/LANGUAGE.md) · [Current address lookup](../lean/compiler/Zkc/Frontend/Emit/Root.lean)

## Frontend review

| Boundary inspected | Finding and consequence |
|---|---|
| Parser and printer | Parsing the 504 reference programs distinguishes grammar errors from later refusals. The corpus also exercises canonical printing, tree equality and comment retention. It cannot establish the static or security rules of a program that parses. |
| Scope and declarations | Whether a resolved declaration is a relation or an executable algorithm, its statement/witness split and the existence of a named loop can be checked before a goal is selected. Performing these checks in ordinary elaboration also catches malformed siblings of a selected clause. An unresolved module member needs an instance. |
| Closed instance | A relation and its extractor must agree on instantiated operand types, result tuple, role and run shape. Cost closure and simulator permissions have their own conditions. General checking of those requirements is incomplete. A successful name check gives a later phase work to do. |
| Written exporter | The current code reconstructs clause terms from byte offsets in a flat list, re-reads the syntax for paths, and accepts a restricted set of positional public ports. Whitespace changes move offsets, and synthesized terms can lack a unique location. The design should carry resolved clause fields directly. The present joins work for the two supported examples. |
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

Of the 170 positive programs, 167 had no error through body typing and three were refused.
Of the 333 negative programs, 189 produced a listed rule, four produced a different rule
and 140 produced no error at this prefix. One further reference case is marked skipped.
These counts use the diagnostic log, without treating a pending body as a finished one.

| Reference cases | Diagnosis and decision |
|---|---|
| `N-TY14e`, `I-4d`, `V-F2` | In the positive case P guards that its array has length eight, sends it to V as `m`, and indexes `m[7]` at P. TY14 requires this to succeed. The emitted send binds its result at both holders. The role analysis can certify equality of the sender's natural and Boolean readings across a give, but that law does not cover a sequence-length observation. The checker rejects the positive case with TY7. In the two negative cases it reports TY7 where the corpus expects the role-specific TY4. |
| `N-SC1a` | The scheme tried to close a specification-only natural. Static argument binding now identifies an ordinary named argument for that parameter as SP11. SC1 checks an explicit `spec` argument at the scheme. Omitting the argument leaves it for the goal. This belongs at instantiation, before computing a deployment identity. |
| `N-SC5a`, `V-C2` | An earlier group-operation typing diagnostic in a dependency masks the expected suite-key or goal diagnostic. Reproduce the point-by-nonzero-scalar operation in isolation and reconcile the vocabulary and its coercions before changing SC5 or GL4. |
| `N-E1`, `N-E2` | Both carried algebra examples fail to resolve multiplication on `Bound`. One expects an accepted program and the other additionally expects evaluation to falsify a law. Resolve home-module operator lookup first, then test the two law outcomes separately. |

For the role cases, preserve TY14. First distinguish the sender and receiver with a pair
of source tests. P may index after its own guard and send. V must establish the bound
before indexing. A third test should let V guard and ensure that P cannot use that guard.
Compare two implementations. One can emit the original payload when reading a send binding
at the sender, which requires a role-indexed binding across aliases, guards and shared
expressions. Another can extend the Core observation law at the sender to cover sequence
length and transport the corresponding domain fact. We favor the latter if its proof works
at the existing role projection and all three controls hold. It also serves direct Core
clients and avoids a second per-role environment in emission. Check whether the domain can
recover both the observed length and its bound before enabling the rule. This is the first
joint correctness experiment and can run alongside structured contract elaboration.
[Send emission](../lean/compiler/Zkc/Frontend/Emit/NamedProtocol.lean) · [Role observation rules](../lean/compiler/Zkc/Core/Facts/Contracts/Roles.lean) · [Soundness requirement](../lean/compiler/Zkc/Core/Facts/Domains/Rules.lean)

## Joint design

| Owner | Data and checks it should own | Example of a failure it should detect |
|---|---|---|
| Language | What authors can name, scope, relation positions, roles, event identity, stage defaults and the diagnostic contract | A `knowledge` branch supplies its own witness. |
| Frontend resolver | The declaration and binder identities for each clause field. Source spans travel alongside them for diagnostics. | A function in an imported module shadows an identically spelled relation. |
| Frontend instance elaborator | Close the selected declaration and type each actual expression in its owning scope. Derive the role views and compute the source-to-emission address map. Preserve distinct states for a language error, a dependency awaiting instantiation and a valid feature awaiting implementation. | A relation expects a point from one group but the selected scheme supplies a point from another. |
| Core admission and projection | Independently check types, available inputs, event order and party projections of emitted code, including packages supplied directly to Core. | A well-named source field points to an event hidden from the selected party. |
| Formal library and companion | Define the property over this admitted subject, derive structural verification conditions from operations, and discharge the remaining mathematical or model hypotheses. | The byte-for-byte right program returns the wrong witness, or the stated theorem assumes a different sampling law. |

A practical migration has two representations at different times. The resolver should return
a clause with an identity local to its owner, relation reference, ordered argument terms,
optional algorithm reference, source label and locations. Instance elaboration should attach
the closed types and the selected program instances, with an origin for each view field.
The exporter can then emit both the Core term and the bindings used in the proposition.
A Lean client should independently check those bindings against the admitted entry points.
Storing a second copy of the execution semantics in the frontend would make this last check
circular. Conversely, putting source lookup into Core would make admission depend on imports,
scopes and the state of a source file. The distinction follows the same rationale as Lean's
separation between elaboration and checking. [Lean elaboration and compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)

For property extension, the useful precedent in MLIR is an operation interface that lets a
generic pass request specific capabilities from each operation. Here the analogue is a typed
request from a property for a view, role execution or address correspondence, with a checked
answer wherever it contributes to a theorem. An interface method alone cannot establish a
security hypothesis. [MLIR interfaces](https://mlir.llvm.org/docs/Interfaces/)

## Delivery and evidence

1. Replace flat contract terms and byte-offset joins with structured clauses in the ordinary
   resolver. Migrate the existing written exporter as the first reader. Exercise imported
   aliases, reordered operands, two clauses with identical text under separate owners, and
   a malformed unselected clause. The generated target must still identify the same admitted
   verifier, relation and extractor.
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
