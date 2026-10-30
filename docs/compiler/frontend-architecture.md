# Frontend architecture

The source frontend separates authored facts, partial editing facts, checked
native programs and admitted proof evidence. These are different API products;
none is reconstructed by pretending an earlier failed phase succeeded.

## Phase ownership

| Layer | Product and owner | Failure behavior |
| --- | --- | --- |
| Source | Immutable byte revision, name profile, cancellation and budgets | Invalid UTF-8 or resource exhaustion refuses capture. |
| Syntax | Lossless tokens/CST, layout recovery, notation descriptors | A partial tree remains navigable; formatting requires complete syntax. |
| Authored model | Fallible typed projection into native source records and the neutral formal arena | Unsupported ghost/custody/effect forms refuse projection rather than changing meaning. |
| Resolution | Modules, imports, declaration identities and installed operation/service selection | Failed declarations do not acquire checked signatures or bodies. |
| Analysis | Immutable authoring view with validity per declaration | Independent valid facts remain available after recoverable errors. |
| Native checking | Types, placement, effects, resources, local inference and closed instances | Only an error-free project constructs `CheckedProject`. |
| Translation | Existing typed language-to-Protocol lowering and actual-original comparison | Exported associations are proposals to an independent reader. |
| Formal checking | Existing Lean declarations, subjects, requests, companions and receipt audit | Pending obligations remain open; missing consumer requirements cannot disappear. |

Frontend owns the checked program and its source associations. IR owns lowering
that program into IR, the shared operation catalog and generated registries.
Frontend resolution consumes the catalog's installed signatures and spellings;
it does not maintain a competing operation registry. Lean owns its independent
interpretation, companion resolver and receipt audit, including all code under
`lean/`. These ownership boundaries apply when extending the language as well
as when changing a shared contract.

`LayoutReader` provides explicit fallible extraction; declarations, expressions
and bodies have separate implementation units. It does not communicate failure
through a shared optional diagnostic while returning invented nodes. The
`FormalSource` arena has a reference type separate from CST node indices and a
closed variant of named fields. Only its serializer owns wire spellings. Adding
a grammar form requires an explicit authored projection and refusal tests;
adding a wire form also requires the owning consumer and schema change.

`AuthoringStorage` retains analysis facts independently of executable checking.
A body error permits queries on independently checked declarations. A malformed
body retains the recovered syntax and unrelated semantic facts. A failed
signature currently prevents global body checking: the editor may show valid
neighboring signatures, but does not claim their bodies are checked. Header
recovery is still syntactic rather than independent semantic admission.

The source server's bounded `RequestQueue` owns admission, cancellation,
generation invalidation, completion and publication predicates. A cancelled
running request can release its client ID; its late completion cannot erase a
new request reusing that ID. Tests drive these transitions directly, without
sleeping or introducing test commands into the LSP protocol.

Oracle source projection has its own implementation unit. The semantic oracle
checker classifies each supported expression as a view or an ordered action;
the general expression checker uses that same classification for dispatch and
`<-` enforcement. The parser spelling table is shared by both source profiles.
Shape attributes stay in authored records and resolve into port bounds during
signature checking. They do not become invented inline source annotations.
The [oracle profile](../spec/language/oracles.md) records operation coverage and
the remaining virtual-definition and logical-record integration boundaries.
Protocol oracle calls and returns already decompose/rejoin their components
through the existing checked ABI; no separate source keyword is needed.

## Catalog selection and four faces

The shared catalog is an installation contract, not a parser keyword table.
A family identifies a frontend declaration, logical IR signature, execution
adapter and Lean interpretation. Each face declares its supported parameters;
availability is their required intersection, not the union of familiar names.
The catalog may name laws but cannot prove a kernel implementation correct.

The first service change uses `Contracts/Services.h`, the existing owner of
logical service contracts. Its `SourceService` rows name installed declarations
and a typed family adapter. Header parsing retains ordinary typed ports. After
module/import resolution, the checker partitions service ports by the resolved
catalog declaration. `Random`, `zkc::prelude::Random`, and an imported module
alias can select the same installed constructor. An authored type or static
binder named `Random` keeps its own meaning. The selected family and parameter
count are checked by signature formation and included in installation identity.

The initial installed declaration is the prelude interface `Random<F: Field>`.
It is a name-resolution anchor, not an ordinary data type, a provider root, or a
proof of random sampling. Its `draw` and `index` signatures still come from the
existing logical service catalog, and provider/root admission remains separate.
New service families require an explicit typed adapter until a probe establishes
that a more general signature algebra covers them. No catch-all string dispatch
is added to the parser.

Notation has two independent concerns. `Syntax/Operators.def` owns built-in
shape, precedence and associativity. Installed/library callable declarations
supply meaning through normal operator binding and capability checking. Parsing
`^` does not install exponentiation, but an explicit valid operator binding for
it is now accepted consistently by both parsers. The catalog's frontend face
must refer to the callable declaration, not merely the glyph.

The [FRI query-domain probe and decision](query-domain-maps.md) follow the IR
owner's candidate. The probe exercises actual source resolution and IR contracts,
80 native Host cases and six Lean equations reusing existing index laws. It
selects a shape-bound map family for the next joint unit while preserving the
checked general arithmetic and native-kernel trust boundary. A successful
metadata join is not a simulation theorem. Oracle family additions likewise use
the IR owner's descriptors.

This follows the useful part of MLIR's
[operation definitions](https://mlir.llvm.org/docs/DefiningDialects/Operations/):
central declarative facts can generate repetitive accessors and validation.
MLIR [interfaces](https://mlir.llvm.org/docs/Interfaces/) motivate explicit
capabilities for consumers of different operation families. Neither mechanism
requires putting the source parser or Lean proof terms inside MLIR. Reuse the
existing zkc TableGen/catalog machinery; adding a second schema engine would
increase the number of contracts that must agree.

## Checked program to IR

Both source profiles enter the same checked-program API. `zkc` is the installed
library profile; `zkc-layout` is the development layout profile. A capture selects
one profile for its supplied modules, with an explicit exception for the installed
prelude. A layout client cannot silently reinterpret an old-profile dependency.
The [layout execution contract](../spec/language/layout-execution.md) records
the supported projection; accepting a CST does not establish executable support.

The integration points below identify responsibilities that must survive changes
to the IR representation. The [translation contract](../spec/language/translation.md)
owns their semantics; these paths locate the current implementation.

| Boundary | Current implementation | Required property |
| --- | --- | --- |
| Capture and checking | [Language API](../../compiler/include/zkc/Language/Project.h), `capture`, `analyze`, `Analysis::checkedProject` | Partial authoring results cannot construct a checked program. Preserve capture, installation and source-format identities. |
| Selection and closure | Same API, `resolveEntry`, `closeEntry`, `closeSubject` | Resolve an exact specialization before emission. Keep static arguments, scoped captures, domain instances and the selected invocation policy. An executable Entry is not automatically a proof subject. |
| Scoped validation | [ScopedWitness](../../compiler/lib/Language/ScopedWitness.cpp), [ScopedSpecialization](../../compiler/lib/Language/ScopedSpecialization.cpp) | Reconstruct source capture and specialization associations; do not trust stored candidates as evidence. |
| Direct emission | [Translation API](../../compiler/include/zkc/Translation/Language.h), [Emission](../../compiler/lib/Translation/Language/Emission.cpp), [FiniteEmission](../../compiler/lib/Translation/Language/FiniteEmission.cpp) | Consume `ClosedEntry` and preserve types, roles, custody, ordered effects, sites and auxiliary callback/domain definitions. |
| Actual-original admission | [Compiler API](../../compiler/include/zkc/Compiler/Language.h), [Language admission](../../compiler/lib/Compiler/Language.cpp), [Comparison](../../compiler/lib/Translation/Language/Comparison.cpp), [FiniteComparison](../../compiler/lib/Translation/Language/FiniteComparison.cpp) | Parse and verify the actual candidate, compare its SSA and interface to the checked program, then retain its exact bytes. Comparing two outputs of the emitter cannot replace this check. |
| Formal publication | [SourceCorrespondence](../../compiler/lib/Compiler/SourceCorrespondence.cpp), [written-source schema](../spec/language/source-ast.md) | Bind authored nodes, binding proposals and closed instances to the same admitted snapshot. Neither a matching name nor a source span establishes that association. |

`prepareOriginal` emits a direct original and admits it through
`compareOriginal`. `admitOriginal` checks supplied original/interface bytes and
also enforces canonical encoding. The correspondence comparison does not simplify,
re-emit or mutate the candidate. Later executable lowering cannot redefine the
source meaning selected at this boundary. Moving these checks into a new IR
representation requires preserving their independent inputs and refusal behavior.

Occurrence identities have separate scopes: a written node, closed instance,
protocol site and structured row are not interchangeable integers. Preserve the
explicit associations in the [contract register](../spec/contracts.md#occurrence-identity),
including role substitution and instantiated call/loop paths. A source migration
changes its capture identity even when emitted IR bytes happen to match; regenerate
source-bound proof products against the new capture.

The relevant regression boundaries are:

| Checks | What an IR change must preserve |
| --- | --- |
| `language-layout`, `language-layout-oracles`, `language-role-assembly` | Development syntax reaches actual IR with oracle action/view distinctions and distinct role components. |
| `source-correspondence`, `source-correspondence-cli`, `language-interface`, `language-written-source` | Candidate mutation, exact interface agreement and authored-source associations are checked independently. |
| `source-scoped-execution`, `source-finite-execution`, `language-scoped-ir`, `language-finite-occurrence`, `language-reduction-ir` | Closed callbacks, domain witnesses, auxiliary definitions and finite/reduction occurrence mappings survive translation. |
| [Layout Host tests](../../common/tests/protocol/test_language_layout.py) | Spec-free Schnorr executes; additional unused draws consume capacity, extra messages remain observable, reached guards refuse, and unavailable formal requests remain open. |
| `source-syntax`, `language-authoring`, `source-requests`, `source-lsp` | Editing and cancellation remain usable without promoting partial analysis into execution or proof evidence. `source-lsp` requires its optional build target. |

Use the [test guide](../../common/tests/README.md#selecting-checks) for build and
suite selection. Parser fixtures such as FRI, Sumcheck and KZG illustrate the
intended source surface; they are not end-to-end acceptance receipts. Library
binding syntax, domains, finite iteration and scoped callbacks must consume the
IR-owned catalog before those examples can establish full layout-library support.
The [runtime project compiler](../../crates/zkc/src/project/compiler.rs) still
selects `zkc`; its source-format switch belongs to the coordinated production
cutover, after dependency closures and their consumers migrate together.

## Formal and executable connection

The [checked-elaboration contract](../spec/language/elaboration.md) fixes what
Lean's future independent source checker must reconstruct, including complete
coverage in both directions. The neutral written model, binding observations,
closed instances and exact structured admission are its input. The checker must
reject additional observable operations as well as omitted ones unless an
explicit semantic rule justifies the transformation.

Claims may instead start from the exact original IR with frontend elaboration
named as a trusted translation, as specified by the
[assurance boundary](../assurance.md#ir-relative-security-claims). The independent
source checker strengthens that boundary without blocking IR-relative security
claims. Native checking and actual-IR comparison remain in the execution path;
security-transforming constructions and realizations retain their Lean checks.

Every authored postcondition and security request enters the required inventory.
[Companion keys](../spec/language/companions.md) support lookup of a proof against
an already fixed proposition. Consumer requirements independently fix the desired
request set; coverage is compared after fresh Lean receipt audits without
demoting valid receipt rows. These mechanisms solve separate problems: a stable
key cannot establish meaning, and an inventory cannot infer a postcondition the
author never wrote.

Reuse `zkc.declarations/0`, subjects, bound requests, record checks and the receipt
audit. The earlier proposed standalone `zkc.lean-interface/0` pipeline is
superseded. A future interactive Lean worker may cache projections of these
formats, but shares their environment identities, statuses and admission rules.
It cannot establish a weaker proposition after failing to prove the requested
one. Generated definitions and obligations do not import author companions;
the final assembler imports both.

## Delivery boundary

The [contract register](../spec/contracts.md) records semantic owners and identity
maps. The production cutover requires oracle-source coverage, complete request
reporting, native source/IR consistency, explicit source trust, editor/host parity
and the runtime-owned SDK format change. A checked source-level theorem has the
additional independent elaboration obligation above. The shared 4.1 FRI/STARK
acceptance source has separate frontend, IR, Lean and runtime results.
Uninstalled quartic suites, unrealized oracle families
or unproved cryptographic claims remain explicit owner obligations.
