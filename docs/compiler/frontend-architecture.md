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

An existing-family baseline is field addition: prelude `field_add`/`+`, the `field.add`
TableGen signature, the runtime's admitted `arkworks/field.add` adapter, and
Lean's installed `.fieldAdd` interpretation. Preserve the existing mathematical
laws and native-kernel trust boundary. The joint probe follows the IR owner's FRI index-map candidate, comparing library
operations with new primitives and fixing bounds, widths, zero-size and overflow
behavior. Check source resolution, actual IR contracts, runtime output, Lean
selection and one reused law before generating a larger cross-language registry. A successful metadata join is not a simulation
theorem. Oracle family additions likewise use the IR owner's descriptors.

This follows the useful part of MLIR's
[operation definitions](https://mlir.llvm.org/docs/DefiningDialects/Operations/):
central declarative facts can generate repetitive accessors and validation.
MLIR [interfaces](https://mlir.llvm.org/docs/Interfaces/) motivate explicit
capabilities for consumers of different operation families. Neither mechanism
requires putting the source parser or Lean proof terms inside MLIR. Reuse the
existing zkc TableGen/catalog machinery; adding a second schema engine would
increase the number of contracts that must agree.

## Formal and executable connection

The [checked-elaboration contract](../spec/language/elaboration.md) fixes what
Lean's future independent source checker must reconstruct, including complete
coverage in both directions. The neutral written model, binding observations,
closed instances and exact structured admission are its input. The checker must
reject additional observable operations as well as omitted ones unless an
explicit semantic rule justifies the transformation.

Every authored postcondition and security request enters the required inventory.
[Companion keys](../spec/language/companions.md) support lookup of a proof against
an already fixed proposition. Consumer requirements independently fix the desired
request set; they are compared inside the existing Lean receipt audit. These
mechanisms solve separate problems: a stable key cannot establish meaning, and
an inventory cannot infer a postcondition the author never wrote.

Reuse `zkc.declarations/0`, subjects, bound requests, record checks and the receipt
audit. The earlier proposed standalone `zkc.lean-interface/0` pipeline is
superseded. A future interactive Lean worker may cache projections of these
formats, but shares their environment identities, statuses and admission rules.
It cannot establish a weaker proposition after failing to prove the requested
one. Generated definitions and obligations do not import author companions;
the final assembler imports both.

## Delivery boundary

The [contract register](../spec/contracts.md) records semantic owners and identity
maps. The production cutover requires oracle-source coverage, actual request and
source correspondence, editor/host parity and the runtime-owned SDK format
change. The shared 4.1 FRI/STARK acceptance source has separate frontend, IR,
Lean and runtime results. Uninstalled quartic suites, unrealized oracle families
or unproved cryptographic claims remain explicit owner obligations.
