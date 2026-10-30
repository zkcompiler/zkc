# Native MLIR foundation

This contract defines the target compiler structure and its shared boundaries.
It is specified before the implementation cutover; [status](../../status.md)
distinguishes specified formats from supported producers and consumers. The
[interface inventory](../formats/foundation-interfaces.md) records the schema
changes consumers must implement under development version `0`.

## Ownership and stages

The frontend owns the immutable checked program, source specifications and
closed instance selection. Translation consumes that checked program. Source,
syntax and Language public APIs do not depend on MLIR or a Lean process.
Neutral declarations own operation identities, kinded static parameters,
signatures, capabilities and implementation requirements. IR owns their MLIR
projection, lowering, application associations and stage admission.

Protocol, Relation, Algebra, Poly and Data retain their mathematical and protocol
meaning until the last responsible consumer. Crypto and Commitment currently
own types and attributes, with installed actions reached through Exec. A future
scheme operation needs a consumer that requires its distinct semantics; an empty
operation inventory is not a reason to manufacture operations or merge owners.
Func/SCF/CF provide ordinary functions and control. Tensor/Linalg provide
structured computations with admitted scalar meanings. Their use does not grant
vectorization, bufferization or protocol-motion laws implicitly.

The common admitted target ingress precedes native resident representation
selection. Target-neutral domains, setup, roles, explicit outcomes, widths,
loop rules and complete layouts remain readable without acquiring a native
handle. AOT and a new execution backend are not requirements of this contract.

## Typed declarations and reached invocation

`runtime.binding` declares a resolved logical operation and its static
specialization. It retains its exact contract identity, kinded arguments,
implementation constraint and resolved signature as inherent structured data.
Physical selection additionally fixes complete represented ports and the
selected immutable installation. A declaration cannot install executable code.

The installed invocation is `exec.apply`. Its native signature is:

```text
(runtime.scope, inputs...) -> exec.outcome<(results...)>
```

The declaration's resolved logical signature and executable scope/outcome
signature are distinct projections of the same contract. Native signature
formation evaluates the catalog's ordered static scope directly. Domain and
Slot roots are `StringAttr`, Type roots are `TypeAttr`, and Nat roots are
unsigned 64-bit `IntegerAttr`. Associated members use installed nominal facts;
application terms construct the owning native type from earlier typed terms.
Complete-Type ports retain the exact native type. The numerical family alone
has a trailing `DenseBoolArrayAttr` mask, bounded to 1023 positions; its bits
select scalar/vector operands in order. It does not use a textual binary mask
or a natural as an alternative encoding.

Signature formation checks logical type formation and catalog requirements.
It grants neither message-codec support nor an implementation or stage profile.
A signature may therefore form even when an executable or interchange consumer
cannot admit it. This distinction also keeps byte-parser bounds out of native
mathematical port derivation. Scope is borrowed
according to the execution rules; it is not a mathematical operand or a proof
token. The call retains the actual ordered operands, structured parameters,
source occurrence and referenced declaration. Reached validation, charging,
kernel effects, output validation and retention are part of invocation behavior.

The binding's stored `function_type` is the actual executable signature above.
Logical ports are derived from the catalog; they are not another independently
authored signature. At a logical stage, the stored ports must agree exactly
with that derivation. Physical selection replaces value ports with complete
represented types; erasing those representations must recover the same logical
ports. Actual represented ports determine layout choices. Do not retain a
second string-carried `physical_arguments` schema inside the IR: encoding an
existing program-byte binding recovers its boundary arguments from the selected
ports. Selection/admission independently checks applicability of the chosen
implementation and every represented port.

Use CallableOpInterface, CallOpInterface and SymbolUserOpInterface at this
boundary with exact type checks and correct symbol scope. The binding is an
external callable with no callable region. Its argument types include scope;
its sole result is the typed outcome. The call interface exposes all actual
operands, including scope. Standard argument/result attribute arrays, when
present, follow that executable signature. None of these interfaces grants
inlining, speculation, purity or permission to ignore reached failure.
`exec.compute` does not acquire this interface by analogy: its mathematical
helper has a different ABI from the scoped execution boundary. Calling a binding is
not protocol composition or an ordinary mathematical helper application.
`exec.compute`, finite requests, scope transitions, outcome dispatch and
publication keep their separate meanings where they are observably distinct.
Per-contract executable wrapper operations are absent;
mathematical operation identities remain available to analyses and rewrites.

Structured TypeDef/AttrDef and inherent properties carry complete aggregate,
parameter and execution descriptor information. Generic IR verifiers compare
formed MLIR types; they do not print them, parse a neutral spelling and compare
the reconstructed type. Native neutral types remain independent of MLIR.
Canonical public spellings are encoded/decoded at format boundaries once,
under explicit work limits. Keeping a stable public spelling is not a second
internal schema or compatibility execution route.

Compiler analyses inspect actual SSA values, control regions and symbol
dependencies. Reconstructing a neutral executable program and caching it as the
compiler's working representation does not satisfy this boundary. Neutral
program definitions remain useful at independent byte admission and comparison
boundaries; the catalog remains immutable declaration data. Neither becomes a
second mutable compiler IR.

The declaration catalog has one complete operation collection. Fixed-port
signatures and the closed numerical signature family are explicit alternatives;
a dynamic family is never represented by its empty-mask ports. Resource-unit
signatures carry their nominal Slot root. Consumer profiles select supported
identities and forms separately, and native containers are not logical type
constructor declarations. Generated projections share these facts while each
consumer retains its own installation and interpretation obligations.

## Native logical type observation

`CatalogTypeInterface` exposes the catalog constructor and ordered arguments
of a native MLIR type through typed getters. Domain and Slot identities use
`StringAttr`, complete types use `TypeAttr`, and naturals use unsigned 64-bit
`IntegerAttr`. The observation is transient; the MLIR type remains the sole
carrier. The catalog defines argument kinds and constructor permissions.
Shared carriers such as builtin integers can have the interface while returning
no logical application: only signless `i1` and unsigned `ui64` denote the
Boolean and Index constructors. A tensor's shape does not identify a nominal
collection. Nominal variants expose their structural identity and alternatives
directly rather than inventing a catalog constructor.

The native binding inventory generates external interface models. Owned
dialects attach their models after registering types, so intrinsic formation
works in a minimal context. MLIR dialect extensions attach models for builtin
and contributed carriers in a composed registry. Registration does not load an
unrequested dialect, replace a native type, or grant an execution profile. Typed observations and
serialization callbacks are distinct; observations never invoke an encoder.
Missing or ambiguous constructor observations are refused. The same native
inventory supplies typed construction callbacks, distinct from byte decoding.
Construction validates argument kinds, identities and bounds before calling a
loaded native owner, then checks that the resulting type observes exactly the
requested application. It cannot load a missing dialect or infer a carrier
from a shape. Native owners retain their intrinsic verification obligations.

Logical formation checks argument kinds, declared nominal instances and
constructor permissions through these observations. Copy and drop permission
propagate through every complete-type argument and every variant alternative,
including inactive alternatives. A sequence requires both permissions from its
element. This check does not install a codec or physical representation.
Structural inspection bounds expanded occurrences, including repeated uniqued
children, to 200000, depth below 64, and attribute string bytes to 64 MiB.
Runtime resource types store an explicit `CapabilityKind` enum and a separate
nominal identity. Randomness, nonce, transcript and resource-slot tags are
structurally distinct even when identities coincide. Transcript consumers use
the enum and identity getters; they do not parse a `kind:identity` string.
Formation refuses unknown enum values and inadmissible identities. The previous
combined MLIR spelling is removed; the existing neutral byte spelling remains
owned by its codec boundary.

Natural type parameters remain bounded by 1048576. Public byte encodings have
separate bounds: native formation alone never authorizes serialization.

Native use policies inspect these same typed observations and every variant
alternative. Copy permission does not imply a message frame, constructibility
or protocol-boundary permission. Closed frame membership is checked separately
from atomic default-codec selection. Native policy analysis bounds expanded
type/metadata nodes to 200000 and metadata string bytes to 1 MiB across distinct
queried types; repeated queries may reuse immutable type facts. It neither
constructs canonical spellings nor uses byte-parser depth as a mathematical
permission test. Publication still enforces its independent encoding limits.

## Formation, admission and invalidation

Ordinary MLIR verification establishes structural formation, region/operand
agreement and symbol-use validity. Explicit stage admission checks the whole
permitted vocabulary, callable closure, all dormant definitions, ownership,
setup, effects, bounds and selected installation. A profile attribute states
an intended stage and does not certify admission.

CLI entry points, already-parsed C++ APIs, textual pipelines, imports and
publication call the same admission service. No public entry may rely on the
side effect of a previous module verifier or a copied checked annotation.
The complete mutation-to-publication path rechecks the applicable stage.

Analyses are owned by the isolated module/symbol scope containing the mutable
dependencies they inspect. Cross-callable admission runs at that enclosing
scope; a nested function pass must not walk sibling definitions. Such a pass
may consume a parent snapshot only when the inspected facts remain fixed for
that phase. A cached parent analysis can be stale: its presence does not
certify current closure admission.

AnalysisManager supplies caching and invalidation mechanics. Analyses must
explicitly implement dependency invalidation when selective preservation is
used; requesting another analysis does not register that rule automatically.
Preserving a derived analysis requires preserving every fact on which it
depends. Invalidation includes changed callees, roles, domains, parameters,
installations and bodies, even when the caller is unchanged. These requirements
follow the [MLIR pass restrictions and analysis rules](https://mlir.llvm.org/docs/PassManagement/).

Cache policy-independent facts; a policy-dependent result is valid only under
the exact immutable policy and unchanged inspected IR. Direct APIs either
invalidate at the owning scope or compute fresh facts. Mutating IR does not
notify an AnalysisManager automatically, and invalidating a child analysis
does not refresh a parent snapshot. Reacquire facts after mutation before
admission or publication; do not reuse references to invalidated analyses.
Context-uniqued types do not certify a mutable declaration's meaning or
permission to execute.

Use ordinary rewrite patterns for local changes and explicit legality plus
TypeConverter for stage/type conversion. Global projection and realization may
use structured algorithms. Every route validates the actual produced candidate;
conversion success alone establishes no source correspondence. Unresolved
conversion casts, unknown executable forms and unsupported semantic attributes
refuse before publication.

Catalog laws state mathematical obligations. They do not automatically authorize
canonicalization, operand sorting or a commutative trait on every checked path.
A transformation must stay within the comparison relation of each required
checker on its crossing, as well as its observation and budget contract. A
reader that recognizes algebraic rearrangement does not enlarge a different
reader's structural relation. Extending a checked relation is a separate change;
until then its unsupported rewrites refuse that profile. This does not prohibit
a separately admitted optimization profile or require every consumer to support
the same equivalences.

## Stage pipelines and target selection

Stage objects own retained originals and checked source/candidate associations.
Those originals do not become mutable attributes solely to fit a whole compile
into one pass pipeline. Each stage uses one shared pipeline builder with explicit
policy options. The C++ API and registered textual pipeline use that same
builder. A stage pipeline admits its input and actual output; publication also
checks the current output. Textual reproduction covers a stage and its explicit
inputs/options, not retained originals that were never serialized with it.

Admission's vocabulary check is read-only. Native operation/profile declarations
provide one legality description for that check and for stage conversion.
Neutral catalog facets provide contract availability; they do not enumerate
MLIR operation names or grant an entire standard dialect. Dynamic legality
checks operand types and semantic attributes where needed. Every nested and
dormant definition is inspected. Conversion success, including a conversion
that folds operations, cannot serve as a read-only admission check.
Pass instrumentation observes execution; an admission pass or direct service
reports failure through the normal failure channel.

Physical ingress records the selected target installation and its restrictions
as typed IR data on the owning compilation scope. Caller configuration may
select this data, but hidden defaults cannot override an explicit selection on
another entry route. Selection states intent: independent installation checks
must still cover every actual represented port, selected implementation and
required service, including unused declarations and inactive aggregate arms.
Catalog availability is not evidence that a backend was compiled or installed.

Target policy is separate from mathematical operation semantics and from the
program-byte language. Record it with the compilation subject and check it at
publication; it is not a new field silently inserted into `zkc.program/0` or
authority for an independent runtime reader. Common target ingress continues
to refuse native resident representations before the target branch. The
foundation implements the existing native installation; device hierarchies,
per-role placement and new executable formats need their own concrete consumers.

## Outcomes, observations and budgets

The execution result is either an ordered returned tuple or a stop with its
cause and occurrence. A stopped prefix invokes no continuation. Previously
reached sends, queries, provider effects and resource consumption remain part
of that prefix. A recoverable error encoded as ordinary data is a return, not
an execution stop.

The existing [VM](../runtime/vm.md), [capacity](../runtime/capacity.md) and
[scope rules](execution.md) define charging, refusal precedence and cleanup.
This foundation preserves their reached schedule. In particular, a type-correct
call does not move setup/custody validation before its occurrence, permit a
failed child to publish values, or erase work consumed before a stop. Cleanup
keeps its specified failure-combination and transfer rules.

Native refactoring preserves outputs, selected stops, ordered observations,
budget charges and observable residual state on the admitted profile. A later
optimization with a different cost schedule needs an explicit refinement
contract. Mathematical value equality alone is insufficient. Malformed raw
artifacts are independently rejected at admission; there is no requirement to
reproduce a historical permissive interpreter's behavior on inadmissible input.

Effect interfaces conservatively expose ordered observations, meter state,
custody and publication. Start with a shared ordering resource for operations
whose relative order matters. Distinct buffers do not justify swapping queries
or first-stop behavior. Mark an operation pure/speculatable only under its
actual totality and effect contract, not because a catalog row calls its result
deterministic.

## Index arithmetic

Logical indices are unsigned integers in `0..2^64-1`. Existing checked add,
subtract, multiply, divide and remainder retain reached refusal on overflow,
underflow and zero divisor. Comparisons do not reinterpret them as field
elements or target-sized MLIR `index` values. No FRI-specific primitive is
introduced by the foundation.

For `n = 2*h`, `h > 0`, `p < n` and representable `n`, the library family
`low = p % h`, `high = low + h` has `low < h <= high < n`. Antipodal FRI
interpretation additionally requires the selected domain ordering and its
pairing convention. Power-of-two and installed capacity premises belong to
that profile. A zero divisor or out-of-range query cannot be repaired by a
copied admissibility flag. The source guard must be reached before visible
answer/authentication work. Bounds analyses may guide a transformation; they
do not supply independent proof evidence.

## Independent consumers

Shared catalog data describes signatures, rules and mathematical obligations;
it does not implement or prove a Lean meaning. Native C++ and Rust consumers
retain independent admission and execution obligations. The foundation changes
no file under `lean/`, produces no Lean patch or handoff, and uses no Lean build
as its landing gate. Formal interpretation follows the published schemas and
remains separately reported. Native support for a schema never implies that a
formal consumer already admits it.

## Verification scope

Claims for the paper are relative to the admitted original IR. Frontend
elaboration into that IR and rendering executable bytes into Lean data are
named deterministic trust boundaries. Existing native comparisons, byte
admission and regression controls remain required; naming a trust boundary does
not authorize deleting them. Security-transforming Fiat–Shamir construction
and commitment realization retain their independently checked Lean obligations.
The flagship formal target is the realized compiled verifier, while the native
path still emits and runs program bytes. Formal STARK-operation lowering and a
formal byte reader are neither foundation nor subsequent IR delivery gates.
