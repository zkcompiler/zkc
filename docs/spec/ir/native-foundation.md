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
Its required `function_type` is the complete executable ABI, including the
borrowed scope and one outcome. The mathematical signature is independently
derived from the catalog; erasing the outer representation of each value port
must reproduce it exactly. Physical selection is carried by those actual ports;
there is no native `physical_arguments` attribute. A declaration cannot install
executable code. Program-byte interchange still represents installation choices
in its own binding record, reconstructed and checked at that boundary.

The installed invocation is `exec.apply`. Its native signature is:

```text
(runtime.scope, inputs...) -> exec.outcome<(results...)>
```

`runtime.binding` implements `CallableOpInterface` as a declaration without a
body. `exec.apply` implements `CallOpInterface`; all its operands, including
scope, and its one outcome result must exactly match the callable signature.
These interfaces expose structural call information, without purity, inlining,
implementation admission, or successful execution guarantees. The standard
optional `arg_attrs` and `res_attrs` arrays index the actual ABI, including
scope and outcome; formation requires one dictionary per corresponding port.
Byte publication refuses nonempty dictionaries until it has an interpretation
for them, so an annotation is never silently discarded.
ABI-sized empty dictionaries are semantically inert and are accepted by native
body readers and correspondence checks, including ordinary function calls.
Wrong dictionary arity fails binding/application formation. Native admission
also checks ordinary-call dictionary arity, which standard Func formation does
not enforce.

The declaration's derived logical signature and stored executable scope/outcome
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

SymbolUserOpInterface checks the actual lexical binding and call signature.
Selection/admission independently checks applicability of the chosen
implementation and every represented port. `exec.compute` does not acquire the
call interface by analogy: its mathematical helper has a different ABI from
the scoped execution boundary. Calling a binding is not protocol composition
or an ordinary mathematical helper application.
`exec.compute`, finite requests, scope transitions, outcome dispatch and
publication keep their separate meanings where they are observably distinct.
Per-contract executable wrapper operations are absent;
mathematical operation identities remain available to analyses and rewrites.

Structured TypeDef/AttrDef and inherent properties carry complete aggregate,
parameter and execution descriptor information. Generic IR verifiers compare
formed MLIR types; they do not print them, parse a neutral spelling and compare
the reconstructed type. Native neutral types remain independent of MLIR.
Recursive Host layouts support standard MLIR attribute aliases. Their printed
nesting therefore need not grow with source schema depth. Aliases change no
layout identity, logical depth allowance or parser resource ceiling; native
formation still inspects the complete expanded structure.
Host emission lowers checked source directly to Func/CF, Data operations and
Exec outcomes. Explicit region arguments retain captures; ordinary native ports
and layouts retain schemas. Function metadata supplies only parameter names.
Independent artifact reconstruction reads actual SSA and checks the complete
closed control profile, without a body-shaped annotation or duplicate signature
document. Expected source rendering belongs only to boundary comparison.
Logical formation checks typed catalog arguments and all nominal variant
alternatives. A represented carrier additionally checks its exact logical type,
representation identity and ordered represented children. Sequence and variant
layouts retain every child representation; installed dense layouts constrain the
complete child layout, not just the erased field. The checked represented-type
constructor and parser use the same native structural verification. Type-only
execution and finite-domain verifiers do not acquire byte-format limits by
serializing their ports. Source, operation and target profiles remain separately
admitted; forming a type does not install executable code or grant a wire codec.

Applied representation patterns and their child layouts are typed installation
facts. Native formation matches catalog type observations against those facts;
it neither owns a duplicate representation table nor reparses a caller type.
Expanded structural depth, occurrence and metadata limits apply even to shared,
context-uniqued children. The independent program-type reader retains its own
serialization bounds and exact layout checks.

Canonical public spellings are encoded/decoded at format boundaries once,
under explicit work limits. Keeping a stable public spelling is not a second
internal schema or compatibility execution route.

### Field literals and selected Ring parameters

The pure `data.index` operation carries an unsigned 64-bit `IntegerAttr` and
returns `ui64`. It implements `ConstantLike` and folds to that exact attribute;
the Data dialect materializes only matching `ui64` attributes. This supports
standard constant queries without adopting `arith.constant`'s signless integer
contract. Generic folding does not authorize movement of reached executable
invocations or alter their charges. External decimal spellings belong to source
and format adapters, not the native constant's formation rule.

`algebra.literal` retains its nominal `algebra.field` type and an unsigned
integer attribute. The integer width is the declared binary presentation width,
or the bit width of the modulus minus one for a natural literal. Naturals are
strictly below the modulus. Binary presentations admit their exact bit patterns;
the byte spelling uses `0` and `1` for those two values and minimal lowercase
hexadecimal for other patterns. Formation performs no reduction, field coercion
or interpretation of an arbitrary string. This representation does not enlarge
the set of supported field presentations.

Source mathematics stays in ordinary scalar SSA. A selected numerical kernel's
Ring graph is immutable parameter data: `algebra.ring_expression` retains
ordered nominal input types, typed `algebra.ring_node` attributes and output
indices. Node kinds are enums. Edges, input positions, literals and embedding
targets are checked directly, including field agreement, acyclicity, depth and
reachability. Unused input slots and repeated input nodes remain distinct.
The owning [Ring contract](../domains/ring-expressions.md) defines the graph;
the native carrier does not store another independently authored copy of a
source function.

This distinction is observable: [numerical execution](../runtime/numerical.md)
charges for encoded graph bytes and nodes, and allocates node-dependent scratch.
Replacing the selected graph with an ordinary optimizable scalar region could
change budget outcomes or exact bytes merely by sharing input nodes. Earlier
checked selection may derive or change the graph; storing or serializing an
already selected parameter preserves its order and sharing exactly. MLIR
attribute formation does not establish numerical-call admission. The call's
positional signature, restricted numerical profile, and encoded-size limits
remain separate checks at their owning boundaries. Numerical parameter admission
checks the actual typed graph and counts its canonical output bytes without
building or reparsing a string. Native encoding is tested against the independent
neutral Ring writer, including empty graphs, constant-only graphs and the exact
numerical byte ceiling.

### Source origins and asset parameters

`runtime.origin` contains an entry identity, an ordered path of
`runtime.origin_step` attributes, and one `runtime.query_origin`,
`runtime.message_origin` or `runtime.start_origin` event. Path kinds are the
`apply` and `repeat` enum cases. A query stores its service-input index as u64,
separately from its service contract, method and owner; it does not parse an
`input_N` name internally. Message events retain schema, sender and receiver.
Start events retain the original caller and application site. All names, the
path bound and the 2048-byte canonical template bound follow the
[native occurrence contract](construction.md#native-occurrence-encoding).
Native formation checks these fields and accounts for framing directly. The
hexadecimal template belongs to the byte boundary. Formation neither establishes
source correspondence nor proves distinct transcript namespaces.

`runtime.asset` holds its nominal format identity and exactly 32 digest bytes.
The invocation's catalog schema determines the required asset format. Equal
digests in different formats remain different references. Neither constructing
this attribute nor passing its shape check authorizes an asset, setup or mutable
resource. Hexadecimal spelling is an interchange encoding of the digest bytes.

Pure `algebra.constant` uses the same typed field-literal attribute as execution
parameters. Its fold and materializer preserve the nominal field; ordered
polynomial domain points also use these attributes. Internal interpolation
computes native integer values without a text round trip.

Invocation admission derives associated identities and complete type terms from
the same native catalog scope used for callable signatures. Ordinary natural
parameters use unsigned 64-bit integer attributes; field literals cannot be
substituted for them or for a different nominal field. Sampling and observation
facets determine an origin parameter's event kind and query method. These checks
establish parameter formation, not physical installation, reached execution,
source correspondence or a security-transform theorem.


Compiler analyses inspect actual SSA values, control regions and symbol
dependencies. Reconstructing a neutral executable program and caching it as the
compiler's working representation does not satisfy this boundary. Neutral
program definitions remain useful at independent byte admission and comparison
boundaries; the catalog remains immutable declaration data. Neither becomes a
second mutable compiler IR.

The declaration catalog has one complete operation collection. Fixed-port
signatures and the closed numerical signature family are explicit alternatives;
a dynamic family is never represented by its empty-mask ports. Resource-unit
signatures carry their nominal Slot root. Physical adapter contracts are also
catalog rows: `representation.convert` has erasure `T -> T`, and
`table.relayout` has erasure `table[F] -> table[F]`. Their authoring stage is
`Physical`; deriving these ports grants neither logical-stage admission nor a
mathematical identity rewrite. Actual represented ports, implementation
installation and reached conversion behavior remain independent obligations.
The program/0 codec retains table layout names in its existing byte argument
positions; these are physical selections, not extra catalog scope roots. Consumer profiles select supported
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
Complete relation and finite-domain signatures share these limits across their
inputs or items. Relation consistency compares native constructors, typed
arguments and nominal identity/alternative trees across contexts; its immutable
data profile is checked separately from general logical formation and Copy/Drop.
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

Protocol formation reads the same native type facts. Oracle table kinds retain
native row types and derive native Data/Query/Answer associations. The shared
collection-constructor rule also drives the independent neutral reader;
formation does not require that a native row fit the public byte grammar.
Service methods carry typed logical declarations. Native query checks compare
catalog applications and exact nominal identities; they do not encode actual
ports to compare strings. Construction state and codec-record slots use native
formation and Copy/Drop permissions. Service authority, query availability,
construction ownership and publication remain separate checks.

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
Bound actual structural nesting and cumulative work before recursive verification
or walking, including selected computation modules and dormant definitions.
Generic optimization runs only after admission has established the premises of
the chosen mathematical profile; structural purity alone cannot erase an invalid
body before admission.

Analyses are owned by the isolated module/symbol scope containing the mutable
dependencies they inspect. Cross-callable admission runs at that enclosing
scope; a nested function pass must not walk sibling definitions. Such a pass
may consume a parent snapshot only when the inspected facts remain fixed for
that phase. A cached parent analysis can be stale: its presence does not
certify current closure admission.

Scoped data admission is distinct from scope/transfer ownership. It consumes
actual SSA data operands according to their native Copy/Drop permissions.
Mutually exclusive arms each receive their own formals; duplicate Copy captures
remain distinct ports. Iteration invariants require Copy, while carried state
may be affine. Explicit physical storage release invalidates even a Copy value.
Every potential arm and dormant callable remains checked. Ordered history
transitions are forbidden inside variant matches, including transitions reached
through helpers or finite callbacks.

The closed scoped call/control graph includes actual outlined functions and
finite step/predicate callbacks. It is acyclic and bounded to 64 functions along
one path, including the root. Cached summaries retain subtree height rather
than only visitation. Expanded control occurrences share a 65,536-instruction
ceiling; signatures have at most 1,024 data ports. Graph, occurrence and data-use
work share the reader's remaining allowance. Byte encodings impose their own
size and JSON-depth constraints at export; they do not define native control
nesting or affine validity.

Executable participant admission likewise reads actual SSA, scoped callee
signatures, service declarations, message schemas and entry targets. A service
port retains its declared ingress position among data and service inputs; its
identity is independent of SSA names or names invented at export. Selected
service data ports must have the installed service's exact representation.
Message schema types agree within each protocol instance. Conditional completion
consumes each affine result and introduces its continuing value explicitly.
Loop invariants require Copy and can give distinct formals the same actual.

Participant admission has a separate 65,536-instruction ceiling and one million
work units across all participants, with at most 64 nested body levels. Its
combined callable inventory counts actual ordinary functions, domains and
participants, with a limit of 4,096. Synthetic realization names do not count.
The byte exporter independently applies its aggregate artifact limits and
reserves service identities when naming values. It preserves capture binding
multiplicity: Copy allows duplicate uses but does not erase a formal's owned
storage charge. The current byte grammar cannot represent distinct capture
formals bound to the same actual name, so those native shapes refuse at export.
Artifact comparison checks the complete capture interface, including unused
formals. Equal returned values alone do not establish resource correspondence.

Resource-origin facts are relative to actual data formals, with the borrowed
scope excluded. Closed-region summaries substitute through explicit captures;
match payload roots begin unknown. Continuing alternatives must agree on a
root. A stopped path contributes no returning value, while a zero-trip loop
retains its initial state even when reached iterations stop. Ordered finite
state requires the corresponding affine root from every continuing callback
result. Catalog successor facets constrain these facts jointly; contradictory
facets yield unknown. One invocation shares work bounds, and cached summaries
retain their complete nested height. These are native semantic checks over
immutable SSA, not permission inferred from a signature or a serialized body.

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
Analysis storage must keep any borrowed summary valid across recursive cache
population. Depth limits measure actual dependency path height, including cached
subtrees, independently of root visitation order. A finite callback is one
dependency edge; traversing the containing operation does not add another edge.

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
Pass and direct API initialization share the complete created-dialect inventory,
including temporary candidates; registration alone does not imply loading.

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
