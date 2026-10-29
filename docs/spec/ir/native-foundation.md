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

Protocol, Relation, Algebra, Poly, Data and cryptographic operations retain
their mathematical and protocol meaning until the last responsible consumer.
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
signature are distinct projections of the same contract. Scope is borrowed
according to the execution rules; it is not a mathematical operand or a proof
token. The call retains the actual ordered operands, structured parameters,
source occurrence and referenced declaration. Reached validation, charging,
kernel effects, output validation and retention are part of invocation behavior.

Use CallableOpInterface, CallOpInterface and SymbolUserOpInterface at this
boundary with exact type checks and correct symbol scope. Calling a binding is
not protocol composition or an ordinary mathematical helper application.
`exec.compute`, finite requests, scope transitions, outcome dispatch and
publication keep their separate meanings where they are observably distinct.
Per-contract executable wrapper operations are removed after the cutover;
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

Analyses are owned by the module/symbol scope they inspect. AnalysisManager
tracks dependencies and invalidation. Invalidation includes changed callees,
roles, domains, parameters, installations and bodies, even when the caller is
unchanged. Cache policy-independent facts; a policy-dependent result is valid
only under the exact immutable policy and module revision. Direct APIs either
invalidate explicitly or compute fresh facts. Context-uniqued types do not
certify a mutable declaration's meaning or permission to execute.

Use ordinary rewrite patterns for local changes and explicit legality plus
TypeConverter for stage/type conversion. Global projection and realization may
use structured algorithms. Every route validates the actual produced candidate;
conversion success alone establishes no source correspondence. Unresolved
conversion casts, unknown executable forms and unsupported semantic attributes
refuse before publication.

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
