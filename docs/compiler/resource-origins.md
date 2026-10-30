# Exact resource origins through local control

Scoped helpers use the shared [native execution resource-origin analysis](../../compiler/lib/Dialect/Exec/ResourceOrigins.cpp)
through the [Protocol analysis adapter](../../compiler/lib/Dialect/Protocol/IR/ResourceOrigins.cpp). The [capability map](../status.md#foundation-capability-map) owns
current coverage and the [structured iteration profile](../spec/ir/iteration.md)
owns the carried-root invariant.

## Purpose and scope

An affine result of `protocol.repeat` must preserve its corresponding input
resource root on every continuing iteration. A new SSA handle or generation can
have the same root; this does not establish state equality, equal bytes,
independent randomness or cryptographic correctness. Affine-use, history and
backend generation checks remain separate requirements.

The compiler's resource-origin analysis checks this invariant through local
branches, loops, capture-only
matches, local applications and static `protocol.apply`. The same local programs
remain legal outside a repeat even when their result root is unknown or they swap
roots.

## Analysis contract

Each isolated block or callable has a summary relative to its affine formal
inputs:

- An exact result names one formal input root.
- An absent result entry means unknown identity.
- A separate continuation flag records whether a local execution can return or
  yield. It never supplies a value origin.

Only demanded affine repeat obligations compute summaries. Common calls with
no affine results do not demand a callee summary; local calls still need
continuation information. Unknown origins are
refused at those obligations; they are not global formation errors. Ordinary
formation still checks all original bodies, including unused definitions and
stopped or constant-unselected arms. A limit is an analysis failure, distinct
from both an unknown root and a noncontinuing execution.

| Form | Transfer |
|---|---|
| Affine input | Its own symbolic root. Identity edges require affine values at both ends. |
| Installed state successor | Follow validated history, sampling and observation pairs. All applicable pairs for an output must identify the same exact input root; unknown or conflicting equations remain unknown. |
| Ordinary scoped `func.call` or `protocol.local_call` | Resolve the actual definition and substitute actual arguments into its formal-relative summary. Existing placement and call validation remain required. |
| `protocol.apply` | Summarize the mathematical callee and substitute its actual inputs under the role/application validation and preparation rules. |
| Scoped conditional | Join equal roots from every continuing arm. An explicit stopping arm contributes no returned value. |
| Scoped match | Join explicit captures the same way. Payload arguments have no inferred relation to an outer root. Existing private-tag history restrictions remain. |
| Scoped range loop | Give each affine carried slot a distinct symbol. A backedge preserving that slot proves the initial root, including zero trips. An unknown slot does not discard evidence for other slots. |
| `protocol.repeat` result | Follow the initial operand using the invariant independently checked for that repeat body. |
| Constructor or unknown transfer | Unknown; no identity equation is invented. |

Local loop captures remain non-affine. A body that always stops still permits a
zero-trip continuation with the initial roots. A swapping loop cannot prove its
per-slot invariant by assuming an even iteration count. Root sets, count-parity
reasoning, affine aggregate construction/projection and general CFG fixed points
are outside this transfer vocabulary. Carry resources in separate ports; a
required aggregate consumer can reopen that cut.

### Stops belong to one participant

Within one local function, continuation composes through nested control and
applications. One stopping arm and one identity arm can establish an exact
result. Two stopping arms cannot manufacture one; existing terminal-output
formation restrictions still apply.

A stop by role A cannot prune role B's subsequent common actions. In a common
protocol body, a no-return local call yields unknown outputs and analysis
continues. Mathematical application summaries never report local
noncontinuation as a global fact. In particular, A stopping followed by B
swapping two carried roots remains refused, directly and behind an application.
Projection removes A's local work from B's program.

## Implementation

The Protocol adapter resolves the actual scoped Func definition, checks its
borrowed Scope and Outcome signature against the logical call ports, and reads
the complete source execution closure. The scoped reader validates the actual
CFG, transfer dispatch and closed region associations before exposing the
borrowed native SSA view. Administrative ports do not imply resource-successor
laws. Calls retain their placement rules: ordinary `func.call` composes scoped
helpers; `protocol.local_call` belongs in common protocol control.

The [native API](../../compiler/include/zkc/Dialect/Exec/ResourceOrigins.h)
uses that admitted association over the immutable actual IR. It analyzes
ordinary calls, conditionals, capture-only matches and range loops, together
with installed state-successor contracts. An affine finite fold additionally
requires its actual callback to preserve each carried state root. Synthetic
Program realizations and serialized type spellings do not participate in native
admission or origin analysis. The neutral Program adapters remain responsible
for byte export and independent source/candidate comparison.

Native summaries are keyed by actual function identity within that owner.
Each summary stores formal input indices, not caller-specific roots. Calls
substitute actual arguments. The cache and the caller-owned cumulative allowance
live for one analysis invocation; the owner must remain immutable throughout.
Current application attributes do not specialize root contracts; a future
contract-changing parameter would require an instantiated key. Active calls
detect recursion. Cached summaries retain their complete nested depth, so a
shallow query cannot bypass a later deeper query's bound.

Module formation first checks every original body and collects affine repeat
obligations. A separate origin phase then shares one cache and budget over those
queries, so forward references cannot send summaries into unformed callees.
`mathematical::analyze` uses the same implementation with a fresh invocation. Its
containing module must already have passed formation, including every callee's
repeat invariant. Module verification checks all those bodies independently of
whether another summary uses a repeat's result. Queries do not bypass callee
formation or certify arbitrary supplied participant programs.

### Deterministic bounds

Each invocation has 100000 work units and at most 64 active call/structured-region
levels. A demanded repeat body starts at level one. Sequential operations and
successor chains spend work, not nesting depth. Existing formation, expansion,
projection and runtime limits remain independent and can refuse first.

The Protocol adapter and native execution analysis share a cumulative allowance.
The adapter charges common SSA operations, ports, region mappings and installed
successor equations. The native analysis charges declaration indexing,
callable queries and signatures, visited instructions, port substitutions,
control captures and results, installed successor equations, and returned
summary facts. Charges precede associated analysis storage growth. A cache hit
reuses body work but still checks the query's actual depth and charges query,
substitution and result costs. The owning implementations define the exact
accounting; one work unit is not a runtime cost or an MLIR operation count.

The initial discovery of whether a repeat has an affine obligation does not
start origin work for an otherwise unrelated program. Only affine origin facts
are stored. Source closure admission and native formation have independent
bounds; the origin allowance does not replace them.

Exhaustion or excessive depth emits `mathematical-analysis-limit`; an unresolved
root retains `mathematical-formation` with the exact-root detail. Invalid symbols
and cycles remain formation errors, with earlier ordinary diagnostics preserved.
Private test limits isolate this analysis where another formation limit would
otherwise refuse first; source attributes and CLI options cannot raise the bound.

## Evidence and remaining boundaries

The maintained [compiler controls](../../compiler/test/resource_origins.py) cover
identity/control inside and outside repeats, static applications, standalone
swaps/replacements, conflicting branches, unknown aggregate payload roots,
per-slot loop evidence, local stopping and cross-role stop counterexamples.
They retain private-match history and affine-reuse refusals.
The [native API controls](../../compiler/test/native_resource_origins.cpp)
exercise actual function ownership, cumulative allowances, cached depth,
state-successor contracts and exact root joins. The existing
[Protocol API controls](../../compiler/test/resource_origin_analysis.cpp)
also cover stage admission, per-program queries and demanded-query work
sharing with native Func/Exec helpers. They no longer depend on synthetic
Program local definitions.

The [scoped source generator](../../compiler/test/resource_origin_sources.cpp)
authors the current compiler controls and the fresh runtime fixtures directly
with Func, Exec and Protocol operations. Its execution source carries RNG and
transcript resources through nested common/local loops, applications, both
Boolean arms and both match tags. The
[runtime client](../../crates/zkc-test-drivers/src/resource_origins.rs) checks returned
roots, generations, actual draw/observation/challenge counters, budgets, stop,
cancellation, backend failure and frame cleanup. Stops are exercised before any
draw and after transitions inside nested control; cancellation occurs between
outer iterations. It runs zero, one and several iterations in ordinary,
unsimplified and storage-release modes. Compiler checks confirm retained
branches, matches and both loop forms, plus explicit storage releases. These
checks compare resource transitions, not sampled values across modes. The existing
native host handles structured loop control and participant execution.

This is finite source-admission and execution evidence. Supplied-participant
readers still enforce their own type/custody contracts; they do not infer
mathematical source correspondence. No new Lean semantics, independent retry
host, external transcript deployment or security theorem follows.

[Native attempts](../runtime/attempts.md) use the shared controller and
`produce_admitted` driver. The [structured proof boundary](construction.md),
[nested data](mathematics.md) and [mathematical composition](mathematics.md)
use the same participant execution path. The [roadmap](../roadmap.md) records
remaining native correspondence work.
