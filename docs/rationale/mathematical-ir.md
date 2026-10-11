# Mathematical IR uses ordinary SSA

The [mathematical profile](../spec/ir/protocols.md)
keeps total mathematics in ordinary typed SSA. Role interfaces and explicit
restrictions state availability boundaries; analysis derives intermediate
availability from dependencies. Structured control uses regions, and functions
provide reusable definitions.

## Why keep the graph in MLIR

SSA already represents shared values and their dependencies. A second editable
mathematical graph would duplicate operands, symbols, types and source locations
and require every transformation to synchronize them. Analyses and checkers can
build transient views without making another representation authoritative.

Wrapping every expression in an isolated compute region adds captures and
results through which analyses must propagate the same facts. Such a boundary
is useful for actual control, isolation or execution placement; it contributes
little around each total expression. Transparent regions do not impose the
same capture cost, but still need a consumer to justify their structure.

A role-qualified type such as `at<T, A>` would also spread placement through
mathematical type handling. Ordinary types plus declared interfaces and derived
availability suffice for the current contract. Availability alone establishes
neither agreement between roles nor permission to disclose a value.

## Representations follow consumers

The [four profiles](../compiler/pipeline.md) preserve different facts:
joint mathematics, participant behavior, executable calculations and physical
choices. Domain dialects keep their ownership across those profiles. Phase
legality, observation policies and analysis facts are judgments on a program;
each does not need another IR. Group or Boolean computations do not acquire a
polynomial stage merely because other protocols use polynomials.

An opaque host callback would lose inspectable computation. Conversely, an
interpretation alone supplies no materialized target for a lower-level analysis.
Build a form where a consumer needs it, with its preservation obligation. The
[formal semantics](../../lean/docs/design/semantics.md#interpretation-and-representations)
explains that distinction independently of the native pipeline.

The tradeoff is that placement and preservation need explicit analyses rather
than being encoded in every value's type. This is a choice for the supported
contracts, not a proof that flat SSA suits every future feature. A new region or
type boundary should solve a concrete consumer's requirement.

## Finite callbacks and direct emission

Finite domains and callbacks remain symbol-based definitions. A checked ABI
adapter partitions their inputs into current state, enumerated items, domain
inputs and captures. Each consumer reconstructs its own mapping; equal SSA
actuals retain distinct formal positions, and current state never becomes an
alias for its initial seed. This supports reusable helpers and nested
computations without duplicating their bodies in every expression.

A prototype compared direct symbol-body emission with an explicit-capture
region using MLIR's dialect conversion. Both produced the same small SCF
loop in that experiment, including zero-trip and aliased-input cases. This
establishes feasibility for the toy integer loop, not equivalence of the full
zkc finite contract. It supplies no demonstrated optimization benefit that
would justify a second canonical representation and its admission rules.

The implementation instead removes temporary emission functions: finite
expressions emit directly at the caller's insertion point through an MLIR
rewriter. A persistent finite declaration uses the same body emitter inside
its generated function. Callback expansion and polynomial normalization still
use a checked scratch clone and may fail after mutation. They remain before
primitive dialect conversion until they can meet its rewrite contract.

## Analysis, choices and checking

The structural computation view borrows the admitted SSA: ordered domain
constructors, occurrence-specific axes, actual/formal environments, accesses,
state and results. Private transformation equations interpret that structure;
private recipes select installed logical algorithms. Removing a recipe leaves
the recognized equation intact and retains ordered execution. These are
analysis views and compiler choices, not new authoritative expressions.

Candidate checking reconstructs the source and reads the actual emitted
instructions. It shares nominal types, admitted scalar-law declarations and
the finite ABI, but receives no producer equation witness, selected recipe or
binding-emission plan. The dependency checks enforce that boundary for the
separate finite, nested-contraction, mathematical-lowering, helper-normalization,
algorithm and mathematical-comparison readers. This reduces accidental coupling;
it is not a proof of the native checker or of cryptographic security.
