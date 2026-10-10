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
