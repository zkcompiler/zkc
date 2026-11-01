# Why compiler state and external contracts differ

The compiler needs SSA identity, native types, symbol lookup and analysis
invalidation. Its independent consumers need bounded, explicitly specified
data. Making either representation own both jobs introduces avoidable coupling.
The [compiler boundary guide](../compiler/serialization.md) states the resulting
ownership rules; the [contract register](../spec/contracts.md) lists the actual
external consumers.

MLIR bytecode is a useful encoding of MLIR, including types, attributes,
properties and resources. Its stable container does not make evolving dialect
semantics stable. Upstream provides optional custom dialect codecs and version
hooks, rather than requiring another generic serialization framework.
See [MLIR bytecode](https://mlir.llvm.org/docs/BytecodeFormat/).

StableHLO makes long-lived compatibility an explicit architectural commitment:
VHLO retains versioned definitions and provides conversions to current
StableHLO. zkc has not made that external IR compatibility promise. Introducing
an equivalent layer now would create an additional semantic owner without a
consumer requirement. See [VHLO](https://openxla.org/stablehlo/vhlo).

IREE uses MLIR compilation checkpoints and a separate runtime VM artifact.
CIRCT imports external annotations into native attributes, and transformations
consume them or turn them into IR. These are useful precedents for keeping a
genuine external contract while making compiler work native. See
[IREE compiler tooling](https://iree.dev/developers/general/developer-tips/) and
[CIRCT annotations](https://circt.llvm.org/docs/Dialects/FIRRTL/FIRRTLAnnotations/).

For zkc, replacing every format with bytecode would require runtime and formal
consumers to understand compiler dialects and their evolution. Keeping JSON as
an internal program would instead duplicate SSA, types and schema ownership.
Wrapping positional JSON in a C++ class would retain that duplication. Native
views of actual operations and explicit boundary codecs avoid both costs.

Independent validation means independently interpreting the actual candidate
against its source and requirements. It does not require serializing an
internal proposal and parsing those same bytes to call the checker. External
record readers still need strict bounds, complete field checks and their own
negative tests. The remaining cost is intentional: each independent contract
has a codec, specification and consumer coverage, while native analysis keeps
one program owner.
