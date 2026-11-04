# Compiler state and serialized contracts

MLIR owns compiler programs. Operations, SSA values, types, attributes, symbols
and regions carry their meaning. Passes transform that IR; analyses borrow it
for a bounded lifetime. A JSON report or an exported semantic model must not
become the program that a native compiler analysis interprets.

Serialization has a different responsibility: carrying data across a process,
storage, deployment or independent interpretation boundary. A format is justified
by that consumer and its admission rules, not by the name of a compiler pass.

| Data | Native owner | Serialized boundary |
|---|---|---|
| Compiler program | MLIR module and its context | MLIR assembly or bytecode |
| Authenticated original | Immutable admitted module, exact supplied bytes and source association | Canonical original and interface contract |
| Analysis facts | Bounded native view of the actual operations | Optional diagnostic or correspondence report |
| Checked transformation | Retained source and candidate, independently checked against each other | Application or realization record for independent consumers |
| Executable program | Portable program model and independent runtime admission | `zkc.program/0` and its typed parameter contracts |
| Logical interpretation | Actual source operations and nominal catalog identities | Structured source and logical-type contracts |
| Written source | Frontend checked program, declarations and spans | Source AST, bindings and correspondence publication |

The [contract register](../spec/contracts.md) owns the inventory and consumer
status. Different external contracts are not competing compiler IRs. Their
encoders project from their owning representation; native analyses must not
recover their input by exporting and reparsing those projections.

## Lifetime and authority

An admitted owner must not expose a mutable success handle. Consumers borrow an
immutable view for one analysis, or receive an independent clone for rewriting.
MLIR `IRMapping` transports associations to a clone. Analysis results become
invalid when their subject changes; pass analyses follow MLIR's invalidation
rules. A cache key or a report does not authorize reuse after mutation.

Actual-program validation and wire validation are separate checks. An internal
producer supplies typed proposals to an independent reader of source and
candidate operations. An external reader first validates its bounded encoding,
then invokes the same actual-program check. The native reader must not call the
producer to establish correctness. Checked occurrence and query-block facts feed
request-count and proof-origin analysis directly. Published JSON data owns its
strings and keys before leaving the source/context lifetime; copying an LLVM
JSON value alone does not detach borrowed `StringRef` storage. Tests must alter both records and actual
programs, including well-formed programs with a different meaning.

Retaining an original has a cost: its context and module stay alive beside the
authenticated byte buffer, and independent analyses use temporary clones. The
frontend transfers its emitted module directly into admission. Canonical
printing records operation-name ranges in those exact bytes; it does not
reparse the printout to recover the program. Imported originals are parsed once
and must reproduce the supplied canonical bytes. Both paths retain the same
independent source comparison and immutable ownership rules.

Native source admission checks the complete profile, declarations, references
and closed control structure before constructing a borrowed operation index.
Its shared work allowance bounds expanded uses and retained metadata. The index
stores actual operations, bindings and regions; it does not construct JSON
descriptors or format-local synthetic computations. Coordinate construction
keeps prepend offsets instead of repeatedly shifting every earlier binding.

Structured publication is an explicit projection from that admitted view. It
enforces its own text, table, nesting and encoded-size bounds and may refuse an
otherwise admitted native source. Per-operation descriptors are constructed
only for reports that request them. Native facts cannot depend on publication
succeeding. This separation does not establish a net memory or speed improvement.
The owner remains local to a compilation; no global mutable IR cache is
introduced.

Fresh target compilation admits the authenticated original bytes into an isolated
compilation context. Target installations, diagnostics and rewriting then belong
to that compilation; it does not reimport a generated semantic report. Read-only
inspection of a checked original uses its retained module through a clone. If a
caller requests tighter limits than the original admission established, inspection
must re-admit under those limits instead of reusing the weaker judgment.

## Encoding and identity

MLIR assembly and bytecode encode the same compiler IR. Bytecode is appropriate
for compiler checkpoints and exchange between compatible compiler tools. Its
container version does not promise compatibility of changing dialect semantics.
Use upstream parsing, printing and resource management; introduce custom dialect
bytecode encodings only for a demonstrated storage or performance need.

An encoding change does not preserve an artifact's digest. Authentication binds
the exact bytes required by the owning contract. A bytecode location can retain
a source location, but it is not a textual offset in the supplied bytecode file.
Source association must keep that distinction explicit.

The Rust runtime and independent semantic consumers do not need to depend on
MLIR to read their contracts. Numerical plans remain typed MLIR attributes while
inside the compiler, and portable runtime parameters at deployment. Their
separate expression, lane and scratch semantics justify that boundary.

All zkc-owned formats remain at version `0` until external stabilization.
Changes update the specification, producer, readers and fixtures together; no
compatibility route is retained. See the [design rationale](../rationale/serialization.md)
for the alternatives and their costs.
