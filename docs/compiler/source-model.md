# Typed protocol source model

The compiler uses an owned C++ common source model. Admission, generic
elaboration, inspection, construction, site resolution and MLIR import/export
operate on named records and instruction variants. The frontend additionally
retains a [source-language analysis](frontend.md), including distinctions
such as nominal record identity that common PIR erases. JSON is
an interchange and identity encoding, not the representation those algorithms
navigate.

The source model retains protocol semantics across compilation stages. It is
not another protocol abstraction level or a final DSL.

## Architecture

```text
.pir -> syntax -> retained analysis -> common lowering-+
programmatic C++ records -----------------------------+-> owned source model
portable source JSON -> decode ----------------------+          |
                                              immutable Document + origins
                                                                |
                                              common checks / specialization
                                                                |
                                              construction / MLIR / lowering
                                                                |
                                              export / independent checks
                                                                |
                                              Rust artifacts and execution
```

Tokens handle comments, punctuation and pre-admission formatting. The source
model describes declarations and structured bodies, including unresolved names
and open requirements. MLIR owns mutable compiler graphs, analyses and lowering.
Rust owns product/artifact tooling, runtime resources and backend integration.
Lean retains independent meanings, checks and reference execution. There is no
C++/Rust exchange inside an analysis loop.

The current parser stays in C++ beside its consumers. A future Rust or Python
frontend can submit the same contract through a codec or future coarse interface;
it need not share C++ pointers. The maintained authoring syntax has private C++ records in
`lib/Frontend/Syntax/Tree.h`. `Frontend/Analysis.h` exposes a separate immutable resolved
snapshot with scoped IDs, nominal types, products, lexical bindings and
specialization origins. The internal model owns no parser tree. Checked body
plans refer to callable declarations directly; emission does not resolve those
names a second time. Its checker
retains source distinctions before common lowering erases them. Tooling queries
that snapshot without reconstructing source types from flat PIR. No Rust
frontend, FFI builder, package system or incremental editor database is implemented.

## Representation and ownership

| API | Responsibility |
|---|---|
| [Source/Model.h](../../compiler/include/zkc/Source/Model.h) | Owned declarations, parameters, bindings, requirements and recursive instruction variants |
| [Source/Document.h](../../compiler/include/zkc/Source/Document.h) | Immutable shared snapshot, spelling, filename and validated diagnostic spans |
| [Source/Codec.h](../../compiler/include/zkc/Source/Codec.h) | Structural checks, portable encoding/decoding and optional encoding-coordinate maps |
| [Frontend/Input.h](../../compiler/include/zkc/Frontend/Input.h) | Immutable text and filename snapshot |
| [Frontend/Compile.h](../../compiler/include/zkc/Frontend/Compile.h) | Lower a checked module; independent PIR admission remains required |
| [Frontend/Analysis.h](../../compiler/include/zkc/Frontend/Analysis.h) | Retained source identities, types, uses, diagnostics and checked lowering plans |
| [Frontend/Protocol.h](../../compiler/include/zkc/Frontend/Protocol.h) | Text parsing, checking, printing and token-preserving formatting |
| [Protocol/Instantiation.h](../../compiler/include/zkc/Protocol/Instantiation.h) | Generic checks, source-preserving preparation and shared specialization |
| [Protocol/Admission.h](../../compiler/include/zkc/Protocol/Admission.h) | Common and participant semantic admission |
| [Protocol/Construction.h](../../compiler/include/zkc/Protocol/Construction.h) | Construction from typed common source and a typed descriptor |
| [Contracts/Kernels.h](../../compiler/include/zkc/Contracts/Kernels.h) | Installed kernel shapes and static parameter checks |
| [Contracts/Bindings.h](../../compiler/include/zkc/Contracts/Bindings.h) | MLIR-free nominal types and contract application checking |
| [Source/Snapshot.h](../../compiler/include/zkc/Source/Snapshot.h) | Checked exact portable-source identity |
| [Dialect/Bindings.h](../../compiler/include/zkc/Dialect/Bindings.h) | MLIR type encoding and binding adapters |
| [Translation/Protocol.h](../../compiler/include/zkc/Translation/Protocol.h) | MLIR import and checked export |
| [Transforms/Protocol.h](../../compiler/include/zkc/Transforms/Protocol.h) | Participant projection, physical planning and storage insertion |

`Module` contains functions, protocols, instances, entries, operation bindings,
generic definitions and configurations. `Participants` is a distinct root with
a logical or physical stage. `Construction` is a descriptor. Sharing instruction
structures does not merge these semantic responsibilities.

Instance parameter bindings are typed `ParameterBinding` values: a canonical
natural string or `FamilyIngress`. An ingress has a ceiling and one selector
per actual role, with an ordered list of entry-port arguments. The local selector
returns an index. This binding retains actual input provenance through MLIR;
it is not a string-encoded configuration language or a new protocol-specific
operation. [Interactive execution](interactive-execution.md#input-selected-families)
states its admission and execution boundary.

`Instruction` distinguishes operation, local call, algorithm application, protocol call, message,
send, receive, loop, return, yield, stop, incomplete execution and physical-only
local storage release. `Release` carries ordered value names with no site; common
and logical source reject it. Operations
carry a callee, static arguments, attributes, inputs and outputs. Algorithm
applications carry a callee, ordered static arguments, inputs and outputs; their
static arguments are eliminated by specialization, before MLIR admission. New installed
algebraic or cryptographic contracts use this open case; a protocol family needs
no dedicated AST class. New control semantics require a model/checker extension.

Common types and static terms use explicit constructor/domain spellings. Names
and requirements still need common admission, especially for JSON and builder
inputs. Unresolved authoring calls and type expressions stay in the syntax AST;
resolved authored signatures and uses stay in the frontend analysis. Ordered assignments preserve duplicates until checking. Typed C++ fields prevent wrong field access;
they do not prove resolution, semantic typing, stage legality, resource safety
or security. The frontend reconstructs bounded static arguments; the existing requirement
engine checks capability entailment. Neither is a global solver or backend search.

A `Document` owns records and spelling. Copies share immutable storage; borrowed
references live while a copy survives. Transforms produce owned results and leave
inputs intact. Current consumers need neither arenas nor persistent node IDs.
The `library` flag retains an explicitly empty library envelope for exact encoding;
it introduces no new protocol property.

`source::OperationBinding` combines a symbol and diagnostic origin with a
`BindingApplication`: contract, static arguments and optional implementation.
Resolving that application produces a `BoundOperation` with checked input/output
types, independent of source provenance or MLIR. The dialect adapter selects the
registered operation separately. Internal algorithms do
not retain JSON overloads of typed source APIs. Portable codecs, certificates
and independently read artifacts retain their own encoding boundaries.

## Using the model

Text authors continue to use the [readable notation](../language/reference.md).
Programmatic authors build the same records and call the same checkers:

```cpp
using namespace zkc;
source::Module module;
module.bindings.push_back({{}, "both", "bool.and", {}, ""});
source::Function function;
function.name = "Both";
function.arguments = {{"a", "bool"}, {"b", "bool"}};
function.results = {"bool"};
function.origin = source::LogicalOrigin{"Both", {}};
source::Instruction operation;
operation.site = "join";
operation.value = source::Operation{"both", {}, {}, {"a", "b"}, {"c"}};
source::Instruction result;
result.value = source::Return{{"c"}};
function.body = source::Body{operation, result};
module.functions.push_back(std::move(function));
source::Document document(std::move(module));
if (auto error = frontend::checkProtocolDocument(document))
  return error;
```

This defines a reusable function, not a protocol entry. The
[source test](../../compiler/test/source.cpp) independently builds a whole
Alice/Bob protocol using a generic group operation, a boolean function and a
message. It compares separately written `.pir` through checking, specialization
and print/read, and exercises failures and ownership.

`checkProtocolSyntax` checks complete text syntax without resolution.
`inspectProtocolSyntax` and `protocol-parse` emit tagged syntax inspection, not
portable common JSON. `parseProtocolDocument` parses and elaborates text into
explicit common records; it does not establish semantic admission. JSON input
decodes directly into the existing model, bypassing the private syntax AST.
`checkProtocolDocument` checks common/generic source. `prepareLibrary` preserves
authored configuration names for construction; `elaborateLibrary` shares
instantiated bodies. Import checks the result before creating MLIR.

`construct` returns an owned, verified MLIR module alongside its portable
certificate. The caller's `MLIRContext` must outlive the module. A caller needing
IR uses that module directly; certificate consumers use the encoded result.
Availability and exact resource-origin analyses remain distinct private
algorithms sharing one construction invocation and work budget.

`encode` requires successful `checkStructure` on the unchanged enclosing value.
On that domain, decode-after-encode preserves fields except diagnostic origins.
Semantic and typed hashing entry points validate their inputs. The low-level
encoder is not a checked authoring API. Its limit counts compact portable bytes,
not C++ allocation size; semantic admission imposes additional bounds.

## Provenance, identity and verification

A node may carry an origin span in one document. `Document::span` accepts members
of that snapshot; a copied node is not a member just because its span fits.
Transforms copy span values for MLIR diagnostics. Elaboration separately maps
generated failures to live original nodes, registering addresses after container
growth finishes. JSON-tree resemblance does not establish this correspondence.
Decoder failures carry an optional source span directly, without exposing a
borrowed JSON subtree to the frontend for reverse lookup.

Origins never enter encoding, source hashes, construction identity, transcripts
or proof bytes. Some construction errors identify a protocol/function context
rather than an exact descriptor token. Multi-file expansion origins remain future work. Frontend analysis supports
bounded module-declaration recovery; recovered errors prevent accepted emission. Encoding coordinates used by inspection are not
persistent compiler IDs. The nested library encoding has only one semantic root.

The registered protocol module verifier checks the stage-specific source contract
through typed export/admission. Operation-local MLIR verification alone does not
establish ownership/resource rules. A pass may mutate internally before reaching
its verified output. A future multi-pass intermediate form must define its legal
stage and checks; disabling the current verifier is insufficient. Export remains
an explicit boundary. The broader [selective lowering design](lowering.md) is not
claimed for every current container.

Closed local [algorithm composition](local-composition.md) now adds
`AlgorithmCall`/`apply`, retained `func.call` common IR and a bounded native
expansion pass. Its [accounting and occurrence contract](../spec/profiles/compiler/local-algorithms.md)
defines the executable boundary. Participant export still rejects residual
applications; independent Lean consumers derive their own expansion.

## Scope and next work

The rewrite covers protocol source and construction consumers under `compiler/`.
The older direct table/region carrier, runtime inputs, manifests and certificates
retain their own representations. Rust and Lean readers remain independent.

Clients include polynomial/PCS composition, DLEQ/group arguments, multiple roles,
nested/zero loops, generics and external declarations. ExecutionProof and
correlated-service declarations remain declaration-only. General branching,
higher-order modules and a complete zkVM
implementation are not added.

The frontend now has scoped source identifiers and immutable semantic queries.
Incremental query invalidation, package identity and new intermediate MLIR
containers need their own concrete consumers and contracts; this common carrier
does not preselect them.
