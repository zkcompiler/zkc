# Portable semantic and interchange IR contracts

> **Document kind:** Temporary comparative research dossier
> **Document state:** First research pass
> **Cases:** StableHLO/VHLO, SPIR-V, ONNX
> **Authority:** None. Source facts describe the named systems; PIR transfers
> are hypotheses for Stage 1 and do not select an architecture.
> **Disposition:** Absorb reviewed cross-case rationale into the Stage 1
> synthesis and durable decisions, then delete this page.

## 1. Scope

This dossier asks how three externally consumed IRs divide:

```text
semantic language
working compiler representation
portable artifact
validation environment
compatibility mechanism
extension authority
```

It focuses on the location and cost of a stable boundary. It does not use
tensor, shader, or graph equivalence as a substitute for protocol semantics.

## 2. StableHLO and VHLO

### 2.1 Contract shape

**Source fact.** StableHLO specifies a high-level tensor program independently
of its surface syntax. Its specification defines operations, constraints,
types, effects, execution, and dataflow-constrained order. Side effects are
ordered through tokens. See the
[StableHLO specification](https://openxla.org/stablehlo/spec).

**Source fact.** Its current working and compatibility forms are distinct:

```text
CHLO or mixed producer MLIR
        -> legalized current StableHLO
        -> versioned VHLO
        -> MLIR bytecode artifact
```

StableHLO is the current compiler-facing dialect. VHLO is an add-only,
versioned compatibility dialect used by serialization. CHLO and other mixed
dialects must be legalized before the compatibility contract applies. See
[the VHLO dialect](https://openxla.org/stablehlo/vhlo) and
[dialect interoperability](https://openxla.org/stablehlo/spec#dialect-interop).

**Design inference.** A portable MLIR artifact is not defined by the fact that
it uses MLIR. It needs a closed dialect and feature profile plus an explicit
serialization entry point.

### 2.2 Validation and correspondence

**Source fact.** StableHLO separately tracks specification, verifier, type
inference, pretty-printer, interpreter, and test status. Not every operation is
fully inferable or interpreted. See the
[project status](https://openxla.org/stablehlo/status),
[specification checklist](https://openxla.org/stablehlo/spec_checklist), and
[interpreter status](https://openxla.org/stablehlo/interpreter_status).

**PIR transfer.** A future PIR conformance matrix should likewise track
operation semantics, local verification, whole-Protocol sealing, canonical
identity encoding, carrier round trip, consumer projections, and refusal
tests separately. One implemented checker cannot stand for all of them.

### 2.3 Compatibility and debt

**Source fact.** StableHLO builds its own compatibility contract over MLIR
bytecode. Individual VHLO operations, types, and attributes are versioned; an
incompatible semantic change introduces a new versioned element. Serialization
can target an older version and refuse when downgrade is impossible. The
compatibility promises apply to artifacts created through the compatibility
APIs, not arbitrary StableHLO text or raw bytecode. See
[StableHLO bytecode](https://github.com/openxla/stablehlo/blob/main/docs/bytecode.md),
[compatibility](https://github.com/openxla/stablehlo/blob/main/docs/compatibility.md),
and the [compatibility RFC](https://github.com/openxla/stablehlo/blob/main/rfcs/20230623-compatibility.md).

**Historical report.** StableHLO inherited behavior from MHLO and XLA whose
semantics were not always fully documented. Its status and deprecation records
show later specification archaeology and removal work. The
[VHLO checklist](https://openxla.org/stablehlo/vhlo_checklist) also makes the
permanent conversion and testing surface visible.

**Design inference.** A compatibility dialect can successfully quarantine
history from the optimizing representation, but it is an indefinite product
obligation. PIR should not introduce that obligation before it can name the
artifact lifetime and independent consumers that justify it.

### 2.4 Extension boundaries

**Source fact.** StableHLO distinguishes decomposable `composite` operations,
higher-level CHLO operations that must be legalized, and implementation-defined
`custom_call` operations. Its specification describes inherited `custom_call`
metadata as organically accumulated and not uniformly structured.

**PIR transfer.** PIR should distinguish at least:

1. canonical semantic operations;
2. authoring conveniences that must lower away;
3. semantics-defining decompositions;
4. exact external semantic dependencies;
5. realization hooks;
6. non-semantic annotations; and
7. unsupported experimental content.

One generic custom operation category would blur identity, portability, and
checker authority.

### 2.5 Analogy limit

StableHLO normally judges tensor-computation behavior. PIR additionally
exposes transcript distributions, challenges, asymmetric endpoints,
assumptions, and conditional security judgments. VHLO informs representation
and compatibility design, not the preservation relation for a Protocol
transform.

## 3. SPIR-V

### 3.1 Contract shape

**Source fact.** SPIR-V is a standard binary intermediate language. A module
contains functions, control flow, SSA values, memory operations, entry points,
interfaces, capabilities, and execution modes. Its meaning and validity are
the combination of the universal specification and a client execution
environment such as Vulkan or OpenCL. See the
[SPIR-V unified specification](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html).

**Source fact.** The binary word stream is the normative interchange form;
assembly is a tooling representation. The same binary form is also transformed
by tools. See
[SPIR-V physical layout](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html#_physical_layout_of_a_spir_v_module_and_instruction).

**Design inference.** SPIR-V demonstrates the benefit and cost of making the
working binary itself the public contract. PIR should decide explicitly
whether its sealed compiler form and external portable form are the same
artifact instead of arriving there accidentally.

### 3.2 Layered validity

**Source fact.** SPIR-V validation combines binary and logical rules,
capability and extension rules, and client-environment restrictions. Static
validity is distinct from defined execution behavior. The official
[SPIRV-Tools README](https://github.com/KhronosGroup/SPIRV-Tools/blob/main/README.md)
also states that validator coverage is incomplete.

**PIR transfer.** `ValidPIR` would be too coarse. The architecture needs named
judgments such as decoding, local well-formedness, closure, identity,
environment-relative admission, projectability, qualified analysis, and
realizability. A positive result at one layer cannot imply the next.

### 3.3 Environment, capabilities, and extensions

**Source fact.** A module declares capabilities and extensions; client APIs add
admissibility rules. SPIR-V's modeless design principle aims to preserve the
meaning of a spelling rather than reinterpret it under a capability. It also
has registered extensions, extended instruction sets, and explicitly
non-semantic instruction sets. See
[extendability and design principles](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html#_extendability).

**PIR transfer.** A PIR capability may declare required constructs, but must
not change the meaning of an existing canonical operation. Unknown semantic
extensions must fail closed. Only material structurally classified as
non-semantic may be ignored without changing `ProtocolId` or any normative
consumer result.

**Historical report.** Extension promotion and renaming accumulated binary
aliases. The machine-readable grammar later gained explicit alias support to
reduce duplicated entries and tooling complexity. See the
[SPIR-V machine-readable grammar](https://registry.khronos.org/SPIR-V/specs/unified1/MachineReadableGrammar.html).

**Design inference.** Once tokens escape into deployed artifacts, cleanup must
preserve their numeric history. PIR should not freeze vendor-style semantic
opcode space before it has a closed extension-authority model.

### 3.4 Identity and transformation

**Source fact.** SPIR-V does not define a content-addressed semantic identity.
IDs, generator metadata, debug instructions, and permitted ordering choices
can vary. SPIRV-Tools provides normalization and optimization, but normally
relies on pass implementations, validation, and testing rather than portable
preservation certificates.

**PIR transfer.** A validated carrier is not a canonical identity preimage.
PIR requires its own quotient over identifiers, ordering, metadata, semantic
dependencies, and interface information. Its transforms also need stronger
claim classes than general optimizer validity.

### 3.5 Analogy limit

SPIR-V is an executable interface and deliberately admits environment-relative
restrictions and some undefined behavior. PIR's transcript order, dependency
closure, and conditional security arguments require stricter authority and
preservation contracts. SPIR-V informs capabilities and environment modeling;
it does not define Protocol admission.

## 4. ONNX

### 4.1 Contract shape

**Source fact.** ONNX defines an extensible computation graph and operator
contracts. The semantic specification is normative while protobuf messages
define normative syntax. Implementations may use different in-memory forms for
optimization. See the [ONNX IR specification](https://onnx.ai/onnx/repo-docs/IR.html).

**Design inference.** ONNX is evidence that a portable artifact need not be the
optimizer's best mutable representation. It is not evidence that zkc needs a
portable Protocol schema immediately.

### 4.2 Version and dependency axes

**Source fact.** ONNX distinguishes IR version, operator-set version, and
model-owner version. Models import operator sets by domain and version; a
breaking operator change introduces a new schema version while older schemas
remain registered. See [ONNX versioning](https://onnx.ai/onnx/repo-docs/Versioning.html).

**Source fact.** Model-local functions can define portable decompositions while
a runtime substitutes an optimized implementation. The specification also
describes serialized operator-set documents but reports that known
implementations do not process them at runtime.

**PIR transfer.** Merely naming a domain and version does not make a semantic
environment closed. A sealed Protocol dependency must say whether it supplies
an identifier, canonical preimage, typed declaration, checker, theorem/rule
material, opaque citation, or realization implementation.

### 4.3 Validation and conversion limits

**Source fact.** ONNX has a graph checker and optional fuller checking through
shape inference. Shape inference is explicitly incomplete, and custom-domain
checking is configurable. See the
[checker API](https://onnx.ai/onnx/api/checker.html) and
[shape inference](https://onnx.ai/onnx/repo-docs/ShapeInference.html).

**Source fact.** Version conversion operates through registered adjacent
adapters and may refuse when support is missing; default support does not cover
all custom domains. See the
[version converter](https://onnx.ai/onnx/repo-docs/VersionConverter.html).

**PIR transfer.** A version integer does not imply convertibility. A PIR
migration must identify its source and successor and state the exact checked
correspondence; adapter existence alone cannot establish preservation of
transcript or security semantics.

### 4.4 Serialization closure

**Source fact.** Large ONNX tensors may reside in relative external files with
offset, length, and optional checksum metadata. See
[ONNX external data](https://onnx.ai/onnx/repo-docs/ExternalData.html).

**PIR transfer.** Protocol identity cannot rely on ambient paths or optional
integrity. Every meaning-bearing external resource needs explicit typed
closure, exact identity, and a defined binding time.

### 4.5 Analogy limit

ONNX primarily describes extensional graph computation and leaves optimization
and execution broad. PIR cannot adopt best-effort inference, optional extension
checking, or ambient registries for any dependency that affects transcript,
projection, or property judgments.

## 5. Cross-case pressure matrix

| Pressure | StableHLO/VHLO | SPIR-V | ONNX | Stage 1 pressure |
|---|---|---|---|---|
| Working versus portable form | Current dialect versus hidden compatibility dialect | One standard binary serves both | Serialized graph may differ from optimizer form | Name the exact stable artifact before selecting a mechanism |
| Compatibility | Explicit add-only representation and conversions | Versioned binary, extensions, aliases, environments | IR/opset/model versions and adapters | Compatibility is a product promise, not a parser feature |
| Validation | Spec, verifier, inference, interpreter tracked separately | Layered and environment-relative; tooling incomplete | Checker distinct from incomplete inference | Use an explicit judgment lattice and coverage matrix |
| Extensibility | Composite, CHLO, custom call | Capabilities, extensions, ext-inst, non-semantic sets | Domains, opsets, functions, custom ops | Classify extension authority and unknown behavior before seal |
| Identity | No semantic content ID | No semantic content ID | No semantic content ID | zkc must design content identity independently |
| Environment | Compatibility subset and consumers | Explicit client environment | Registry/runtime dependent | Seal or admit against an exact semantic regime |
| Transformation | Optimization plus compatibility conversion | Trusted tools plus validation | Primarily version adapters | Define Protocol-specific preservation claims |

## 6. Stage 1 hypotheses produced by this dossier

These remain open until cross-family synthesis:

1. **Closed sealed profile.** If MLIR remains the carrier, sealing must admit a
   closed dialect-and-feature profile, not arbitrary verified MLIR.
2. **Separate version axes.** Protocol language, canonical identity encoding,
   dialect schema, transport, dependency schemas, admission policy, and tool
   release are distinct even if v0 couples some of them deliberately.
3. **No premature compatibility dialect.** Preserve a fail-closed version hook
   now; introduce permanent migration machinery only when independent release
   cycles, long-lived external artifacts, or third-party consumers exist.
4. **Extension taxonomy before extension ecosystem.** Unknown meaning-bearing
   content fails closed; decomposable, external, opaque, target, and
   non-semantic categories receive different contracts.
5. **Identity is zkc-specific.** None of these systems supplies the canonical,
   dependency-closed, interface-aware content identity that Protocol needs.
6. **Transport conversion is not semantic preservation.** Any future migration
   produces a fresh identified subject unless a stronger explicit equivalence
   relation proves otherwise.

The dossier does **not** yet decide whether canonical PIR and optimizing PIR
are one dialect, two dialects, or one semantic model with several adapters.

