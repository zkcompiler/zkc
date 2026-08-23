# Long-lived IR contracts and difficult-to-reverse decisions

> **Document kind:** Temporary comparative research dossier
> **Document state:** First research pass
> **Cases:** LLVM IR/bitcode, WebAssembly Core/Component Model, SPIR-V
> **Authority:** None. Documented history and PIR inferences are kept distinct.
> **Disposition:** Absorb reviewed rationale into Stage 1 synthesis and durable
> decisions, then delete this page.

## 1. Scope

This dossier studies evolution after an IR has acquired an installed base. It
asks which early choices became compatibility obligations, how text and binary
contracts differ, how environment assumptions enter meaning, and which later
layers were needed for composition.

SPIR-V is included only for the long-lived environment and repair pressure.
Its portable-format architecture is covered in the
[portable IR dossier](portable-ir-contracts.md).

## 2. LLVM IR and bitcode

### 2.1 Current semantics versus readable historical bytes

**Source fact.** LLVM makes no general backward-compatibility promise for
textual IR, while current readers are expected to read bitcode produced by old
LLVM releases. Compatibility is commonly implemented by translating historical
bitcode into the current IR model. See the
[IR compatibility policy](https://llvm.org/docs/DeveloperPolicy.html#ir-backwards-compatibility)
and [bitcode format](https://llvm.org/docs/BitCodeFormat.html).

**Design inference.** Byte readability does not require preserving every old
in-memory semantic representation. A future PIR compatibility promise should
be specified as an explicit function:

```text
historical bytes
  -> historical interpretation
  -> checked migration
  -> current semantic subject
```

**PIR transfer.** Migration must not silently preserve `ProtocolId`. It either
produces a new identity with a migration relation or establishes the stronger
claim that both encodings denote the same canonical subject.

### 2.2 Undefined behavior and partiality

**Source fact.** LLVM distinguishes immediate undefined behavior from deferred
forms including poison, and uses `freeze` to obtain one stable nondeterministic
choice. See [LLVM undefined behavior](https://llvm.org/docs/UndefinedBehavior.html).

**PIR transfer.** General-purpose undefined behavior is a poor default for
Protocol semantics because it can make a claimed security refinement vacuous.
PIR should enumerate and type:

- malformed or inadmissible artifacts;
- unresolved dependencies;
- unsupported profiles;
- conditional obligations;
- explicit randomness or nondeterminism;
- malformed proof and named rejection;
- supplier or operational failure; and
- intentionally unspecified realization properties.

None authorizes arbitrary Protocol behavior.

### 2.3 Target and environment pressure

**Source fact.** LLVM modules can contain a target triple and data layout. The
layout defines pointer representations, widths, alignment, and other facts that
must match later code generation. See
[target triple](https://llvm.org/docs/LangRef.html#target-triple) and
[data layout](https://llvm.org/docs/LangRef.html#data-layout).

**PIR transfer.** Portability never means absence of assumptions. Stage 1 must
separate:

- a **semantic environment**, required to interpret field, group, hash,
  transcript, codec, contract, and sampling meaning; and
- a **realization profile**, constraining where or how an already meaningful
  Protocol can be implemented.

A realization profile may refuse a Protocol; it must not reinterpret it.

### 2.4 Typed pointers

**Historical report.** LLVM's
[opaque-pointer migration](https://llvm.org/docs/OpaquePointers.html) explains
that embedding pointee types into every pointer produced redundant casts,
complicated analyses, and became expensive ecosystem ABI despite weak semantic
value. Removal required a multi-release migration.

**PIR transfer.** A field placed pervasively in types or operations will become
compatibility surface. Backend representation, display names, debug state, and
realization-specific data should not enter canonical Protocol merely because
they are locally convenient.

**Analogy limit.** The history establishes migration cost, not that opaque
pointers were a feasible original design under all of LLVM's early goals.

### 2.5 Convergent operations

**Historical report.** LLVM's original `convergent` marker could not precisely
state transformation constraints. The later design introduced explicit
convergence-control tokens and token-producing intrinsics. See
[convergent operations](https://llvm.org/docs/ConvergentOperations.html).

**PIR transfer.** A boolean “ordered” or “transcript-sensitive” attribute is
unlikely to capture shared challenge context, exact prefixes, framing, and
legal commutation. These dependencies need explicit structure plus whole-
Protocol laws.

### 2.6 Composition

**Source fact.** LLVM composition is governed by symbols, linkage, and module
flags with merge policies. See
[module structure](https://llvm.org/docs/LangRef.html#module-structure) and
[module flags](https://llvm.org/docs/LangRef.html#module-flags-metadata).

**Analogy limit.** Protocol composition cannot inherit generic symbol conflict
resolution. Combining subjects changes transcript domains, challenge
dependence, public interfaces, dependency closure, assumptions, and property
bounds.

## 3. WebAssembly Core and Component Model

### 3.1 Abstract syntax, validation, and encodings

**Source fact.** WebAssembly Core separately defines abstract syntax, binary
encoding, validation, execution, and text format. Decoding yields an abstract
module that is then validated and instantiated. See the
[Core introduction](https://webassembly.github.io/spec/core/intro/introduction.html)
and [overview](https://webassembly.github.io/spec/core/intro/overview.html).

**Source fact.** Valid binary encodings of some abstract values need not be
unique, and text includes symbolic identifiers and syntactic sugar. See
[binary conventions](https://webassembly.github.io/spec/core/binary/conventions.html)
and [text conventions](https://webassembly.github.io/spec/core/text/conventions.html).

**PIR transfer.** Neither MLIR text nor generic bytecode is automatically a
semantic canonical form. Producer labels, source locations, incidental order,
and equivalent carrier encodings must either be excluded from identity and
unread by normative consumers or promoted into the semantic subject.

### 3.2 Bounded nondeterminism

**Source fact.** WebAssembly validation has a declarative system and a sound,
complete algorithm for its stated rules. Its official nondeterminism note
enumerates bounded sources such as host calls, resource exhaustion, shared-
memory interleaving, NaN payloads, and relaxed SIMD rather than importing
arbitrary source-language undefined behavior. See the
[validation algorithm](https://webassembly.github.io/spec/core/appendix/algorithm.html)
and [nondeterminism note](https://github.com/WebAssembly/design/blob/main/Nondeterminism.md).

**PIR transfer.** Explicitly enumerated partiality and randomness is a better
model for PIR. Protocol randomness additionally affects distributions and
security theorems and therefore needs typed occurrences, provenance, and
sampling contracts.

### 3.3 Version axes and non-semantic sections

**Source fact.** Core specification evolution is distinct from the binary
format version, which remains `1` for compatible feature additions. Custom
sections are semantically ignored; malformed custom payloads do not invalidate
the core module. See the
[module binary format](https://webassembly.github.io/spec/core/binary/modules.html).

**PIR transfer.** A strict test for non-semantic metadata is:

> Every normative transition and consumer can remove or ignore it without
> changing identity, admission, projection, judgment, or realization meaning.

If OIR projection, relation wiring, composition, or proof generation reads a
field, it is not non-semantic merely because the seal encoder ignored it.

### 3.4 Explicit host boundary

**Source fact.** Core modules have no ambient operating-system API; functions,
memories, tables, and globals are explicitly imported from the embedder. See
[WebAssembly portability](https://github.com/WebAssembly/design/blob/main/Portability.md).

**PIR transfer.** Construction may use process-local registries, but a sealed
or admitted Protocol must identify every dependency needed for meaning. Ambient
lookup is acceptable only for non-semantic realization supply with an explicit
binding contract.

### 3.5 Component Model as an outer layer

**Source fact.** Core function boundaries expose low-level machine values. The
Component Model adds typed language-independent interfaces, components, and
canonical lift/lower operations while preserving Core modules. See the
[Component Model goals](https://github.com/WebAssembly/component-model/blob/main/design/high-level/Goals.md)
and [MVP explainer](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md).

**Design inference.** A compact core can be the right early boundary yet remain
insufficient for rich composition. The compatible response can be an outer
interface layer rather than mutation of the core artifact.

**PIR transfer.** Protocol interfaces should become explicit before external
composition depends on incidental symbols or labels. This does not imply
copying WIT or putting every future composition feature inside the first
Protocol kernel.

**Analogy limit.** The Component Model's cross-language memory and value ABI is
not a protocol transcript or security-composition algebra.

## 4. SPIR-V evolution pressure

### 4.1 Version, revision, capability, and environment

**Source fact.** SPIR-V distinguishes encoded language version, unencoded
specification revision, capabilities, extensions, extended instruction sets,
and client execution-environment rules. See the
[unified specification](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html).

**Design inference.** These axes support a large deployed ecosystem but create
a validation product over versions, features, extensions, and client
environments. zkc should introduce only the axes that correspond to distinct
authority, identity, or compatibility needs.

### 4.2 Late semantic refinement

**Historical report.** The revision history records refinements to validity,
undefined values, poison, and stable values. The Vulkan memory-model extension
introduced more precise availability and visibility semantics while replacing
older decoration-based mechanisms. See
[SPV_KHR_vulkan_memory_model](https://github.khronos.org/SPIRV-Registry/extensions/KHR/SPV_KHR_vulkan_memory_model.html).

**PIR transfer.** Ordering, visibility, partiality, and dynamic dependence are
costly to retrofit. PIR's analogous transcript observation and challenge
dependence need explicit semantics before aggressive rewrite contracts are
frozen.

### 4.3 Stable names and aliases

**Historical report.** Standardized promotion and renaming sometimes retained
old token aliases for binary compatibility.

**PIR transfer.** Human-readable names should not receive semantic authority
unless the project is prepared to preserve them as long-lived ABI. Semantic
identifiers and display labels require separate namespaces.

## 5. Cross-case conclusions

| Concern | LLVM | WebAssembly | SPIR-V | Stage 1 implication |
|---|---|---|---|---|
| Old artifacts | Reader migrates bitcode into current IR | Stable envelope with proposal evolution | Unified binary plus versions/extensions | Specify migration as a transition, not an implicit promise |
| Text/binary/meaning | Text unstable; bitcode readable | Both decode to abstract syntax; bytes can be noncanonical | Binary normative but not semantic content identity | Keep `ProtocolId` independent of generic carrier bytes |
| Partiality | Broad UB, poison, freeze | Bounded traps/nondeterminism | Validity distinct from UB and poison | Use explicit refusal, randomness, and failure classes |
| Environment | Triple and data layout | Explicit host imports | Capabilities plus client environment | Separate semantic regime from realization profile |
| Difficult repair | Typed pointers and convergence | Rich composition outside Core | Memory, partiality, and alias evolution | Make effects, interfaces, and evolution axes explicit early |
| Composition | Linkage and merge policies | New outer component layer | Limited linkage | Define protocol composition independently |

## 6. Stage 1 hypotheses produced by this dossier

1. The same canonical operation or contract identifier must never acquire a
   new meaning. Semantic change requires a new identifier or semantic regime.
2. Protocol language, canonical identity encoding, carrier schema, producer
   release, and realization profile require separate conceptual version axes.
3. Canonical PIR should not have a general-purpose undefined-behavior escape
   hatch.
4. Transcript and challenge dependence must be explicit structural and
   semantic relationships, not a side attribute.
5. Protocol interface and composition authority should be designed before
   labels become accidental external ABI.
6. Historical-byte support, if introduced, should translate into a current
   subject through an explicit checked transition.
7. A small semantic kernel and a later outer compatibility or composition
   layer are compatible design choices; the first need not predict every
   future ecosystem feature.

These histories support careful separation. They do not independently select
MLIR, a wire schema, or a particular Protocol factorization.

