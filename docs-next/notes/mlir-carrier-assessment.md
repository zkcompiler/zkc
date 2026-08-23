# MLIR carrier assessment

> **Document kind:** Temporary design note
> **Document state:** Baseline assessment absorbed by Stage 1 decision
> **Provisional owner:** `project`
> **Authority:** None. This assessment records a design recommendation and
> reconsideration criteria; it does not select a dependency version or amend
> PIR, OIR, artifact, or versioning contracts.
> **Disposition:** Absorb the final boundary into project architecture and
> carrier specifications, preserve a decision if ratified, then delete this
> page.

> **Convergence notice — 2026-08-22:** The completed
> [Protocol IR architecture research](stage-1-ir/README.md) re-evaluated this
> recommendation against a broader comparative record. The selected durable
> [Protocol IR Architecture](../project/protocol-ir-architecture.md) retains
> MLIR as the v0 workbench and canonical structural carrier, adds a distinct
> small closed PIR level, and preserves language-independent semantics and
> identity. This page remains the prior focused assessment and source of
> reversal criteria.

## 1. Prior recommendation

**Keep MLIR as the structural carrier and compiler workbench for PIR and OIR.**
Do not make MLIR the semantic authority, stable identity format, proof object,
or required interface for every consumer.

This is a conditional architectural recommendation, not a claim that MLIR is
intrinsically the best representation for every part of zkc. It is the best
fit for the current combination of:

- a protocol representation with two coupled geometries;
- several abstraction levels and checked transformations;
- typed operations, regions, SSA values, and protected effects;
- parser, printer, verifier, diagnostic, pass, and rewrite infrastructure;
- substantial existing dialect and test investment; and
- a need to keep semantic identity separate from transport encoding.

The design should be reconsidered if zkc becomes primarily a stable artifact
exchange and independent-checking project with very little IR transformation.
No evidence currently justifies paying for a rewrite in anticipation of that
possibility.

## 2. Current role reconstructed from the repository

The current specification already states the right conceptual boundary:
[`carrier.md`](../../docs/spec/carrier.md) gives PIR and OIR an MLIR
representation, while [`versioning.md`](../../docs/spec/versioning.md) refuses
to make raw MLIR text or bytecode the durable semantic identity contract.

The implementation correspondence is extensive:

- [`PirOps.td`](../../include/zkc/Dialect/Pir/PirOps.td) represents Protocol
  sources, the transcript spine, claim values, reductions, terminals, routes,
  and sealed content;
- [`OirOps.td`](../../include/zkc/Dialect/Oir/OirOps.td) represents endpoint
  programs, protected effects, provenance, proof-stream operations, transcript
  operations, checks, and decisions;
- [`Passes.td`](../../include/zkc/Dialect/Pir/Transforms/Passes.td) defines the
  current seal, link, projection, and transformation work surfaces;
- [`Artifact.cpp`](../../lib/Artifact/Artifact.cpp) uses MLIR bytecode as a
  carrier while separately checking zkc artifact identity and admission; and
- [`SealedSoundnessView.h`](../../include/zkc/Soundness/SealedSoundnessView.h)
  already demonstrates the desirable escape hatch: analysis consumes an
  immutable, MLIR-free semantic view rather than retaining an MLIR object.

This is more than incidental syntax. Replacing MLIR would replace a mature
structural toolkit and a large amount of encoded invariants. It would not,
however, remove the need for zkc's own semantic checks, canonical encoding, or
authority model.

## 3. Why MLIR fits PIR and OIR

### 3.1 It represents the two Protocol geometries without conflating them

PIR uses block order and threaded tokens for transcript order, while SSA claim
values and their consumers represent linear claim flow. MLIR supplies both
structures natively without forcing them into one generic graph.

A custom AST could express the same facts, but zkc would have to build and
maintain traversal, use-def tracking, mutation discipline, diagnostics, and
verification infrastructure itself.

### 3.2 Dialects make abstraction boundaries explicit

PIR and OIR can have different operations, types, invariants, and legal
transformations while sharing infrastructure. This matches the semantic split:
PIR owns explicit Protocol content; OIR owns endpoint-observable behavior.

The dialect boundary also leaves room for an internal realization IR later if
real consumers require one. It does not require inventing that level now.

### 3.3 ODS and TableGen remove repetitive structural machinery

Operation definitions generate builders, accessors, parsing/printing support,
and parts of verification. Declarative types, properties, traits, and
interfaces make carrier shape reviewable in one place.

This benefit is structural only. A generated verifier can establish operand
types, region shape, or trait contracts; it does not establish seal admission,
property judgments, projection coverage, or backend conformance.

### 3.4 Effect resources protect endpoint ordering

OIR marks transcript, stream, public-binding, check, and decision behavior as
effects on a protected endpoint resource. Pure algebra can be transformed
without giving generic passes permission to reorder protocol-observable
effects.

This is a strong fit for a compiler IR. It is still a convention whose exact
preservation obligations belong to OIR semantics and pass admission, not a
blanket guarantee provided by MLIR.

### 3.5 Pass and rewrite infrastructure supports checked transformation

Pattern rewriting, pass pipelines, dialect conversion, analysis management,
and diagnostics provide a scalable workbench for linking, projection,
optimization, and future lowering. The infrastructure is especially valuable
when transformations preserve some semantic relation rather than merely
serializing an object.

zkc should continue to put authority in checked transition contracts. A pass
manager schedules transformations; it does not prove their semantic relation.

### 3.6 The surrounding testing and tooling ecosystem is already useful

Textual IR is convenient for focused examples and negative tests. `lit`,
FileCheck-style expectations, pass drivers, printers, and diagnostics make
structural regressions relatively cheap to localize. The readable form is a
development interface, not a promised interchange format.

## 4. Costs and risks

### 4.1 MLIR verification is not zkc semantic admission

The most important risk is false authority. `verify()` can succeed while
whole-Protocol closure, environment authentication, canonical identity,
property derivability, or projection coverage fails. Documentation and APIs
must qualify the result as carrier or local structural validity.

### 4.2 Mutable IR conflicts with sealed immutability

MLIR is designed for mutation. A sealed artifact must instead be immutable and
re-admitted under exact authorities at every consumer boundary. The current
guard and capability pattern is directionally correct, but it must remain a
zkc invariant rather than an assumption about ownership of an `Operation *`.

Required discipline:

- no raw mutable operation escapes through an admitted capability;
- transformations work on an explicitly open clone or mint a new artifact;
- successful results are resealed and re-authenticated; and
- analysis views carry immutable semantic facts, not retained MLIR pointers.

### 4.3 MLIR text and bytecode are unsuitable as semantic identity authority

Printer choices, property layout, dialect evolution, unknown-field behavior,
and bytecode versioning serve compiler transport needs. zkc needs a smaller,
explicit canonical semantic encoding whose domain tag and preimage are owned
by its specifications.

Upstream describes the [MLIR bytecode format](https://mlir.llvm.org/docs/BytecodeFormat/)
as versioned and stable under an important assumption: dialect definitions are
immutable unless the dialect supplies its own version and upgrade handling.
That transport promise does not identify zkc semantics across evolving v0
dialect definitions.

Therefore:

- artifact identity must continue to use zkc canonical encoding;
- MLIR bytecode is an authenticated carrier, not the named semantic object;
- stable exchange must not be promised merely because bytecode round-trips;
  and
- any future portable format must map to the same carrier-independent content
  contract rather than define a second meaning.

### 4.4 Dependency and expertise cost are real

MLIR brings LLVM-scale builds, C++ APIs, TableGen, version churn, and a smaller
contributor pool than a plain Rust or schema-based representation. It raises
the cost of installation, embedding, fuzzing, language bindings, and small
independent checkers.

These costs argue for narrow carrier adapters and MLIR-free public views. They
do not yet outweigh the transformation infrastructure already used by zkc.

### 4.5 Generic transformations can be semantically unsafe

SSA legality, purity, dominance, and memory effects do not capture all
Protocol identity and transcript constraints. A generic canonicalization may
be locally legal but globally identity-changing or outside an admitted
transition family.

Every enabled generic pass should therefore be classified as:

```text
representation-only and identity-preserving
semantic transformation requiring new identity
legal only on Open PIR
legal on OIR pure regions under an observable-equivalence rule
forbidden on admitted sealed content
```

The whitelist and its preservation argument belong to the relevant carrier
and transformation specifications.

### 4.6 The dialect can accidentally become a duplicated specification

ODS descriptions and C++ verifiers are precise and attractive. If normative
documents simply paraphrase them, the code becomes de facto authority; if the
documents independently restate every field, the project creates two schemas
that can drift.

The final design needs one semantic Protocol/OIR definition, one carrier
mapping, and generated or mechanically checked inventories where practical.

### 4.7 MLIR enlarges the implementation trust surface

Parsing, verification, rewriting, and bytecode handling depend on a large
upstream system. That is acceptable for the compiler workbench, but it is a
poor endpoint for a minimal independent checker or long-term exchange
boundary.

The response should be defense in depth through small semantic encodings,
immutable admitted views, differential or independent checking, and explicit
residual trust—not a claim that the dependency can be eliminated from the
current compiler.

## 5. Alternatives and their appropriate roles

| Alternative | Main strength | Main weakness for current zkc | Recommended role |
|---|---|---|---|
| Custom immutable AST in Rust or C++ | Small controlled model, easier embedding and stable API | Must rebuild IR traversal, use-def, diagnostics, passes, rewriting, textual tools, and multi-level conversion | Possible future independent checker or portable semantic view, not a current wholesale replacement |
| Protobuf, FlatBuffers, Cap'n Proto, or JSON schema | Good transport and language interoperability | Serialization schema does not supply compiler semantics, linearity, effects, transformations, or canonical semantic identity by itself | Envelope, exchange, or evidence transport after the semantic model is complete |
| Lean, Coq, or another proof-assistant datatype | Machine-checked definitions and theorems | Poor primary mutable compiler workbench; extraction and integration do not remove runtime admission needs | Formal model and theorem correspondence for selected kernels |
| LLVM IR | Mature backend and optimization ecosystem | Too low-level and machine-oriented for transcript, claim, relation, and endpoint semantic objects | Downstream realization target where appropriate |
| Custom graph database or e-graph | Powerful search or equivalence exploration | Does not naturally own ordered effects, artifact identity, or complete endpoint programs | Internal optimizer component if a concrete transform family needs it |
| Keep MLIR with carrier-independent semantic views | Retains current compiler leverage while limiting authority and dependency leakage | Requires disciplined dual interfaces and correspondence checks | Present recommendation |

No serialization technology solves semantic ownership by itself. No proof
assistant replaces operational parsing, admission, or execution. The right
comparison is therefore role-by-role rather than “MLIR versus one universal
replacement.”

## 6. Required architectural constraints

Keeping MLIR is justified only if the final v0 architecture enforces these
constraints:

1. **Carrier-independent subjects.** Protocol, admitted artifact, analysis
   view, OIR observables, and realization obligations are defined without
   requiring an MLIR class name to state their meaning.
2. **zkc-owned identity.** Canonical semantic encoding and domain-separated
   identities remain independent of MLIR text and bytecode.
3. **Qualified capabilities.** Parsing, MLIR verification, decoding, seal,
   artifact admission, projection admission, and analysis admission grant
   different types or predicates.
4. **Immutable consumer views.** Semantic consumers do not retain mutable IR
   authority. Analysis remains MLIR-free after adaptation.
5. **Checked transitions.** Every identity-changing pass names its source,
   target, environment, preservation or refinement relation, and refusal
   boundary.
6. **Effect-aware OIR optimization.** Generic rewriting is restricted to a
   reviewed whitelist and an explicit observable-semantics contract.
7. **No accidental interchange promise.** Bytecode compatibility and producer
   markers remain carrier concerns until an external trust boundary justifies
   a versioned exchange contract.
8. **Independent-checker path.** The semantic model remains small enough that a
   future checker need not import MLIR, the pass manager, or the full compiler.
9. **Demand-driven new dialects.** A realization IR is added only when several
   targets share a durable intermediate semantic role with its own consumers
   and preservation contract.

## 7. Reconsideration triggers

Re-evaluate the carrier choice if one or more of these conditions becomes
true:

- admitted transformations remain trivial and rare, while stable exchange and
  embedding become the dominant use cases;
- external consumers require a small independently implemented decoder and
  checker as a primary trust boundary;
- LLVM/MLIR upgrade cost repeatedly dominates protocol feature work;
- non-C++ consumers require the complete semantic model and MLIR-free views
  prove insufficient;
- the dialect spends most of its complexity working around MLIR mutability
  rather than using its analysis and transformation facilities; or
- the carrier mapping cannot be mechanically kept consistent with the
  carrier-independent Protocol and OIR definitions.

Evidence in the opposite direction strengthens the current choice:

- several admitted transformation families with nontrivial rewrites;
- multiple meaningful abstraction levels;
- growing endpoint optimization under protected effects;
- useful dialect conversion into several realization targets; and
- continued leverage from common verifier, diagnostic, pass, and testing
  infrastructure.

A reconsideration should compare total migration cost and residual complexity,
not only line count or build time. Replacing MLIR after semantics are complete
is less risky than replacing it in order to discover what the semantics are.

## 8. Primary external references to use in final review

- [MLIR: Scaling Compiler Infrastructure for Domain Specific
  Computation](https://research.google/pubs/mlir-scaling-compiler-infrastructure-for-domain-specific-computation/)
  motivates reusable multi-level IR infrastructure.
- [Defining Dialects](https://mlir.llvm.org/docs/DefiningDialects/) and
  [Defining Dialect Operations](https://mlir.llvm.org/docs/DefiningDialects/Operations/)
  describe the extensibility and generated structural machinery zkc uses.
- [Interfaces](https://mlir.llvm.org/docs/Interfaces/) describes reusable
  behavioral contracts across operations and types.
- [Pass Infrastructure](https://mlir.llvm.org/docs/PassManagement/) and
  [Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/) describe
  the transformation infrastructure and its limits.
- [MLIR Bytecode Format](https://mlir.llvm.org/docs/BytecodeFormat/) is relevant
  to transport and version mechanics, not to zkc's semantic identity.

These sources support statements about MLIR's design and mechanisms. They do
not validate zkc's dialect, passes, canonical encoding, or semantic claims.

## 9. Absorption and deletion

Promote the final carrier role and constraints into project architecture; put
the Protocol-to-PIR and endpoint-semantics-to-OIR mappings in their owning
carrier specifications; put dependency and supported-version facts in status
and guides; and preserve a decision record if the choice is ratified after
alternatives are reviewed.

Delete this note when those destinations contain the complete conclusion and
reconsideration triggers. Durable pages must not link here as their rationale.
