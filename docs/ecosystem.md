# Ecosystem

> **Document role.** This guide explains how zkc's architecture relates to
> concrete relation toolchains, formal systems, proving libraries, compiler
> infrastructure, and zkVMs. It is not a compatibility list, endorsement,
> benchmark, or claim that an adapter exists. The [Architecture](architecture.md)
> owns the project-independent model. Current checkout claims belong in the
> authoritative [Current Status](status.md); the
> [repository README](../README.md) is a summary, and planned work belongs in
> the [Roadmap](roadmap.md).
>
> External interfaces were reviewed against primary project sources on
> 2026-08-03. Every real integration must pin and revalidate the exact revision
> it consumes.

zkc sits between relation-producing systems and protocol implementations. The
intended integration shape is below; boxes and arrows do not imply that an
adapter exists. zkc does not absorb either side's semantic authority:

```text
relation source and witness toolchain
  -> native relation artifact and interface
  -> zkc relation adapter and protocol binding
  -> sealed protocol and typed judgments
  -> endpoint Operator IR (OIR)
  -> zkc realization adapter
  -> proving library, device, service, or zkVM runtime

formal or analysis system
  -> exact theorem, estimate, receipt, or observation
  -> attributed zkc evidence record
  -> consumer admission for one exact subject and claim
```

The same project may occupy several roles. A zkVM, for example, can define a
VM relation, generate traces, contain a proof protocol, implement a prover,
and consume recursive proofs. “Supports project X” is therefore never a single
Boolean property.

## 1. How to read a relationship

Each relationship crosses up to three independent extension boundaries:

1. **Semantic-contract boundary:** which exact relation, protocol operation, ABI,
   parameter, and identity is being described?
2. **Implementation boundary:** which pinned compiler, library, binary, device, or
   service produces or executes it?
3. **Evidence boundary:** what theorem receipt, correspondence check, replay,
   vector, attestation, or explicit trust premise supports the claimed link?

Crossing one boundary never crosses another. Importing a circuit format does not
prove source correspondence. Calling a prover does not establish protocol
equivalence. Reproducing one challenge stream does not prove all backend
behavior. Checking a formal proof does not prove that its statement models the
zkc subject to which it is attached.

The following labels summarize why each project appears in this guide:

| Category | Meaning | Examples discussed below |
|---|---|---|
| Structural dependency | The project is part of zkc's ordinary build or carrier. | LLVM and MLIR. |
| Bounded implementation evidence | A pinned, explicitly scoped external execution is part of the evidence surface. | Plonky3. |
| Formal evidence source | Exact ArkLib declarations can be inspected through a receipt procedure and checked with Lean, without becoming an ordinary compiler dependency. | ArkLib declarations, checked with Lean. |
| Research or comparison neighbor | The project pressure-tests a boundary or supplies an independently attributable analysis. | VCVio, Ethereum soundcalc, and a historical SP1 mapping. |
| Candidate adapter or target | The architecture has a natural seam, without implying implemented ingress or lowering. | Circom, Noir/ACIR/ACVM, LLZK, zkInterface, arkworks, Halo2, OpenVM, Jolt, SP1 as a system, and RISC Zero. |

These are orientation labels, not capability or evidence grades. Exact
revisions and fixtures are recorded by pins, manifests, and evidence records;
current capability and residual assumptions belong in [Current Status](status.md).
The current public checkout has no relation-tool adapter; every relation-system
entry below describes a candidate boundary rather than implemented ingress.

## 2. Relation and witness producers

Relation systems provide predicates and public interfaces; their toolchains
may also provide witness machinery. At the target boundary, zkc is responsible
for authenticating their exact outputs and binding them to a protocol; it does
not become the source compiler or a universal interpreter for their predicates.

### Circom

[Circom](https://docs.circom.io/getting-started/compiling-circuits/) compiles
source into several distinct products: an R1CS constraint artifact, symbol or
debug data, and WASM or C++ witness-calculator code. Executing the calculator
then produces witness material through a separate workflow.

A future adapter would bind the exact compiler and format revision, R1CS bytes,
field profile, ordered public-input ABI, witness-port map, calculator identity,
and witness artifact or provider session. zkc would add relation-instance,
statement, protocol, invocation, and evidence identities around those native
objects.

The important non-implications are:

- parsing R1CS does not establish correspondence to Circom source;
- a calculator returning a witness does not establish R1CS satisfaction;
- R1CS plus a witness does not establish absence of underconstraints; and
- artifacts emitted by one command are not mutually correct merely because
  they share a producer invocation.

Circom would be one versioned ingress profile, not the definition of zkc's
relation boundary.

### Noir, ACIR, and ACVM

[Noir](https://noir-lang.org/) is a relation-source language. Its
[ACIR](https://github.com/noir-lang/noir/blob/master/acvm-repo/acir/README.md)
is an intermediate constraint representation between frontends and proving
backends, while
[ACVM](https://github.com/noir-lang/noir/blob/master/acvm-repo/acvm/README.md)
solves ACIR witnesses and executes supporting operations.
ACIR's own documentation notes that a backend may add constraints and witnesses,
so ACIR need not be the final proving relation.

A future zkc profile would consume compiled bytecode and ABI, exact compiler
and format identities, public and private input roles, field and black-box
requirements, an ACVM-backed witness-provider contract, and any backend
relation-lowering identity. If the backend changes the relation, zkc needs the
post-lowering artifact or a separate refinement and correspondence claim; an
ACIR digest alone cannot authenticate the final predicate.

“Backend agnostic” does not mean that all backends produce identical relations,
proof protocols, or encodings. ACVM solving also does not establish satisfaction
of backend-added constraints.

### LLZK

[LLZK](https://github.com/project-llzk/llzk-lib) is an MLIR-based relation and circuit
IR. Its component model distinguishes witness computation from constraint
generation even when both appear in one component; the
[syntax guide](https://github.com/project-llzk/llzk-lib/blob/main/doc/doxygen/03_syntax.md)
uses separate computation and constraint contexts.

This is a natural boundary match rather than a reason to merge the projects. A
future LLZK adapter could bind an exact module, instantiated types and shapes,
public ABI, constraint artifact, and witness-computation implementation to
Protocol IR (PIR) claims and endpoint witness ports. Shared MLIR infrastructure
can help diagnostics and adapters, but LLZK operations do not become PIR
operations and LLZK transformations do not acquire Protocol Kernel authority.

Co-location of witness and constraint code does not prove their correspondence.
Each source frontend and target lowering keeps its own attributed correctness
claim.

### zkInterface

[zkInterface](https://github.com/QED-it/zkinterface) is an interchange protocol
and schema, not a relation compiler. Its FlatBuffers messages distinguish
circuit headers, constraint systems, witnesses, and commands, which makes it a
useful pressure test for zkc's planned artifact, statement, witness, and
provider roles.

A safe profile would still have to close the accepted schema version, message
ordering and stream identity, free-form configuration interpretation,
statement-variable order, producer provenance, relation/witness join rules,
and streaming behavior. Schema validity establishes none of relation meaning,
satisfaction, producer correctness, or zkc witness-capability semantics.

zkInterface describes itself as an experimental interoperability layer focused
on low-level constraint-system exchange. It should remain one possible profile,
not be elevated to a universal zkc relation package.

## 3. Formal assurance

Formalization systems provide theorem statements and machine-checkable proof
evidence. In the target architecture, zkc checks the binding from an exact
formal subject to an exact protocol obligation and enforces a consumer-selected
admission policy. The current receipt surface does not implement that semantic
bridge, and zkc does not acquire theorem truth by citing or loading a formal
artifact.

### Lean

[Lean](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) is the
proof-assistant host and proof-term checker, not a ZK theorem library. Kernel
acceptance says that one elaborated proposition follows from its environment;
the axiom profile and the correspondence between formal and intended meaning
remain separate concerns.

There are two independent north-star directions:

```text
Lean -> zkc
  exact declaration, printed statement, axiom profile, toolchain, and revision
    -> receipt bound to one zkc rule or subject obligation

zkc -> Lean
  Protocol Kernel, judgment evaluator, projection, or concrete protocol subject
    -> exported/formalized model plus a separately checked correspondence
```

Consuming a theorem never implies that the zkc checker itself is verified. A
future generic formalization-provider interface should admit Lean first without
hard-coding Lean as the only possible proof system.

### ArkLib

[ArkLib](https://github.com/Verified-zkEVM/ArkLib) is a developing Lean library
for formalizing interactive oracle reductions and SNARKs, including
specifications and selected composition, completeness, and
(knowledge-)soundness results. It is a concrete theorem provider whose
abstractions align well with the PIR claim-flow graph.

zkc's public formalization surface can inspect exact declarations from a pinned
ArkLib checkout through a receipt-reading procedure. That is stronger than a
paper citation and weaker than importing a theorem into compiler semantics.
Current receipt metadata lives in
[`soundness-signature.json`](../registry/soundness-signature.json); the pinned
reading, explicit theorem demand, and drift procedure are documented in
[Formalization Evidence](formalization.md) and exercised by
[`formalization_receipts.py`](../test/Soundness/Inputs/formalization_receipts.py).

A mature bridge has three separately owned links:

```text
Sealed PIR occurrence and zkc rule obligation
  <-> explicit subject-correspondence object
  <-> exact ArkLib declaration and axiom profile
  -> attributed evidence admitted by policy
```

Lean checks the declaration, ArkLib owns its definitions and statement, and the
bridge author owns theorem-to-zkc correspondence until that correspondence is
itself mechanized. A receipt does not automatically cover interleaving, shared
challenges, the full Fiat-Shamir hop, deployed verifier correspondence, or the
whole protocol.

### VCVio

[VCVio](https://github.com/Verified-zkEVM/VCVio) provides Lean semantics for
oracle computations, handlers, probabilistic programs, simulations, and game
reasoning; its design is described in the
[VCVio paper](https://eprint.iacr.org/2026/899). It is a complementary formal
neighbor to ArkLib rather than the same kind of library.

ArkLib is the more direct source for IOR and reduction theorem shapes. VCVio is
the more direct candidate for transcript-runner semantics, oracle handlers,
Fiat-Shamir game hops, rewinding, and logging or caching correspondence. A
future bridge could interpret an authenticated PIR transcript spine as a VCVio
oracle computation and bind a game theorem to one zkc obligation.

Today that is a research direction, not a translator or proof receipt. Citing
VCVio does not establish faithful runner interpretation, relation satisfaction,
or backend correspondence.

## 4. Analysis, proving libraries, and compiler infrastructure

### Ethereum soundcalc

[ethereum/soundcalc](https://github.com/ethereum/soundcalc) is a security
calculator for hash-based zkEVM proof systems. It currently reports
round-by-round security for underlying interactive oracle proofs and estimates
proof size; its own documentation distinguishes estimates from measured proof
sizes and leaves broader non-interactive compilation as future work.

The repository-local [`fri_soundcalc.py`](../test/Soundness/Inputs/fri_soundcalc.py)
is an independent exact-fraction re-derivation of cited formulas. It does not
import or execute `ethereum/soundcalc`; the similar local test name must not be
read as an upstream integration.

The natural relationship is an attributed analysis provider or independent
differential oracle:

```text
authenticated protocol parameters
  -> versioned soundcalc adapter
  -> external estimate
  -> comparison or candidate suggestion
  -> independent zkc applicability checks and judgment derivation
```

Numeric agreement does not prove calculator correctness, theorem applicability,
Fiat-Shamir security, or backend correspondence. Analysis-only parameters must
not silently become protocol semantics, and estimated proof size is not a
measured realization result.

### Plonky3

[Plonky3](https://github.com/Plonky3/Plonky3) is a modular toolkit of fields,
hashes, challengers, polynomial commitments, AIR interfaces, and PIOP proving
components, used especially by STARK-based systems. A concrete configuration
couples choices that span protocol semantics and implementation.

zkc currently carries one pinned, fixture-scoped
[replay and prover evidence path](../evaluation/upstream/plonky3-replay/README.md).
It is deliberately outside the compiler and is not a general Realization
Compiler or generic Plonky3 adapter.

The north-star relationship has two granularities:

- exact Plonky3 primitives can satisfy individual realization capability
  requirements; or
- a pinned `prove` or `verify` path can serve as a checked whole-endpoint fast
  path whose evidence exhaustively covers one OIR region.

PCS choice, transcript construction, challenge order, FRI shape, proof ABI, and
other acceptance-affecting parameters are fixed by the protocol before
realization. A backend revision, build, configuration, and proof-format adapter
remain separately bound. One accepted fixture proves none of generic Plonky3
support, AIR correctness, relation satisfaction, protocol soundness, zero
knowledge, or production performance.

### arkworks

[arkworks](https://arkworks.rs/) is a Rust ecosystem spanning relations, fields,
curves, polynomials, serialization, setup, and multiple proving systems. It is
not one backend and must not be confused with the Lean project ArkLib.

On the relation side, a pinned adapter could expose an exact R1CS or synthesis
result, ordered public ABI, and witness ports. On the realization side, exact
arkworks crates could provide cryptographic kernels or a whole prove/verify
path. The latter is a fast path because a generic SNARK API hides most
transcript and protocol structure.

Any integration must bind crate revisions and features, proving system,
curve and field, relation identity, instance order, witness provider,
PK/VK/SRS and setup mode, randomness policy, serialization, and validation
behavior. Generic trait conformance is not protocol equivalence; serialization
is not automatically the canonical zkc proof ABI; and circuit synthesis or
underconstraint correctness remains external.

### Halo2

[Halo2's arithmetization](https://zcash.github.io/halo2/concepts/arithmetization.html)
spans fixed, advice, and instance columns, gates, equality, lookups, synthesis,
and layout. Its
[proving-system design](https://zcash.github.io/halo2/design/proving-system.html)
also fixes commitments, challenges, permutation and lookup arguments, quotient
construction, opening protocol, keys, transcript, proof encoding, proving, and
verification.

A future integration would bind an exact circuit configuration and instance
ABI, import or author the corresponding explicit protocol, and realize its
endpoints through a pinned Halo2 implementation. It would also exercise a
materially different PLONKish protocol family than the FRI-shaped evidence
path.

A Halo2 circuit is not a portable protocol description. Circuit synthesis and
`MockProver` checks do not establish protocol security. Forks and transcript
variants are separate targets, and high-level proof calls cannot hide public
binding or transcript coverage.

### MLIR and LLVM

[MLIR](https://mlir.llvm.org/docs/LangRef/) and
[LLVM](https://llvm.org/) are current compiler infrastructure, not proving
backends. MLIR provides zkc's structural carrier, dialect and verification
machinery, passes, textual representation, and bytecode framework. LLVM also
provides build, support, testing, and low-level compiler facilities.

The governing boundary is:

> MLIR is zkc's structural carrier and compiler framework; it is not the
> semantic authority.

Dialect verification and conversion can implement fail-closed structural
checks and target legalization. They do not by themselves prove Protocol
Kernel judgments, OIR preservation, backend conformance, or protocol security.
Future schedule, kernel, or target dialects should be introduced only when
their contracts are understood. CPU lowering may eventually use LLVM IR, while
GPU, accelerator, library, and RPC targets may take different routes. The
current project is not an OIR-to-LLVM proving compiler.

## 5. zkVMs are role vectors

A zkVM combines at least four logical roles:

| Project | Relation and witness upstream | Protocol-family source | Realization/runtime target | Composition model |
|---|---|---|---|---|
| OpenVM | VM extensions, chip AIRs, interactions, traces | Segment and proof-layer protocols | Native prover and verifier | Continuations, recursion, deferrals |
| Jolt | RISC-V execution, lookups, memory, bytecode, R1CS | Staged sumchecks and final opening | Native prover and verifier | Explicit claim DAG; recursion is a separate horizon |
| SP1 | Guest compilation, shard traces, memory relation | Shard/core, normalization and compression, shrink, and Groth16/PLONK wrapper paths | CPU, GPU, or service proving | Shards, recursive compression, in-VM aggregation |
| RISC Zero | Method image, RISC-V relation, execution trace | Segment/composite, succinct STARK, and Groth16 receipt paths | Local or external proving | Continuations, assumptions, receipt composition |

The common target contract is:

```text
guest source
  -> external compiler and VM relation package
  -> relation adapter and protocol binding
  -> sealed base protocol -> OIR -> realization

execution or trace generation
  -> typed witness-provider capability
  -> invocation-bound handles -> prover endpoint

sealed child protocols
  -> separately authored continuation, aggregation, or recursive parent protocol
```

A VM package must bind the executable or program identity, ISA and extension
configuration, relation and circuit identity, public I/O ABI, segment boundary
state, witness ports, verifier key, proof format, and exact recursion layer.
With a relation adapter and protocol subject in place, zkc could compile the
surrounding protocols without owning VM semantics or source-to-relation
correctness.

### OpenVM

The [OpenVM whitepaper](https://openvm.dev/whitepaper.pdf) describes a modular
VM-extension architecture, AIRs with interactions and buses, trace classes,
and proof layers for continuations and recursion. For zkc, these separate into
VM-semantic upstream objects, relation packages, base and aggregation protocol
subjects, and native realization providers.

OpenVM buses belong to the VM relation; they are not PIR claim-flow edges.
Registering an extension or naming an AIR proves neither extension semantics nor
global balance. A native endpoint could become a checked fast path only after
exact build, configuration, proof-layer, and protected-effect correspondence
are bound. A deferred circuit remains an externally supplied relation package.
When the deferred computation is proof verification, its verifier-to-relation
lowering remains external before it becomes an outer zkc protocol.

### Jolt

The [Jolt architecture](https://jolt.a16zcrypto.com/how/architecture/architecture.html)
separates instruction lookups, memory checking, bytecode checks, R1CS glue,
sumcheck stages, and final polynomial opening. Its explicit sumcheck DAG is a
particularly useful analogue for the PIR claim-flow graph: claims are edges and
reduction protocols are nodes, while transcript dependencies determine staging.

Structural similarity is not a translation proof. Every claim, challenge,
batching coefficient, committed or virtual polynomial role, and final opening
must map to the flat transcript spine and exact claim graph. Any zero-knowledge
variant needs its own ZK judgment, and recursion remains a separate protocol and
evidence boundary.

### SP1

The reviewed [SP1 Hypercube documentation](https://docs.succinct.xyz/docs/sp1/hypercube/)
describes sharded RISC-V execution, table-shaped traces, global consistency,
recursive normalization and compression, and several final proof modes. Each
mode that changes proof or verifier semantics is a distinct protocol subject,
not a realization-only switch. CPU, GPU, and remote execution can be target
choices only when they implement the same fixed endpoint contract.

The repository includes a bounded `sp1-rlc` regression pair whose
[provenance and scope](../evaluation/README.md#regression-provenance) are
recorded separately. It does not execute SP1, import its VM relation, verify
its complete transcript, or establish implementation conformance. A full
adapter would bind the ELF and build, circuit or verification key, ordered
public values, shard and memory-boundary relations, witness generation, proof
type, and every recursive layer.

### RISC Zero

The reviewed `risc0-zkvm` 3.0.6
[`ReceiptClaim`](https://docs.rs/risc0-zkvm/3.0.6/risc0_zkvm/struct.ReceiptClaim.html)
exposes pre- and post-state, exit code, and input and output fields. Its output
can carry a journal digest and assumptions, while successful method
verification separately binds the expected image ID. Segment continuations,
assumption resolution, succinct receipts, and wrappers remain separate semantic
layers.

A future adapter would bind the method ELF and image ID, circuit or control
identities, receipt kind, verifier parameters, claim fields, journal encoding,
and ordered assumptions. Unresolved assumptions map to explicit PIR assumptions
or residuals, never unconditional claims. Receipt integrity is also distinct
from successful execution of the expected method and interpretation of its
application-defined journal.

## 6. What ecosystem integration should prove

A public integration should be named only after its exact finish line. At
minimum, reviews should ask:

- Is the external artifact and producer revision authenticated?
- Is the public ABI ordered, typed, encoded, and bound to one statement?
- Are witness generation, checker acceptance, and semantic satisfaction kept
  distinct?
- Is every protocol-affecting backend choice visible before sealing?
- Does endpoint coverage include transcript, proof I/O, checks, child
  verification, routes, EOF behavior, and decision?
- Are implementation supplier and semantic contract identities separate?
- Are theorem, correspondence, execution, and admission claims independently
  attributable?
- Are base, aggregation, recursion, compression, and wrapper protocols separate
  whenever their accepted proof languages differ?
- Does the documentation state what remains external, conditional, or open?

The purpose of these boundaries is not to keep the ecosystem at arm's length.
It is to make deep integration possible without allowing a familiar project
name to stand in for an exact protocol, implementation, or proof claim.
