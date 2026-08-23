# Stage 1 first-wave cross-case synthesis

> **Document kind:** Temporary research synthesis
> **Document state:** First-wave synthesis complete; superseded by evaluation
> **Authority:** None. This page synthesizes the first research wave and does
> not select the target architecture.
> **Disposition:** Replace hypotheses with scenario results, promote the final
> architecture and decisions to durable owners, then delete this page.

> **Completion note — 2026-08-22:** The required candidate construction and
> scenario gate are complete in [Candidate Instantiations](candidate-instantiations.md)
> and [Scenario Results](scenario-results.md). The
> [Convergence Record](convergence.md) and durable
> [Protocol IR Architecture](../../project/protocol-ir-architecture.md) replace
> the hypotheses below; this page remains the first-wave research record.

## 1. Scope and state

This synthesis combines:

- the [zkc-native design-force ledger](zkc-design-forces.md);
- [current specification and implementation correspondence](cases/current-zkc-correspondence.md);
- [portable/interchange IRs](cases/portable-ir-contracts.md);
- [multi-level MLIR systems](cases/multilevel-mlir.md);
- [long-lived IR contracts](cases/long-lived-ir-contracts.md);
- [ZK and proof-adjacent IRs](cases/zk-proof-adjacent-irs.md); and
- [protocol and transformation theory](cases/protocol-semantics-theory.md).

The first divergence wave is broad enough to construct better candidates. It
is not yet a convergence decision. In particular, no case study can decide an
architecture merely because its mechanism has been successful elsewhere.

## 2. Most important correction to the previous question

The earlier discussion often treated these as one choice:

```text
MLIR-centered PIR
        versus
carrier-independent Protocol model
```

That is a false binary.

There are at least four independent questions:

1. **Normative semantics:** can Protocol meaning be stated independently of
   MLIR printer, bytecode, C++ classes, and pass behavior?
2. **Primary compiler representation:** which data structure best supports
   construction, transformations, diagnostics, and lowering?
3. **Canonical identity form:** over what exact semantic projection is a
   Protocol named?
4. **External consumer surface:** what do independent tools decode and check?

The answer can consistently be:

```text
language-independent normative semantics
        +
MLIR as the primary compiler and possibly canonical structural representation
        +
zkc-owned canonical semantic identity
        +
minimal authenticated views or a later portable profile for external consumers
```

No surveyed evidence supports moving the semantic center into a parallel Rust
object merely to claim independence. Conversely, using MLIR internally does
not justify making arbitrary MLIR text or bytecode the public semantic contract.

## 3. Candidate-independent conclusions with strong support

These conclusions recur across native evidence, external cases, and theory.
They should constrain every serious candidate unless a later counterexample
reopens them.

### 3.1 Protocol is a distinct semantic subject

Relation, witness-construction, trace, program, endpoint, and realization IRs
have different denotations and preservation laws. LLZK, CirC, ACIR, AIR,
Sierra, and R1CS do not make explicit Protocol IR redundant.

Protocol should own at least:

- role-indexed message and proof events;
- transcript absorption and challenge derivation;
- claims, reductions, checks, and terminal behavior;
- exact statement/relation interfaces consumed by the Protocol; and
- theorem, construction, and assumption bindings required to interpret those
  events.

It should not become a universal relation, VM, or backend IR.

### 3.2 The two primary geometries remain

The ordered effect spine and linear claim/reduction graph are independently
necessary and jointly constrained. Ordinary SSA/dataflow equivalence cannot
replace their coupling.

### 3.3 Semantic order needs observation-indexed effects

At minimum protect transcript/Fiat--Shamir, proof-wire, public-binding, check,
artifact-verification, claim, and terminal observations. A rewrite may be
central for one observer and not another. Unqualified commutation or
“semantic equivalence” is insufficient.

### 3.4 Admission is a judgment lattice

Decoding, local IR validity, closure, identity authentication, semantic
admission, endpoint projection, property analysis, realization, and execution
remain distinct. SPIR-V, ONNX, StableHLO, WebAssembly, and current zkc all
reinforce this separation.

Canonical PIR should not have a general undefined-behavior escape hatch that
makes arbitrary target behavior acceptable.

### 3.5 Identity is independent of generic carrier bytes

MLIR text, MLIR bytecode, source labels, producer metadata, and generic
canonicalization cannot define `ProtocolId`. Identity needs a separately
specified semantic projection with explicit invariance and sensitivity tests.

### 3.6 Closed canonical semantics, explicit external dependencies

A sealed canonical Protocol must fail closed on unknown semantic content. An
extension system must distinguish canonical operations, authoring conveniences,
semantics-defining decompositions, exact cited contracts, opaque external
subjects, realization hooks, and removable non-semantic annotations.

### 3.7 Transformations need named relations

At minimum distinguish representation equality, exact Protocol equality,
observer-relative trace equivalence, refinement, distributional relation,
Fiat--Shamir preservation, property transport, checked intentional change, and
cost improvement. Heuristic search can remain untrusted when each accepted
result is validated under an exact relation.

### 3.8 Interfaces and composition are first-class design problems

Current zkc relabel behavior, WebAssembly's later Component layer, zkInterface,
and mature name-preservation debt all show that incidental labels must not
become an interface ABI. Protocol composition also cannot be reduced to graph
union, function calls, constraint concatenation, or symbol linkage.

### 3.9 MLIR remains a credible primary workbench

Current zkc, LLZK, CIRCT, IREE, and upstream MLIR demonstrate real value for
typed structure, SSA, effects, diagnostics, verification, rewriting, and
multi-level lowering. MLIR still cannot define zkc semantics or prove
preservation by itself.

## 4. New architecture pressures absent or weaker in the previous baseline

### 4.1 Protocol/interface functional closure

Current `ProtocolId` erases some labels that projection and Relations later
read. The target must make every normative result a function of identified
inputs.

Candidate solutions include:

```text
interface committed inside ProtocolId
separate content-addressed InterfaceId
canonical positional interface with external aliases outside semantics
explicit authenticated carrier-qualified interface at each transition
```

The last choice is valid only if the extra input is typed and identified; it
cannot remain implicit carrier context.

### 4.2 Canonical quotient versus physical canonical form

Current `pir.sealed` preserves authored bodies while identity normalizes them
inside the encoder. This creates a canonical semantic equivalence class, not a
unique physical carrier.

That architecture is coherent only if every normative consumer reads either:

- the canonical semantic projection; or
- separately authenticated non-Protocol input.

Otherwise carrier representatives with one ID can yield different results.
Stage 1 must compare encoding-only canonicalization with normalization before
seal and with a distinct canonical representation.

### 4.3 Interactive core versus transcript construction

Theory suggests factoring:

```text
InteractiveCore
        + TranscriptConstruction
        + selected total observable schedule
        = CompiledProtocol
```

This can support one public-coin construction under several Fiat--Shamir or
duplex profiles while keeping theorem and quantitative loss explicit. It does
not require separate dialects or persisted artifacts, but it creates a real
identity-factorization question.

### 4.4 Verifier Protocol versus prover construction plan

LLZK and Noir separate relation from witness construction. Current PIR routes
and holes may bind one prover plan into Protocol identity even when several
strategies could satisfy the same verifier behavior and proof ABI.

Stage 1 must distinguish:

- verifier-visible Protocol semantics;
- abstract prover obligations;
- construction/witness plan;
- endpoint schedule; and
- concrete supplier realization.

The split must preserve honest-prover completeness and coverage; it cannot be
made solely for reuse.

### 4.5 Semantic regime

A content hash permanently names bytes, but the interpretation and seal rules
can evolve. Long-lived or independent checking needs a precise relation among:

- semantic-language or regime version;
- canonical identity encoding version;
- dialect schema;
- transport encoding;
- dependency schemas and profiles;
- admission policy; and
- producer/tool release.

Some axes may intentionally move together in v0, but the architecture must not
pretend they are conceptually one version.

### 4.6 Endpoint readiness as a typed state

Current reserved artifact verification can seal while having no projection
obligation. This forces a choice:

- canonical sealed Protocol means endpoint-obligation complete;
- seal has explicit grades or capabilities; or
- reserved/authoring content must lower away or refuse before seal.

The cleanest leading hypothesis is that one admitted canonical Protocol is
obligation-complete and authoring-only or reserved content cannot enter it.
That hypothesis still needs scenario comparison against typed partial
admission.

## 5. Where the external cases genuinely disagree

### 5.1 One working and portable form versus separate forms

- SPIR-V makes one normative binary both interchange and transformation input.
- StableHLO keeps current working StableHLO separate from versioned VHLO
  compatibility serialization.
- ONNX standardizes interchange while permitting different optimizer forms.
- LLVM migrates old bitcode into a current internal semantic model.

**Result.** There is no generic best answer. The correct location depends on
artifact lifetime, independent release cycles, consumer count, and how much
optimization structure a stable form must expose.

### 5.2 One dialect versus several levels

CIRCT and IREE justify boundaries where denotation, legality, consumers, or
information loss changes. They do not justify dialect proliferation for
symmetry. Current Open and Sealed PIR mostly differ in lifecycle, closure,
identity, and mutability, which alone may not require different dialects.

The physical-canonicalization and authoring-extension questions may eventually
create a genuine semantic level. They must be demonstrated, not assumed.

### 5.3 Stable compatibility now versus later

StableHLO, SPIR-V, ONNX, LLVM, Sierra, and WebAssembly show that compatibility
is expensive but valuable once artifacts are external and durable. Current PIR
does not yet have equivalent independent producer/consumer pressure.

**Result.** The ideal design should reserve exact version and fail-closed
mechanisms now, and define product triggers for compatibility, rather than
maintain historical operation forms speculatively.

### 5.4 Total schedule versus causal authoring form

Theory permits a causal partial-order authoring model, while transcript bytes,
wire ABI, check order, and deployed endpoints eventually require a selected
observable schedule. Current single-block total order is simple and precise but
may over-identify order among events irrelevant to some observers.

**Result.** A total sealed schedule remains strongly supported. A partial-order
authoring form is an opportunity to evaluate, not a canonical requirement.

## 6. Methodological correction: the candidate portfolio has orthogonal axes

The initial portfolio mixed subject factorization, representation, stability,
and consumer surfaces. Comparing them as five mutually exclusive architectures
would produce an apples-to-oranges decision.

Stage 1 will instead build complete candidate bundles over these axes.

### Axis S — semantic subject factorization

- `S1`: one monolithic identified Protocol root;
- `S2`: InteractiveCore plus TranscriptConstruction inside one identified
  package;
- `S3`: Protocol plus separately identified Interface;
- `S4`: Protocol plus Interface plus separately identified ProverPlan;
- `S5`: nested content identities for several of the above without requiring
  independent artifacts.

### Axis R — representation levels

- `R1`: one lifecycle-aware PIR dialect and canonical encoding quotient;
- `R2`: flexible construction/import forms fully lower to a closed physically
  canonical MLIR Protocol representation;
- `R3`: optimizing MLIR PIR lowers to a distinct portable Protocol dialect;
- `R4`: a carrier-neutral canonical package owns runtime meaning and MLIR is an
  adapter;
- `R5`: one canonical PIR remains central and supplies authenticated minimal
  consumer views.

`R5` is partly orthogonal and can complement `R1` or `R2`.

### Axis O — order and effects

- `O1`: authored and sealed total order with protected effect classes;
- `O2`: causal/partial-order authoring lowered to one identified total schedule;
- `O3`: one total schedule plus observer-indexed equivalence classes for
  checked transforms.

### Axis C — external consumer surface

- `C1`: admitted MLIR PIR;
- `C2`: closed semantic package or portable dialect;
- `C3`: consumer-specific authenticated facts;
- `C4`: transition witness or certificate plus the minimal source facts needed
  to check it.

### Axis V — stability and compatibility

- `V1`: fail-closed exact v0, no migration contract;
- `V2`: stable current semantic profile, new identities across migrations;
- `V3`: explicit compatibility representation and checked upgrades;
- `V4`: independent producer/consumer compatibility window.

The final architecture may choose different consumer and stability surfaces at
different boundaries. It must still have one semantic authority per subject.

## 7. Refined complete candidates for evaluation

### Candidate A — lifecycle quotient

```text
one MLIR PIR dialect
Open and Sealed as lifecycle states
canonical semantic encoder defines the quotient
explicit Interface input closes carrier-erased behavior
consumer-specific views
no compatibility promise beyond exact v0
```

**Strengths:** smallest model, maximum current MLIR leverage, no duplicate IR,
and inexpensive evolution.

**Risks:** physical representatives differ; every consumer must obey the
quotient boundary; authoring conveniences can accumulate; external checking
imports more compiler structure.

### Candidate B — closed canonical Protocol level

```text
authoring/import workbench forms
       -> exhaustive normalization and closure
small physically canonical MLIR Protocol representation
       -> admitted immutable capability and typed views
       -> OIR projection
```

Protocol, Interface, TranscriptConstruction, and ProverPlan identities can be
nested or separated according to semantic analysis.

**Strengths:** one carrier representative per subject, small seal surface,
clear ban on authoring-only extensions, stronger independent-checking boundary,
and less chance that ignored carrier fields leak into results.

**Risks:** normalization must preserve every rejection-relevant distinction;
the extra level may duplicate operation families; construction-to-canonical
lowering becomes trusted or must be validated; a physical normal form can
prematurely constrain evolution.

### Candidate C — optimizing PIR plus portable Protocol dialect

```text
internal evolving MLIR workbench
       -> checked conversion
stable portable Protocol dialect/profile
       -> independent checker and persisted artifacts
```

**Strengths:** isolates compiler evolution from consumer stability and follows
a proven compatibility-layer pattern.

**Risks:** permanent dual representation and conversion burden, versioned
history, possible semantic drift, and no current independent consumer that
justifies the cost.

### Candidate D — carrier-neutral semantic package

```text
normative schema/package is the primary runtime subject
MLIR PIR is an authoring and transformation adapter
independent implementations consume the package directly
```

**Strengths:** strongest language neutrality and independently implementable
boundary; potentially small checker surface.

**Risks:** a complete shadow IR, weakest optimizer ergonomics, correspondence
becomes the central trusted bridge, and the schema may freeze before Protocol
semantics are mature.

### Candidate E — fact-root and projection architecture

```text
closed canonical PIR remains the complete subject
        -> authenticated semantic fact root
        -> consumer-specific fact projections or certificates
```

**Strengths:** independent consumers need not implement the optimizer IR;
views remain purpose-specific; avoids a second complete mutable model.

**Risks:** fact roots and projections can become a second schema by accretion;
lossy views may be insufficient for new consumers; correspondence to the
complete Protocol still requires a trusted or checked adapter.

Candidate E is most likely a complement to A or B rather than a standalone
compiler representation.

## 8. Leading hypotheses after the first wave

The evidence currently makes one composite direction more plausible, without
yet selecting it:

```text
language-independent normative Protocol semantics
        +
MLIR-centered authoring and transformation
        +
one small closed canonical Protocol level or profile
        +
semantic identity independent of MLIR transport
        +
explicit Interface and possibly ProverPlan identities
        +
observer-indexed effects and named transform relations
        +
consumer-specific authenticated views
        +
no permanent compatibility dialect until an external trigger exists
```

This differs from both extremes:

- it does not make mutable MLIR implementation state the semantic authority;
- it does not replace MLIR with a complete parallel Rust model;
- it does not publish every optimizing operation as stable interchange; and
- it does not postpone interface, regime, and effect semantics until an
  ecosystem has already depended on accidental details.

The unresolved choice inside this direction is whether the closed canonical
level is:

- a subset and physical normalization of the same PIR dialect;
- a distinct canonical MLIR dialect; or
- the canonical semantic encoder plus strictly authenticated views, without a
  second physical IR.

## 9. Alternatives currently weakened, not rejected

### Complete Rust semantic core as the default runtime subject

No case has shown that implementation-language change solves the semantic
problem. It is reconsidered only if a concrete independent checker, formal
extraction pipeline, or embedding boundary demonstrates that an MLIR carrier
cannot meet its trust and deployment constraints.

### VHLO-style compatibility dialect immediately

The mechanism is strong for an established artifact contract but currently
lacks the consumer, retention, and release-cycle pressure that justifies its
permanent cost.

### A dialect for every lifecycle state

Open, resolved, sealed, decoded, and admitted roles differ greatly in
authority, but authority differences alone do not imply different operation
semantics. Typed capabilities may express several of these states more cleanly.

### One broad universal consumer view

Current view growth already mixes facts for different readers. A stable shared
fact root or smaller per-consumer projections appears more scalable, but exact
consumers must be named before selecting either.

## 10. Required next evaluation

The next Stage 1 work should build concrete schemas or mathematical sketches
for Candidates A, B, D, and the A/B-plus-E combinations. Candidate C remains
in the portfolio as the future external-stability option.

Each bundle must answer the same scenarios:

1. equal authoring forms with one intended Protocol;
2. one Protocol core with different external interfaces;
3. one verifier behavior with several prover plans;
4. interactive and Fiat--Shamir constructions over one core;
5. transcript-independent SSA operations with wire/check effects;
6. authoring-only or unknown extension content;
7. a content-changing cost optimization with property deltas;
8. protocol composition with shared or interleaved challenges;
9. an independent checker that does not import the optimizing compiler;
10. same meaning across a carrier revision;
11. same canonical bytes under two semantic regimes; and
12. source-free OIR whose original coverage must be appraised.

Evaluation must report:

- semantic fidelity and functional closure;
- identity and version behavior;
- trusted bridge/checker surface;
- transformation leverage;
- extension and compatibility cost;
- enabled and foreclosed capabilities;
- clean-room implementability;
- formalization surface; and
- reversal conditions.

Only after that comparison should Stage 1 promote a target or rebuild the
Stage 2 entry contract.
