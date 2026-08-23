# Multi-level MLIR compiler architectures

> **Document kind:** Temporary comparative research dossier
> **Document state:** First research pass
> **Cases:** CIRCT, IREE, upstream MLIR
> **Authority:** None. Source facts describe the named systems; PIR transfers
> are Stage 1 hypotheses.
> **Disposition:** Absorb reviewed cross-case rationale into the Stage 1
> synthesis and durable decisions, then delete this page.

## 1. Scope

This dossier asks when a semantic distinction deserves a dialect or durable IR
level, when mixed dialects are safe, and what information becomes explicit or
irreversible at each lowering boundary.

The central comparative result is:

> Add an IR boundary when denotation, admissibility, legal transformations,
> consumers, retained information, or stability contract materially changes.

Pass count, source directory size, and architectural symmetry are not enough.

## 2. CIRCT

### 2.1 Semantic families rather than phase folders

**Source fact.** CIRCT represents hardware across several dialects and levels.
FIRRTL is an input-compatibility and frontend-oriented dialect; HW describes
modules and structural connectivity; comb supplies combinational semantics;
seq supplies sequential state; SV approaches target representation. See the
[CIRCT charter](https://circt.llvm.org/docs/Charter/),
[dialect index](https://circt.llvm.org/docs/Dialects/),
[HW rationale](https://circt.llvm.org/docs/Dialects/HW/RationaleHW/), and
[Seq rationale](https://circt.llvm.org/docs/Dialects/Seq/RationaleSeq/).

**Source fact.** HW deliberately omits combinational, sequential, and
connection semantics so orthogonal dialects can coexist. The comb dialect
deliberately avoids redundant operations that would create competing
canonical forms and duplicate folding logic. See the
[Comb rationale](https://circt.llvm.org/docs/Dialects/Comb/RationaleComb/).

**Design inference.** CIRCT does not justify one dialect per compiler phase. It
justifies a dialect when a semantic family is independently meaningful and
reusable.

**PIR transfer.** Transcript order and claim flow use different structures but
belong to one Protocol subject because whole-object judgments relate them.
Separating them into independently admitted dialect artifacts would lose their
co-authority. A representation may still use distinct interfaces, operation
families, or effects inside that subject.

### 2.2 Mixed forms and conversion

**Source fact.** FIRRTL permits a limited set of foreign types so converted and
unconverted regions can coexist during partial lowering. HW is designed as a
container for orthogonal hardware dialects. See the
[FIRRTL rationale](https://circt.llvm.org/docs/Dialects/FIRRTL/RationaleFIRRTL/#non-firrtl-types).

**PIR transfer.** Mixed dialects are defensible when:

- the enclosing subject defines their role;
- every permitted foreign construct has known semantics;
- the state belongs to an explicit lifecycle phase;
- conversion proceeds toward a named closed target; and
- unknown constructs do not become implicitly legal.

Open/workbench PIR may satisfy these conditions. Sealed canonical Protocol
must be closed and fail closed.

### 2.3 Documented path dependence

**Historical report.** CIRCT records several costly commitments in its own
FIRRTL rationale:

- early elegant deviations from the existing FIRRTL contract created
  incompatibilities and prevented faithful verification;
- canonicalizing nested `flip` types erased counts needed to reject illegal
  connections and could change connection semantics;
- CHIRRTL memories, intended as early authoring conveniences, proved difficult
  to lower and could not be removed under compatibility pressure;
- source and Verilog names became public interaction points that constrained
  transformations; and
- arbitrary JSON annotations accumulated semantic force because the original
  IR lacked adequate typed extension mechanisms.

See the
[FIRRTL rationale](https://circt.llvm.org/docs/Dialects/FIRRTL/RationaleFIRRTL/)
and [FIRRTL annotations](https://circt.llvm.org/docs/Dialects/FIRRTL/FIRRTLAnnotations/).

**PIR transfer.** Four rules follow as hypotheses:

1. Never erase information required to re-establish a rejection judgment,
   even if the representation appears more canonical afterwards.
2. An authoring-only operation needs a total lowering contract, a refusal
   mode, a last legal phase, and tests preventing it from reaching seal.
3. Identity- or security-relevant extensions cannot live in arbitrary
   metadata sidecars.
4. Display labels, semantic ports, canonical references, ABI names, and debug
   handles must not collapse into one name system.

### 2.4 Analogy limit

Hardware scheduling and state can often become explicit at lower levels.
Protocol transcript order cannot be deferred in the same way: challenge
meaning already depends on it at the canonical subject boundary.

## 3. IREE

### 3.1 Boundaries at commitment frontiers

**Source fact.** IREE's path is approximately:

```text
Input -> Flow -> Stream -> HAL -> VM or executable target
```

Flow isolates host data flow and dispatchable tensor computation. Stream makes
affinity, scheduling, resources, lifetimes, sizes, and asynchronous timepoints
explicit. HAL commits to device, buffer, queue, executable, and runtime-facing
concepts. See
[phase-by-phase compilation](https://iree.dev/developers/general/developer-tips/#compiling-phase-by-phase),
[Flow](https://iree.dev/reference/mlir-dialects/Flow/),
[Stream](https://iree.dev/reference/mlir-dialects/Stream/), and
[HAL passes](https://iree.dev/reference/mlir-passes/HAL/).

**Design inference.** Each useful boundary corresponds to a decision frontier
or to information becoming explicit. This is stronger than grouping related
passes under a name.

**PIR transfer.** A candidate Protocol stack should name where it commits to:

- a closed semantic vocabulary;
- a canonical identity quotient;
- interactive versus Fiat--Shamir form;
- endpoint asymmetry and proof-stream direction;
- prover construction choices;
- resource/schedule choices; and
- concrete runtime and target ABI.

Those frontiers, not code layout, determine whether a new dialect is useful.

### 3.2 Irreversible lowering

**Source fact.** IREE Stream progressively lowers tensor operations through
asynchronous and command forms. Allocation scheduling is documented as
irreversible after aliasing and local liveness information are introduced or
erased. See the
[Stream dialect](https://iree.dev/reference/mlir-dialects/Stream/) and
[Stream pass documentation](https://iree.dev/reference/mlir-passes/Stream/#-iree-stream-schedule-allocation).

**PIR transfer.** Every zkc lowering should name:

```text
information introduced
information discarded
observables fixed
upstream judgment relied upon
whether raising is defined
```

PIR-to-OIR is not merely a change of syntax if it commits to endpoint
observability and discards Protocol-level freedom.

### 3.3 Retargetability and extension placement

**Source fact.** IREE permits already-lowered HAL inputs, but documents reduced
analysis, optimization, and retargetability. Its extension guidance recommends
introducing an extension at the highest abstraction level at which it has
shared meaning; low-level native escape hatches duplicate implementations and
carry version-skew risk. See
[IREE extensions](https://iree.dev/reference/extensions/).

**PIR transfer.** Protocol-wide semantics belong at the Protocol boundary;
endpoint-visible effects belong at OIR; shared realization mechanisms deserve
a realization IR only after multiple backends exhibit the same resource,
scheduling, or runtime semantics. Backend hooks must remain target-local.

### 3.4 Carrier identity pressure

**Historical report.** IREE notes that VMFB is only one serialization of its VM
module, but strong surrounding tools made the file format partly synonymous
with the system. See [IREE VM design](https://iree.dev/developers/design-docs/vm/).

**PIR transfer.** A convenient MLIR bytecode or package format can become the
perceived product boundary even when the architecture says otherwise.
Documentation, APIs, and conformance tests must keep Protocol identity,
canonical semantic form, transport bytes, and tool release visibly distinct.

### 3.5 Analogy limit

IREE can leave scheduling implicit while immutable tensor SSA captures the
relevant earlier semantics. PIR cannot similarly delay the transcript prefix:
challenge sampling and domain separation depend on it at Protocol level.

## 4. Upstream MLIR

### 4.1 Mechanism, not a denotation

**Source fact.** MLIR supplies extensible operations, types, attributes,
dialects, regions, interfaces, mixed forms, and transformation infrastructure
across abstraction levels. See the
[MLIR paper](https://arxiv.org/abs/2002.11054) and
[language reference](https://mlir.llvm.org/docs/LangRef/).

**Design inference.** MLIR does not supply a universal semantics, canonical
form, or preservation theorem. zkc must define all three where needed.

### 4.2 Conversion legality

**Source fact.** Dialect conversion supports partial, full, and analysis modes;
operations may be statically, dynamically, or explicitly illegal, and type
conversion uses materializations. See
[Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/).

**PIR transfer.** Partial conversion is suitable only for explicit workbench
states. Authoring-to-canonical closure and PIR-to-OIR projection need a full,
fail-closed target or an equivalently exhaustive mechanism.

**Analogy limit.** Successful full conversion establishes only the legality
contract declared by the pass. It does not prove Protocol binding, property
preservation, projection completeness, or security.

### 4.3 Effects, tokens, and whole-object judgments

**Source fact.** MLIR side-effect and speculation interfaces constrain generic
reordering and elimination. Its opaque token supplies an SSA structural
reference without defining runtime data. See
[side effects and speculation](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
and [tokens](https://mlir.llvm.org/docs/Tokens/).

**PIR transfer.** A Protocol resource effect and transcript token are useful
defense in depth. Neither establishes a unique transcript chain, framing,
challenge origin, claim linearity, or the relation between transcript and
claim flow. Those are zkc-owned whole-Protocol judgments.

### 4.4 Canonicalization and transforms

**Source fact.** MLIR canonicalization is best effort, must not be required for
pipeline correctness, and has no stable formally specified canonical form.
See [operation canonicalization](https://mlir.llvm.org/docs/Canonicalization/).

**PIR transfer.** `ProtocolId` cannot mean the output of the current generic
canonicalizer. Its preimage must be a separately specified, versioned semantic
projection.

**Source fact.** The Transform dialect separates transform IR from payload IR
and provides handles, structural preconditions, and failure modes. See the
[Transform dialect](https://mlir.llvm.org/docs/Dialects/Transform/).

**PIR transfer.** Transform IR may orchestrate candidate generation over Open
PIR. Its successful execution is not a preservation certificate; protocol
equivalence, refinement, and conditional property preservation remain separate
judgments.

## 5. Cross-case boundary criterion

A proposed durable dialect or level should normally satisfy at least three of
these conditions:

1. distinct denotation or observables;
2. distinct admission invariants;
3. materially different legal transformations;
4. distinct independent consumers;
5. previously implicit information becomes explicit;
6. information is irreversibly discarded;
7. a distinct public compatibility contract begins.

This is a research heuristic, not a numerical ratification rule. One decisive
semantic difference may outweigh several weak similarities.

## 6. Provisional consequences for the candidate portfolio

1. **One Protocol subject remains favored, not decided.** The transcript spine
   and claim-flow graph require joint admission and should not become
   independently mutable artifacts.
2. **Open versus Sealed does not yet justify two dialects.** If operation
   meanings are identical and only closure, mutability, and authority differ,
   lifecycle types may be enough.
3. **A construction dialect needs real construction semantics.** Unresolved
   holes, macros, synthesis requests, alternate graph forms, or noncanonical
   conveniences could justify it only with total lowering and a last legal
   phase.
4. **PIR-to-OIR remains a strong level boundary.** Endpoint observables,
   proof-stream direction, coverage, and legal optimizations materially differ.
5. **A shared realization dialect is deferred.** It becomes justified only if
   multiple backends share concrete scheduling, resource, placement, lifetime,
   or runtime ABI semantics.
6. **MLIR remains a plausible workbench, not yet a selected public boundary.**
   Its mechanisms support the target distinctions but cannot define their
   meaning or evidence.

This dossier narrows the reasons for adding dialects; it does not yet choose
the final number of PIR representations.

