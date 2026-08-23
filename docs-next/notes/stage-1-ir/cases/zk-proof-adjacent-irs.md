# ZK and proof-adjacent IR boundaries

> **Document kind:** Temporary comparative research dossier
> **Document state:** First research pass
> **Cases:** LLZK, CirC, Noir ACIR/Brillig, Cairo Sierra/CASM, AIR,
> zkInterface/R1CS, Interactive R1CS
> **Authority:** None. Source facts describe the named systems; their transfer
> to PIR remains a Stage 1 hypothesis.
> **Disposition:** Absorb reviewed boundary and preservation rationale into
> Stage 1 synthesis and durable owners, then delete this page.

## 1. Central finding

The surveyed systems are not points on one ladder toward a universal “ZK IR.”
They own different subjects:

```text
provable program semantics             Cairo Sierra
relation and witness construction      LLZK, CirC, ACIR/Brillig
trace-validity arithmetization          AIR
constraint interchange                 zkInterface / R1CS
restricted interactive acceptance      Interactive R1CS
explicit proof-protocol semantics       largely absent
```

**Design inference.** A distinct Protocol IR remains justified. Generalizing a
relation, circuit, AIR, or VM IR would not automatically expose commitment
authority, transcript framing, challenge derivation, endpoint asymmetry, or
conditional security rules.

A clean boundary hypothesis is:

```text
Program or VM semantics
        -> relation and witness construction
        -> exact RelationBinding
        -> Open Protocol
        -> sealed and admitted Protocol
        -> prover and verifier OIR
        -> concrete realization
```

## 2. LLZK

### 2.1 Subject and architecture

**Source fact.** LLZK is an MLIR-based composition for connecting ZK language
frontends and backends. Its structured circuit object pairs witness-generating
`compute` behavior with constraint-generating `constrain` behavior and restricts
calls by traits. See the
[LLZK syntax documentation](https://raw.githubusercontent.com/project-llzk/llzk-lib/main/doc/doxygen/03_syntax.md).

**Design inference.** LLZK's primary subject is a relation plus witness and
constraint construction, not the proof protocol used to prove it.

### 2.2 Optimizer incidents

**Historical report.** The
[LLZK changelog](https://raw.githubusercontent.com/project-llzk/llzk-lib/main/CHANGELOG.md)
records fixes preventing elimination or CSE from merging distinct
nondeterministic witnesses and fresh allocations, as well as refusal of
lowering when control flow exceeds the supported target domain.

**PIR transfer.** This is direct ZK-specific evidence that inaccurate purity,
freshness, and effect models make generic rewrites unsound. Message emission,
absorption, challenge sampling, named checks, and terminal decisions need
non-duplicable, non-speculatable semantics plus whole-Protocol verification.

**Analogy limit.** Circuit component composition does not define transcript
interleaving, shared challenges, domain separation, or property transport.

## 3. CirC

**Source fact.** CirC compiles several source languages into a common
existentially quantified circuit and targets R1CS, SMT, ILP, and MPC. The
common abstraction is a stateless computation with explicit inputs and
existential variables. See the
[CirC repository](https://github.com/circify/circ) and
[CirC paper](https://eprint.iacr.org/2020/1586.pdf).

**Design inference.** CirC's natural transformation contract is extensional:
preserve the relation or existence of a suitable witness and observable
result.

**Analogy limit.** Relation equivalence is not Protocol equivalence. It can
leave witness layouts, commitment choices, proof bytes, transcript schedules,
and security assumptions unconstrained.

**PIR transfer.** Relation-level optimization may occur upstream. If a
Protocol commits to arithmetization-dependent material, a new relation carrier
requires an explicit correspondence and may require a new Protocol identity.

## 4. Noir ACIR and Brillig

### 4.1 Relation versus witness construction

**Source fact.** Noir lowers source through HIR and SSA into ACIR and Brillig.
ACIR is a constraint program; Brillig is executable bytecode used for
unconstrained witness computation. Results of unconstrained functions must be
constrained, and the compiler checks relevant coverage. See
[Noir's architecture guide](https://github.com/noir-lang/noir/blob/master/CLAUDE.md)
and [unconstrained functions](https://noir-lang.org/docs/language/unconstrained).

**PIR transfer.** This supports separate subjects for:

- `RelationContract`: what must hold;
- witness or prover construction plan: how required values are built;
- Protocol: how the claim is proved; and
- coverage/correspondence: why the plan supplies every Protocol obligation.

Canonical Protocol should not absorb arbitrary witness-generation programs
merely because the prover needs them.

### 4.2 Backend neutrality

**Source fact.** Noir emits circuit and witness artifacts for proving backends,
but its profiler shows that ACIR opcode cost and target gate cost can differ
substantially. See the
[manual workflow](https://noir-lang.org/docs/getting_started_manually) and
[profiler](https://noir-lang.org/docs/tooling/profiler).

**Design inference.** “Backend independent” means independent within an exact
field, opcode, capability, and interpretation profile. It does not mean that
backend choice has no semantic or cost constraints.

**Analogy limit.** An ACIR circuit that verifies another proof still represents
the verifier as an outer relation. It does not own the outer proof protocol's
commitment and Fiat--Shamir schedule.

## 5. Cairo Sierra and CASM

### 5.1 Admitted provable execution

**Source fact.** Sierra is a linear IR lowered into safe CASM. Its types carry
usage properties such as droppability and duplicability, and its libfunc,
failure, recursion, and gas rules are designed so executions remain provable.
See the
[official Sierra guide](https://docs.starknet.io/build/starknet-by-example/advanced/sierra-ir)
and [Cairo Book discussion](https://www.starknet.io/cairo-book/es/appendix-09-sierra.html).

**PIR transfer.** Sierra demonstrates the utility of an admitted intermediate
subject whose invariants are established before deployment. Its linear type
discipline is analogous to, but does not replace, Protocol claim and effect
linearity.

### 5.2 Deployed compatibility boundary

**Source fact.** Starknet publishes supported Sierra/Cairo versions, maintains
a compiler spanning versions, and records a compiled class hash for a specific
Sierra-to-CASM result separately from the Sierra class. See
[chain versions](https://docs.starknet.io/learn/cheatsheets/chain-info),
[tooling](https://docs.starknet.io/learn/cheatsheets/tools), and
[state](https://docs.starknet.io/learn/protocol/state).

**PIR transfer.** Source semantic identity, endpoint identity, and realized
artifact identity may all be necessary. Once an IR crosses organizational or
consensus boundaries, version matrices, allowed-operation profiles, migration
compilers, and derived-output identities become product infrastructure.

**Analogy limit.** Sierra preserves program execution and resource/failure
properties. It does not define transcript semantics or transport a
cryptographic reduction theorem.

## 6. AIR and Winterfell

### 6.1 Subject and phase dependencies

**Source fact.** Winterfell's AIR interface fixes field, public inputs,
transition constraints, boundary assertions, degrees, and optional periodic
columns. Randomized AIR divides a trace into stages; later auxiliary trace
construction consumes verifier randomness derived after earlier commitments.
See the [Winterfell AIR documentation](https://raw.githubusercontent.com/facebook/winterfell/main/air/README.md).

**Source fact.** The actual verifier implementation owns the ordered commitment,
challenge, evaluation, and FRI schedule. See the
[Winterfell verifier](https://raw.githubusercontent.com/facebook/winterfell/main/verifier/src/lib.rs).

**Design inference.** AIR owns trace validity, not the full STARK Protocol.
However, randomized AIR proves that the relation/protocol boundary may have
typed phase and challenge requirements rather than being entirely independent.

**PIR transfer.** A relation interface may declare phases and challenge inputs.
PIR should own the actual commitments, transcript events, challenge authority,
and Fiat--Shamir construction that make those inputs available.

### 6.2 Interoperability pressure

**Historical report.** A
[Plonky3 universal-verifier proposal](https://github.com/Plonky3/Plonky3/issues/511)
lists field, hash, challenger, PCS, AIR shape, parameters, verification-key
content, serialization, and versioning as interoperability dimensions. It is a
proposal, not a ratified standard.

**PIR transfer.** “STARK” or “AIR” is not a closed semantic profile. Any
portable Protocol boundary needs exact choices for transcript and cryptographic
dependencies that can change proof bytes or accepted behavior.

## 7. zkInterface and R1CS interchange

**Source fact.** zkInterface specifies FlatBuffers messages for R1CS circuits,
instances, and witnesses and separates instance reduction from witness
reduction. Gadget composition needs variable allocation, local-variable
conventions, input/output wiring, and witness ownership. See the
[zkInterface proposal](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-zkinterface.pdf).

**PIR transfer.** A real interchange boundary immediately requires explicit
field configuration, public/private separation, interface identity,
allocation, and composition rules. This is useful precedent for relation
ingress, not for the Protocol transcript.

**Analogy limit.** zkInterface messages are tool-transport messages, not
prover/verifier transcript events. Concatenating constraints is not protocol
composition.

## 8. Interactive R1CS

**Source fact.** I-R1CS can encode a fixed number of rounds of prover messages
and uniformly random verifier responses followed by a matrix-style acceptance
test. See
[Efficient Proofs of Possession for Legacy Signatures](https://eprint.iacr.org/2025/538.pdf).

**Design inference.** This is a counterexample to the claim that every
relation-like IR is non-interactive. Restricted interaction can be represented
arithmetically while preserving round indices.

**Analogy limit.** A general PIR should not flatten commitments, codecs,
stateful sponges, claim provenance, endpoint I/O, and composition context into
positions in one matrix. I-R1CS does not provide a general construction or
interchange model for those features.

## 9. Comparative boundary matrix

| Case | Primary subject | Transcript first-class? | Useful transfer | Non-transfer |
|---|---|---|---|---|
| LLZK | Structured relation and witness/constraint construction | No | MLIR viability; freshness and effect discipline | Circuit calls are not protocol composition |
| CirC | Existentially quantified computation | No | Relation-level transformation contracts | Extensional equality is not Protocol equality |
| ACIR/Brillig | Constraint program plus witness bytecode | No | Separate relation and construction lanes | Backend-neutral artifact is not full protocol semantics |
| Sierra/CASM | Safe provable program execution | No | Admission, linear usage, derived artifact identity | Program correctness is not cryptographic reduction transport |
| AIR | Trace-validity relation with phase dependencies | Partial requirements only | Typed challenge needs at relation boundary | Verifier code still owns the schedule |
| zkInterface/R1CS | Constraint interchange | No | Exact relation ABI and composition discipline | Tool messages are not transcript messages |
| I-R1CS | Restricted interactive acceptance relation | Abstract rounds | Interaction can appear in arithmetic form | Not a general transcript or endpoint model |

## 10. Stage 1 design pressures

### 10.1 Keep Protocol narrow and explicit

PIR should own:

- ordered prover/verifier events;
- transcript absorption and challenge derivation;
- claims, reductions, checks, and terminal behavior;
- theorem, assumption, and construction bindings needed for those events; and
- exact relation interfaces consumed by the Protocol.

It should reference rather than duplicate program semantics, constraint
systems, trace relations, and witness algorithms.

### 10.2 Fix binding time by semantic effect

Before Protocol sealing, bind every choice that changes transcript bytes,
challenge distribution, accepted proofs, or the interpretation of a property
judgment. A relation carrier may be selected later only if it satisfies a
separately defined correspondence to the already identified relation
interface. Concrete suppliers and machine targets may bind after OIR only when
they cannot reinterpret Protocol meaning.

### 10.3 Protect freshness and ordered effects

Message emission, absorption, challenge occurrence, proof input, checks, and
decisions require exact freshness, duplication, speculation, and ordering
rules. Generic CSE or reordering is illegal unless a Protocol-specific
validator establishes the claimed relation.

### 10.4 Use preservation grades

At minimum distinguish:

- representation equivalence with the same Protocol identity;
- relation equivalence or equisatisfiability;
- Protocol observation equivalence;
- endpoint correspondence or refinement;
- conditional property transport under named assumptions;
- checked intentional change with reported property deltas; and
- candidate generation with unresolved obligations.

### 10.5 Keep identities distinct

The evidence supports separate identities for Protocol, semantic regime or
profile, relation interface, endpoint program, and concrete realization. It
does not decide whether external interface identity is embedded in
`ProtocolId` or paired as a separately identified subject.

## 11. Implication for MLIR

The proof-adjacent cases support MLIR as a viable primary structural and
transformation substrate. LLZK supplies the strongest direct evidence. Its
optimizer incidents show that dialect semantics and effects must be accurate;
they do not show that a second Rust semantic core is preferable.

The working hypothesis remains:

```text
language-independent normative Protocol semantics
        represented by a zkc MLIR dialect or closed profile
        admitted by zkc-owned whole-object checks
        identified by a semantic canonical projection
        consumed through typed capabilities or views
```

This is not yet a selection of one dialect versus several, nor a decision to
publish MLIR bytecode as the stable interchange artifact.

