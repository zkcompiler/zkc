# zkc Kernel Specification

Status: **canonical v0.7 structural semantics** (2026-07-25). This document is
the root of the public zkc specification corpus for the Protocol Kernel.

This document is canonical for the structural Protocol Kernel.
[`soundness.md`](soundness.md) is canonical for post-seal conditional security
and [`compiler.md`](compiler.md) for checked search. The three authorities do
not overlap: the artifact denotes structure, and no theorem citation is
protocol content.

Discipline: every load-bearing claim is graded **proved** (a proof
exists in or with the corpus) / **checked** (validated by executable
reference or test) / **cited** (an external result is relied on, with
reference) / **deferred** (named obligation, not yet discharged) —
the grading rule inherited from the v0 corpus and now defined here.
The kernel fixes
*judgments and their soundness statements*, never implementation
shapes. Anything marked *vocabulary* is provisional and lives in
`vocabularies.md`; growing a vocabulary must not change this document.

---

## 0. Purpose

A zkc protocol artifact exists to make nine judgments possible:

| | Judgment | Kernel section |
|---|---|---|
| J1 | Fiat-Shamir seal admissibility | §5 (BIND) |
| J2 | claim accounting totality | §4 (LIN) |
| J3 | protocol identity and diff | §8 |
| J4 | transformation legality | `compiler.md` §7.2 |
| J5 | endpoint projection preservation | §6 (COV_obl, COV_realized), §10 |
| J6 | composition and descent | §10 |
| J7 | post-seal conditional security derivation | `soundness.md` |
| J8 | exact local reduction closure | §4.1 |
| J9 | typed terminal closure | §4.2 |

The Protocol Kernel is the smallest structural object that supplies the
authenticated protocol facts required by all nine questions. It owns J1--J3, J5, J6, J8, and J9. The sibling Soundness Kernel in `soundness.md` owns J7 after seal and the
Compiler Core in `compiler.md` owns J4; both consume this structural object
without changing its identity. Everything
else in this document is a derived view (§11), a provisional vocabulary (§12),
or a boundary built on kernel judgments (§10).

**Scope of the promise.** A boundary receiving raw Open PIR verifies its
structural representation and the judgments named by that boundary. A boundary
receiving a raw identified PIR or OIR artifact also recomputes its identity. An
operation may instead require an opaque authenticated capability that
unforgeably binds an immutable subject or closed derived view to its identity
and the authority used at admission. Caller assertions, cached booleans,
receipts, and mutable handles never substitute for authentication. Endpoint
programs execute under the declared ABI. Hardening artifacts against arbitrary hostile target contexts is
a named non-goal (the robust-preservation quantifier of the secure-
compilation literature is out of scope; `boundaries.md` states the
consumer contract).

## 1. The kernel object

A **protocol** is

```text
P = (E, ≤, A,  C, R,  χ, K,  anchors, B_M)
```

with components defined in §§1.1–1.6. Two geometries carry all
judgments: the **spine** — the total order (E, ≤) with absorption set A
— and the **claim-flow graph** — the bipartite graph between C and R.
J1 lives on the spine, J2 on the graph, J8 and J9 at the graph/check/material
boundary, and J4 plus J7's structural inputs on their pairing:
the preconditions of the security rules a derivation applies are cross
statements
("this reduction's round challenge is sampled from a prefix containing
these events"), which is why neither geometry may be a sidecar of the
other.

Each geometry has a denotational reading, recorded as grounding — not
as judgment content; every judgment below remains a self-contained
combinatorial definition. The spine reads as a term over the protocol
signature with challenge introduction as an abstract operation,
interpreted by fresh sampling (the interactive semantics) or by the
construction profile's duplex-sponge **runner** (projection, §10) —
the stateful, one-shot, finalizing interpreter class of
[AB20](https://arxiv.org/abs/1910.11629), realized as handler
application in [VCVio](https://eprint.iacr.org/2026/899) (cited). The
claim graph reads as a **string diagram** whose denotation is a
reduction of knowledge ([KP23](https://eprint.iacr.org/2022/009);
§4, cited). Seal, in these terms: **the protocol denotes, and its
Fiat-Shamir interpretation is admissible** — WF and LIN are
definedness of the two readings, COV_obl is definedness of the
obligation reading (§6.1) — COV_realized, proved per endpoint at
projection, is totality of that endpoint's interpretation (§6.2) —
and BIND is the admissibility hypothesis of the
Binding Lemma (§9.2). A weak-FS protocol still denotes; it does not
stay sound — which is why BIND, not definedness, is the
security-critical judgment.

### 1.1 Events and the spine

`E` is a finite set of **semantic events**. `≤` is a total order on E.
`A ⊆ E` marks the **absorbing** events: exactly those that advance the
transcript state. The transcript state is linear:

```text
T_0 --e_1--> T_1 --e_2--> ... --e_n--> T_n     (e_i enumerated by ≤)
```

where T advances only at events in A.

The kernel fixes event *classes* only insofar as judgments need them:

- **slot** — proof material enters the verifier-visible stream.
  A slot is absorbing unless explicitly marked unabsorbed (§5.3). A
  counted slot in A advances the transcript by its elements in index
  order, each exactly as a scalar of its class; the count is a static
  constant of the sealed protocol, so the framing stays injective and
  prefix-free (§13(e)) without any per-event length tag.
- **public_bind** — a statement/public-input binding becomes
  protocol-visible. Absorbing.
- **challenge** — a verifier challenge is introduced (§1.5). Absorbing
  (the sample itself extends the prefix for later challenges).
- **check** — a verifier predicate is declared (§1.3). Non-absorbing.
- **artifact_verify** — a bounded verification of an imported artifact.
  Absorption of the artifact identity is a vocabulary-declared fact.
- **decision** — the endpoint decision. Non-absorbing, final in ≤.
- **object events** — commitments, openings, object state transitions
  (§1.2). Absorption per event as declared.

Finer event kinds are *vocabulary*. The total order is kept even for
non-absorbing events so that canonical encoding, and therefore identity, is
deterministic. Partial-order liberalization is outside v0.7 kernel semantics
and requires the named extension in §12.

### 1.2 Values, protocol objects, and checks

Events introduce **values** (typed handles: slot contents, challenge
values, object versions). Value use is SSA-like: a value may be used
only by events/checks at positions after its introduction (WF, §3).

**Protocol objects** (commitments, oracles, virtual oracles,
accumulators, recursive artifacts, …) are event-introduced values with
SSA-style versioning. Their coarse state alphabets are *vocabulary*;
the kernel requires only that a state transition of an object is
itself an event (no hidden mutation).

**Checks** `K` are predicates over introduced values. Each check cites one
resolved `CheckContract`, carries the contract's exact static `params` and
intrinsic `semantic_args`, and supplies a positional vector of typed operands.
The contract partitions that vector into named segments with an unambiguous
   multiplicity solution and fixes one of two declaration modes:

```text
transparent   the predicate body is an expression in the artifact
opaque        a registered call with declared input coverage
```

The human-readable contract id is a lookup and diagnostic handle. The
contract's tagged content digest is proposition and dispatch authority. A
transparent contract pins the transparent-expression binding format. An
opaque contract instead pins
`(predicate-spec content digest, entrypoint)`; the content-addressed predicate
spec supplies normative acceptance text and an ABI that must equal the
contract's parameter, semantic-parameter, and operand segmentation exactly.
Joint vocabulary admission re-derives the predicate-spec key and resolves that
entrypoint before the contract can be used. This closes the identity of the
predicate being invoked. It does not identify an executable adapter or prove
that any adapter implements the pinned proposition.

`semantic_args` are part of the proposition the check denotes; a discharge
cannot give the same check a new contextual meaning. For transparent mode, the
check also carries a canonical expression whose input leaves normalize from
positions to the unique contract roles. Opacity applies to the predicate
implementation only. Slot reads,
absorptions, challenge introductions/derivations, public bindings,
artifact verification, and decisions MUST NOT be hidden inside an
opaque check, because projection coverage depends on those effects remaining
explicit.

### 1.3 Claims

`C` is a finite set of **claims**: proof obligations, not proof objects and
not runtime booleans. Each claim has a stable id and a **descriptor**
`(profile, anchors)`. A resolved `ClaimDescriptorProfile` supplies the coarse
kind and exact ordered anchor-name schema; the instance supplies exactly one
digest-shaped value for every name and no others. There is no independently
authored kind/profile pair. Descriptor profiles are *vocabulary*; the kernel
requires that the selected profile resolves, the descriptor is canonically
encodable, and every anchor reference is well shaped (§3). Scope, parameters,
and required interfaces are not the canonical encoding descriptor fields; materializing any of
them is a future versioned descriptor constructor, not free terminal-rule
metadata.

The one minted descriptor-vector helper is deliberately exact. Given full
input descriptors encoded as `[profile, anchors]`, sort the records by their
canonical descriptor bytes, refuse duplicate descriptor bytes, and define

```text
claim_vector(descriptors) =
  SHA256("zkc/claim-vector\n" || canonical(sorted_descriptors))
```

The `batch_opening.members` anchor is this algorithm-prefixed digest. No
other list hash, independent field sorting, or traversal order is equivalent.

Claims have **no state field**. Lifecycle state is represented by position in
the claim-flow graph (§11).

### 1.4 Transformers

`R` is a finite set of **transformers**, each of one of three shapes:

```text
source        consumes nothing; produces claims
              (contract statement/connector instantiation,
               protocol-object introduction, artifact import)
reduction     consumes claims (+ objects, + challenge capabilities);
              produces claims; has a body ⊆ E; emits obligations
sink          consumes exactly one claim; produces nothing
              (four kinds: discharge / export / assume / residual)
```

The source shape is neutral: relation-specific meaning comes from the resolved
claim profile, its digest-shaped anchors, and any reduction or terminal
contract that consumes it. Relation-specific profiles belong to the admitted
vocabulary; the kernel does not add a relation-source compiler operation to
PIR.

- A reduction's **body** is a subset of E — a set, not an interval:
  bodies of distinct reductions MUST be disjoint but MAY interleave in
  ≤.
  Events outside every body belong to the ambient protocol.
- **Deferral and accumulation are reductions** (carrier-transfer
  shapes: consume member claims, produce a carrier claim), not claim
  states.
- A **discharge** sink selects one check-backed `TerminalRule` and binds the
  rule's terminal roles to a set of checks. An **export**,
  **assume**, or **residual** sink cites an explicit route ref.
  Which sinks are permitted is a SealPolicy fact (§7).
  The rule fixes the consumed claim profile, an optional exact producer
  pattern, required role-to-contract pins, attachment predicates, and the
  normalized transparent predicate for every transparent role. The role map
  is exact and injective. Artifact-verification discharge is a named future
  rule variant; it is not accepted by this version. A theorem-backed discharge
  is not a variant at all: a terminal rule never cites a theorem, and every
  theorem contribution is declared in the Soundness Kernel signature
  (`soundness.md`).
- Reduction contracts (typing of consumed/produced claim patterns, challenge
  requirements, round structure, exact body-check premises, material
  constraints, and output constructors) are *vocabulary*. A contract contains
  no security price and the reduction names no theorem: a rule binding selects
  the exact contract from the signature side (`soundness.md` §5.2). The kernel
  fixes only the judgment shape:

```text
Γ_anchor; Γ_cap; Θ; Δ_claims; T_i ⊢ reduce_R(args){body} :
    T_j; Δ_claims'; Obligations
```

### 1.5 Challenges and capabilities

`χ` assigns to each challenge event a **capability**

```text
ChallengeCap = (value, origin, pos, T, D, S, N, Q)

value  the exact event-introduced value carrying the samples
origin ∈ { fresh, project(c,i), derive(c,rule,params), imported(ref) }
pos    the event's position in ≤   (its prefix IS the set {e : e ≤ pos})
T      semantic payload class of each sample (and codec-selection key)
D      domain id (separation namespace)
S      sample space
N      exact sample count: 1, or a bounded vector count 2..2^20
Q      sampling rule: uniform for N=1; an admitted vector rule for N>1
```

`origin` and `T` are orthogonal: transcript provenance never doubles as a
semantic value class. In particular, `chal` is not a payload class. A vector
challenge is one event and one capability introducing `N` samples from `S`:
one position, domain, requirement prefix, and priced use. Reuse is a property
of the consuming contract and the rule that reads it, not of the capability.

`fresh` advances the transcript. `project` and `derive` are pure: they
MUST NOT create a new random-oracle query and their capability
inherits the source's `pos` (provenance preserved); uses of projected
or derived challenges are judged against the source's `pos`.

A challenge **use** (by a reduction or check) of the exact capability value
`v` carries a requirement
`NeedChal(v) = (O_req, P_req, T_req, D_req, S_req, N_req, Q_req)` where `P_req` is a
finite set of **event references** — not a separate fact language.
Every relevant prefix fact (statement ids, commitments, public IO, oracle
roots, child artifact ids, and prior challenges) is introduced by an event, so
event references suffice. For contract-owned uses,
`P_req` is **generated** from the reduction contract's declared round structure
(§5.2); hand-declared entries may extend the generated set, never
replace it.

Satisfaction is componentwise and binds the exact `value`; all components
except `P_req` are finite-vocabulary equality/policy checks. `P_req` is §5's
BIND. The consuming contract declares `N_req` by omission for the unique
scalar spelling or by an explicit count in `2..2^20`; explicit count one
refuses. A scalar use cannot bind a vector capability or conversely — the
repetition exponent a rule reads and the sealed sample count are one
declaration (§9; `soundness.md`). The contract's dependency class must also
equal `T_req`; origin constraints are checked separately from that semantic
class.
Reuse: a **use** is requirement-bearing consumption — a reduction
binding the challenge to a round slot, or an ambient check acting as
the challenge's consumer (the sigma shape). By default a challenge
satisfies at most one use; shared use (batching) MUST be declared by
the consuming contract, because sharing is a soundness lever priced by
the rules that read them (§9). A check **reading** a challenge value inside a
reduction's obligations (sumcheck's cross-round consistency reads
prior challenges) is not a use: the read demands nothing of the
sampling — the consuming reduction's round structure already carries
the requirement.

### 1.6 Anchors and material bindings

`anchors` is the set of digest-shaped semantic references carried by claim
descriptors. The resolved claim profile fixes their exact names and order, but
the kernel treats their referenced content as opaque. It authenticates profile
and anchor shape, claim flow, and the exact reduction or terminal contracts
that consume them. It does **not** thereby establish a RelationContract ABI,
relation denotation, application statement, relation completeness, protocol
binding, relation satisfaction, witness correctness, or source-compiler
correctness. Any rule that depends on an external relation fact, payload
interpretation, or size bound must receive that fact through an explicit
admitted premise; it may never infer it from a digest-shaped anchor alone.

`B_M` is a finite set of identity-bearing `MaterialBinding` edges:

```text
ValueRef         = canonical event/result port in this artifact
MaterialRef      = sha256:<hex> semantic reference
MaterialBinding  = ValueRef -> MaterialRef
```

`ValueRef` identifies a local SSA producer by canonical position, not by an
author label. `MaterialRef` is stable across composition and is the namespace
claim anchors inhabit. In the v0 profile `B_M` is a partial function and is
reverse-injective inside one sealed artifact: one local value has at most one
material reference and distinct local producers cannot assert the same
material reference. Every edge must be consumed by a material attachment in
an actual reduction or discharge, and every material attachment that requires
a binding must resolve one exact edge. Link
preserves `MaterialRef` and reindexes only `ValueRef`; an alias requires a
future identity-bearing, independently checked `MaterialAlias` edge. No alias
variant exists in the canonical encoding. These edges prove declared reference equality only, not
external authorization or runtime-byte correspondence.

## 2. Binding times

Three stages are load-bearing for identity:

```text
seal time         everything in P            (this document)
realization time  backend/library/layout     (oir-realize and below)
instance time     public values, proof bytes, sampled challenges
```

Seal-time semantics MUST NOT depend on later-stage values; realization
MUST NOT depend on instance values. A field whose change alters the
accepted statement, transcript bytes, proof ABI, challenge authority,
claim flow, or decision is seal-time (identity-bearing) by definition.

## 3. Well-formedness — WF(P)

WF is decidable structure checking:

1. every value use is at a position after its introduction;
2. reduction bodies are pairwise disjoint subsets of E;
3. every claim/object/check/challenge/anchor reference resolves;
4. descriptors are canonically encodable over the fixed **encoding
   domain**: strings are printable ASCII (0x20–0x7E); integers are
   signed-64-bit-representable; larger or fractional numerics are
   decimal strings; floats are unrepresentable; each descriptor tree
   nests at most 64 levels from its own root, so the judgment is
   total — hostile nesting exhausts a counter, never an
   implementation. A domain violation is a seal error, and every
   reference implementation MUST reject it identically — the enforced
   domain, not encoder agreement, is the cross-implementation
   byte-parity argument;
5. `decision` is ≤-maximal if present;
6. challenge origins are well-founded (project/derive chains terminate
   at fresh or imported);
7. challenge domains are pairwise distinct within the container (carrier
   zkc-E216): a domain namespaces the transcript squeeze, so two
   challenges sharing one squeeze from the same framing and the Binding
   Lemma's injectivity (§13(e)) fails. This is also the base judgment a
   composite spine inherits under §5.4;
8. every claim profile, check contract, reduction contract, and terminal rule
   resolves through the sealed `ProtocolVocabulary`; every transitive
   cross-reference resolves to the content pinned by that same table;
9. every claim's anchors agree exactly with its resolved profile;
10. every check's mode, static parameters, semantic arguments, operand
    classes, and unique operand segmentation agree exactly with its contract;
11. every `MaterialBinding` has a canonical local `ValueRef`, a digest-shaped
    `MaterialRef`, and satisfies the partial-function and reverse-injectivity
    constraints of §1.6; and
12. author labels used to select claims, checks, rules, or producers are
    unique where resolved and never substitute for canonical references.

## 4. Claim linearity — LIN(C)

The claim-flow graph has claim nodes C and transformer nodes R, with
an edge claim→transformer for each consumption and transformer→claim
for each production.

**LIN(C)** holds iff:

1. every claim has exactly one producing transformer and exactly one
   consuming transformer (sources produce only, sinks consume only);
2. the graph is directed-acyclic (no claim justifies itself; the
   *undirected* diamond — one claim split, both halves folded by a
   later batch reduction — is legitimate);
3. every sink kind used is permitted by the active SealPolicy;
4. multiplicities (split/batch/fold/aggregate) are exactly the
   declared reduction-contract signatures — no implicit duplication.

The discipline is **linear** in the standard sense — neither
weakening nor contraction as structural rules
([Gir87/Wad90/Wal05](https://mitpress.mit.edu/9780262162289/advanced-topics-in-types-and-programming-languages/))
— with both rules internalized as explicit, policy-gated operations:
sinks are weakening-as-operation, declared split/batch contracts are
contraction-as-operation. Conditions 1, 2, and 4 are exactly the
well-formedness of a **string diagram**: a LIN-satisfying claim graph
is a morphism of the free symmetric monoidal category generated by
**claim descriptors** (objects) and transformer contracts (generators),
and its
denotation is a **reduction of knowledge** from the tensor of
source-introduced relations to the tensor of sink relations, composed
by the sequential and parallel composition theorems of
[KP23](https://eprint.iacr.org/2022/009) (cited). This composition
structure is what §9's budget arithmetic walks. J2 is LIN: "no claim
silently dropped, duplicated, or discharged twice" is not a rule list
but the definition of a well-formed linear flow. Single-use SSA
values are the carrier realization (carrier.md §4).

The objects are **descriptors**, not profiles. An earlier
revision said profiles, and with profiles as the generating objects the
wires carry only a name: one anchorless profile is one object, and
every arrow out of it composes with every arrow into it. Inside one
artifact the distinction is definitional — the consumed claim *is* the
produced SSA value, so its descriptor is shared and LIN condition 1
makes it unique — but it is load-bearing at two places. `link` fuses a
producer export with a consumer source only on equal
`(profile, anchors)` (boundaries.md §3, item 4), where SSA does not apply;
and §4.1 condition 1 pins the *consumed* profile while condition 5 pins
the *produced* descriptor, so the two conditions type the same wire at
different strengths. A profile whose anchors do not distinguish its
instances is therefore a hazard at the link boundary rather than merely
an uninformative name.

### 4.1 Exact local reduction closure — ReductionClosureOK(P)

For every reduction `q`, let `rc` be the exact admitted
`ReductionContract` selected by `contract`, and let
`select_q` map each contract-owned body-check role to one check in `K`.
`ReductionClosureOK(P)` holds iff:

1. consumed claim profiles, dependency slots and classes, message-role
   membership, challenge scalar/vector multiplicity, round structure, instance
   parameter names and sorts, and produced claim profiles agree exactly with
   `rc`;
2. `select_q` is total and exact on `rc.checks`, with no extra role, and each
   selected event has the required `CheckContract`, uniquely solved operand
   layout, exact static parameters, and (for transparent checks) the exact
   normalized predicate fixed by its slot;
3. every contract attachment resolves its source and target and proves the
   stated relation. `value_identity` compares the local SSA value directly;
   material-reference relations resolve the explicit `MaterialBinding` edges
   they require. A check may not justify unrelated reductions. The sole reuse
   exception is the terminal rule for this exact contract and output position,
   which independently re-establishes its own judgment over the same check;
4. every material constraint compares two expressions of the same static sort
   and evaluates equal; and
5. each positional output constructor evaluates to the exact result profile and
   anchor dictionary authored in `out_anchors`. Authored anchors are assertions,
   not semantic authority.

Contract expressions inhabit one closed many-sorted free algebra. The sorts are
`Ref`, `Refs`, `Claim`, `Claims`, and `Atom`; leaves are literal references,
input anchors/descriptors, dependencies, messages, and typed instance
parameters. Vector constructors use explicit `operand` or
`canonical_unique` order. The only general constructor computes:

```text
SHA256("zkc/material-expr\n" ||
       canonical(["construct", tag, typed_evaluated_arguments]))
```

The algebra has no arithmetic, branching, loops, foreign callbacks, carrier
positions, or protocol-name dispatch. Dependencies and messages become stable
semantic references only through explicit material bindings, except that a
`value_identity` attachment is deliberately a local SSA judgment. Thus link
may reindex local values without changing constructed semantic references.

This judgment establishes the admitted structural local implication from the
exact input descriptors and selected verifier checks to the exact output
descriptors. It does not execute an opaque check, prove an imported relation,
or validate a backend implementation.

### 4.2 Typed terminal closure — TerminalClosureOK(P)

For each discharge `d` consuming claim `c`, let `r` be its resolved
check-backed `TerminalRule` and let `select_d` map every terminal role of `r`
to one check in `K`. `TerminalClosureOK(P)` holds iff all of the following are
true:

1. `c`'s descriptor matches `r.consumed_claim_pattern` exactly, including the
   descriptor profile. If `r` carries a producer pattern, the canonical
   producer of `c` is a reduction citing the exact contract id and digest and
   the exact output position named by that
   pattern. Any producer-input, dependency, or message source used below must
   then resolve through that matched reduction instance and contract.
2. `select_d` is total on the rule's role set and injective; it has no extra
   roles. Each selected check resolves to the exact `CheckContract` required
   by its role. Across the artifact, one check is selected by at most one
   discharge, except for a check selected by the matched producer reduction
   itself; that exact producer-output reuse is adjudicated jointly by the two
   closure judgments and no other reuse is permitted.
3. The rule covers every consumed-claim anchor at least once and every selected
   check semantic-argument role exactly once. One anchor may legitimately feed
   distinct required targets; check targets remain linear. A targeted check
   operand role is constrained at most once, and a byte-identical attachment
   may not repeat. A missing anchor or semantic argument, or a duplicate target,
   refuses.
4. Every attachment source resolves from closed canonical structure: a claim
   anchor; one producer-input anchor at a declared input index; a vector of one
   anchor over all producer inputs ordered by canonical descriptor bytes; the
   full producer-input descriptors in that same order; one producer dependency
   value; or one producer message value at a declared occurrence. Every target
   resolves to one selected check's semantic argument or typed operand role.
5. Every attachment relation is one of the fixed the canonical encoding relations:
   `semantic_parameter`, `material_ref_equality`, `value_identity`,
   `material_ref_vector_equality`, `common_material_ref_equality`, or
   `descriptor_digest`.
   Equality through a binding resolves the exact `(ValueRef, MaterialRef)` edge
   in `B_M`; comparing author labels or coincident digest-shaped strings is not
   a substitute. `descriptor_digest` is exactly the `claim_vector` helper of
   §1.3 over the matched producer's full input descriptors; duplicate canonical
   descriptor bytes refuse before the digest is compared.
6. For each transparent terminal role, normalizing the selected check's input
   leaves to the contract's unique operand roles yields exactly the closed
   predicate stored in the rule. Every transparent role has one predicate;
   omission is not an opt-out. Opaque roles are matched by contract and
   attachments but their predicate implementations are not executed by this
   judgment.
7. Across ReductionClosureOK and TerminalClosureOK, every edge in `B_M` is used
   by at least one successful material attachment, and every material
   attachment that requires a binding uses one. Unknown rules, contracts,
   profiles, producer revisions, roles, attachment constructors, ambiguous
   segmentations, stale content, and failed predicates refuse.

The judgment establishes a typed implication edge from the exact consumed
claim descriptor to the exact propositions denoted by the selected checks. It
does **not** establish that an opaque predicate is true, that relation payload
bytes satisfy an imported relation, that a material assignment was authorized,
or that a backend checked the referenced runtime bytes. Those are separate
future judgments, not residual premises silently discharged here.

## 5. Challenge binding — BIND(χ)

### 5.1 Prefix satisfaction

For every challenge c and every use of c with requirement set P_req:

```text
∀ e ∈ P_req :  e ≤ pos(c)  ∧  e ∈ A
```

Prefix satisfaction is precedence-plus-absorption on the spine.
There is no other prefix fact language. Uses of projected/derived
challenges are judged at the source capability's `pos` (§1.5).

### 5.2 Requirement generation

For a challenge consumed by a reduction, `P_req` is **generated** from the
reduction contract's declared **round structure** — the assignment of the
reduction's message slots and challenges to rounds. This is the shape view of
the same contract whose checks, constraints, and outputs establish the local
implication under §4.1. The contract declares no security theorem; the reduce
names no theorem; a rule's quantitative parameters attach to the contract's
rounds at derivation, through a binding whose protocol anchor is that exact
contract.

```text
P_req(c_i) ⊇ statement bindings ∪ messages of rounds ≤ i
            ∪ {c_1, …, c_{i−1}}
```

per the contract's transcript shape. Hand-declared entries may extend
the generated set, never replace it. A contract whose round assignment
would leave its own round's messages out of `P_req` is ill-formed at
**vocabulary admission** — completeness is reviewed once, when the
shape is admitted, not re-established per protocol.

The unification is deliberate: pricing facts and binding facts are
one declaration, so they cannot disagree, and hand-enumeration of
prefix facts — the demonstrated error surface (a batching challenge
derived before the opening proofs it must bind:
[the Last Challenge Attack](https://eprint.iacr.org/2024/398)) —
is gone: that spine fails §5.1 against the generated requirements.
Note what generation does *not* claim: a message may legitimately
follow the challenge of its reduction (Schnorr's response follows c;
that is the round structure, not a violation) — which is why no
spine-local dataflow rule can replace contract knowledge.

Challenge uses outside any reduction contract carry hand-declared `P_req`;
whether such uses are permitted at all is a SealPolicy fact.

### 5.3 Structural defaults

Two defaults of the same shape — a hard rule with scoped, cited
relaxation; a relaxation is a soundness claim, discharged by a
derivation under §9's boundary, never a structural default:

- **Unabsorbed material.** A slot may be declared unabsorbed
  (e ∉ A): the verifier reads it without binding it into the
  transcript. Default: an unabsorbed slot MUST NOT precede any
  challenge event in ≤ (the generalized Frozen-Heart condition; v0's
  E212). In the canonical transcript order the default already covers
  FRI's query openings — authentication paths follow every challenge,
  bound through the absorbed roots, so no relaxation is spent on them.
  The relaxation instance exists for a protocol that streams openings
  earlier: the rule admitting it cites the binding argument
  (`soundness.md`).
- **Statement binding.** A spine carries a **segment
  decomposition** — contiguous runs of E in ≤ order; a standalone
  protocol is one segment, and link concatenates its operands'
  segments (§5.4). Every public_bind MUST precede the first
  challenge event OF ITS OWN SEGMENT. The Fiat-Shamir theorems hash
  the statement under every challenge OF THE PROTOCOL BEING
  TRANSFORMED ([AFK Thm 4](https://eprint.iacr.org/2021/1377);
  [DMWG23 Def 3](https://eprint.iacr.org/2023/691)'s strong FS; the
  [CFRG draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/)'s
  instance absorption at initialization) — a theorem-interface
  requirement independent of any dataflow, so it stands even where no
  check consumes the statement together with a challenge. The
  per-segment scope is what those interfaces actually demand of a
  composite: the round-by-round bounds are per-query with adaptive content
  (the shapes of CCHLRR §5.2 and ethSTARK Thm 6), so a later segment's
  statement entering after an earlier
  segment's challenges leaves each segment's doomed-state argument
  intact, and cross-segment dependence is excluded by the claim
  graph (a reduction's rounds and generated requirements are its own
  segment's events, and claim flow at link runs producer → consumer,
  never backwards). The SEAM — one sponge instantiating each
  segment's oracle at prefix-disjoint states — is a stated
  obligation (`fs_segment_seam`, one per splice) recorded on the
  composite artifact until a composition rule bounds it
  (cited/deferred; the RT-A track's interface). Segmentation is
  judgment-bearing and
  therefore identity-bearing: the canonical form carries it
  (additively — a one-segment artifact encodes as before). The
  Frozen-Heart default above deliberately stays GLOBAL: no theorem
  interface pressures a per-segment relaxation, and unabsorbed
  material is invisible to every later challenge regardless of
  segment. Any within-segment relaxation requires an admitted vocabulary rule
  and the theorem interface that justifies it; it is never inferred from an
  event label or implementation behavior.

### 5.4 Imported challenges and joint state (composition obligations)

A challenge with origin `imported(ref)` may carry P_req entries that
reference events outside E (they live in the artifact the challenge
is imported from — the cross-shard and recursion-aggregation cases).
Such entries are not checkable at standalone seal. Sealing records
them as **composition obligations**: obligations discharged at the
boundary that materializes the composite spine (link or aggregation),
where precedence-plus-absorption is re-checked over the composed order.
Under a closed-proof policy, unresolved composition obligations fail
the seal; policies that permit them expose the obligation set on the
sealed artifact, where a later derivation must discharge it. This is the
fail-closed rule for cross-shard and recursion-aggregation challenge
dependencies.

Composition also shares transcript state. When link or aggregation
materializes a composite spine, challenge domains `D` MUST be
re-derived and domain disjointness re-judged over the composite —
the joint-state discipline
([CR03](https://eprint.iacr.org/2002/047)). Disjointness is a base
seal judgment (challenge domains are pairwise distinct within any
container, carrier zkc-E216), which the composite inherits when it is
re-sealed; face prefixing makes the re-derived domains syntactically
disjoint, and link additionally refuses face prefixes where one is a
dotted prefix of the other (the only way two prefixed domain spaces
could still collide, carrier zkc-E703). The namespace is
per-boundary: identity is a seal product, so an open protocol has no artifact
identity to namespace by. **Link** (open × open) prefixes
domains by its face names — deterministic authored inputs, present
in the composite's content, collision-fatal — while **aggregation**
of sealed children namespaces by the child-artifact identity, which
exists there. Two independently sealed, separately BIND-clean
artifacts may still collide in `D` or share a sponge once composed;
the composing boundary is where that is caught (boundaries.md §3).

### 5.5 What BIND means

BIND is the structural half of Fiat-Shamir admissibility: it
guarantees that when challenges are instantiated by hashing (§9,
Binding Lemma), each challenge is a function of everything it is
required to bind, and of nothing the adversary may withhold from the
transcript. With requirement generation (§5.2) and the structural
defaults (§5.3), the weak-FS attack corpus — statement not absorbed
[DMWG23]; commitment absorbed after its challenge [Frozen Heart];
opening proofs absorbed after the batching challenge
[Last Challenge]; prover-controlled values unbound before challenge
derivation (the 2026 zkVM corpus); cross-artifact domain collision
[CR03] — falls in BIND's **structural** rejection set, without
per-protocol bespoke verifier branches. The corpus is the negative
test-suite obligation for any kernel implementation
(checked-obligation grade).

## 6. Projection coverage — COV_obl(E) and COV_realized(E, k)

Coverage is two judgments at two boundaries: the seal derives what
every endpoint owes (obligations), and each projection proves that
one endpoint paid exactly that (realization). A sealed artifact
carries obligations, never realization claims.

### 6.1 Obligation coverage — COV_obl(E) (seal)

Every semantic event derives one **projection obligation**
`(event_ref, route_class, discharge)` under a closed route
vocabulary:

```text
executable | fused_executable | conformance_row |
residual | assumption | export | analysis_only
```

`executable` is derived by default; every other class requires
explicit declaration with route/evidence refs and policy admission —
declaration surfaces are a named extension (§12; fused events
additionally declare the covered event set and the conformance rule
justifying the fusion, and the v0 fusion-rule vocabulary is empty).
The **discharge kind** — the endpoint-effect family that must realize
the event — is a function of the event's already-encoded facts, one
rule per event kind: a seal-stage binding realizes as
constant-plus-absorb, an instance binding as argument-plus-absorb, a
slot as read (plus absorb when absorbed), a scalar challenge as a
scalar squeeze, a vector challenge as one counted vector squeeze, a
transparent check as the assert over its lowered algebra, an opaque
check as a registered call. Derivability is the judgment: COV_obl
fails exactly where a derivation input is missing (an unresolved
codec, an unresolved or under-fed check contract, an expression outside
the grammar, a malformed vector mode). Unknown route classes,
discharge kinds, or event kinds fail closed.

Obligations are a **derived view** (§11): the table is a tabulation
of E, κ, and the resolved vocabulary, and never enters canonical(P) —
identity covers the events, policy, and refs the derivation reads,
nothing realization-side.

### 6.2 Realization coverage — COV_realized(E, k) (project)

For an endpoint kind k, the projected program realizes the
obligations **exactly**: set equality between obligations and covered
event positions, in both directions — every executable obligation is
covered by emitted effects of its discharge kind's families, and
every position appearing in any emitted op's provenance is a real
event position carried by a family its obligation licenses (no
phantom coverage; fusion only under a cited rule); covering effects
are reachable from the projected endpoint body; non-executable
obligations route to the artifact's route attributes by ref. An
obligation whose discharge kind is outside k's realization vocabulary
is a named refusal (`unsupported`), never a silent drop.

COV_obl is what makes J5 *checkable* at the pir-project boundary;
COV_realized is J5's verdict for one endpoint. The split assigns obligations
to the seal and realization to projection.

## 7. The seal judgment

```text
seal(P, Envs)
  = WF(P) ∧ LIN(C) ∧ BIND(χ) ∧ COV_obl(E)
      ∧ ReductionClosureOK(P)
      ∧ TerminalClosureOK(P)                  — fail closed
```

`Envs` is the ProtocolVocabulary and construction-profile environment.
`P` already carries its selected construction profile and SealPolicy; they are
identity-bearing protocol content rather than additional call arguments.

Products: the sealed artifact (P plus tabulations of E, χ, C, K — the
tables are *views*, §11, not additional truth) and the projection
obligation table (a derived view, §11, recomputable by any consumer).
Projection proves COV_realized per
endpoint (§6.2); a sealed artifact carries obligations, never
realization claims. A failed seal produces
diagnostics only. Sealed artifacts are immutable; a semantic change is
a new artifact.

`ProtocolVocabulary` supplies the six jointly admitted v4 sections. Successful
seal cross-admits their references and writes exactly the transitive cited
subset and its content digests into the artifact. The construction-profile
environment resolves the selected sponge, codecs, sampling, and IV policy. The
environments themselves are not identified. Anchor values remain opaque references:
seal does not load a relation payload, execute its predicate, or check witness
satisfaction. A future relation adapter may validate an external payload and
produce versioned interface facts or certificates before seal, but those
checks are not hidden premises of either closure judgment and are not supplied
by opaque anchors.

**SealPolicy** is the identity-bearing mode of the artifact. It defines the
permitted sink kinds, allowed check modes, allowed body policies,
composition-obligation stance, and minimum conformance tier. The kernel fixes
that LIN condition 3 and COV_obl's route declarations consult this policy. An
artifact whose policy permits non-discharge sinks MUST NOT present as a closed
proof artifact.

## 8. Identity, equivalence, legality

- **Identity.** id_kind(P) = H(tag_kind ‖ canonical(P)) over exactly
  the kernel object (§1) plus policy and profile; never over evidence
  metadata, backend names, calibrations, or derived security judgments.
  `tag_kind` is a fixed ASCII domain tag (`"zkc/pir\n"` for sealed
  protocols, `"zkc/oir\n"` for endpoint artifacts), so no zkc
  identity is reinterpretable across kinds or as another system's
  digest of the same bytes (tagged-hash practice:
  [BIP-340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki),
  RFC 6962). References to identities — citations, derivation
  subjects, registry keys — carry the algorithm-prefixed form
  `sha256:<hex>`. The byte encoding is a carrier responsibility; the
  identity *set*, the domain tags, and the encoding domain (§3, item 4) are
  fixed here (J3).
- **Vocabulary citations resolve to content.** The protocol-semantic entries
  that jointly determine WF, LIN, BIND, `ReductionClosureOK`, and
  `TerminalClosureOK` — claim profiles, check contracts, reduction contracts,
  and terminal rules — are one
  cross-admitted `ProtocolVocabulary`. Operations cite entry ids. Seal computes
  the transitive cited closure and writes one resolved table of `(section, id,
  content digest)` into the identified object; that sealed table is the sole
  digest authority for protocol-vocabulary content. Operations do not repeat a
  check contract, profile, reduction contract, or rule digest that could
  disagree with it.
  Changing any cited entry changes the protocol identity; uncited environment
  entries do not.

  A reduction cites its **ReductionContract** only. The contract carries the
  reduction's shape and its exact local implication; it carries no security
  price, and the artifact names no theorem. Which theorem applies to an
  occurrence is a property of a derivation, selected by a signature, a binding,
  and a plan (`soundness.md` §5), so it is outside protocol identity by the
  binding-time rule of §2. Construction-profile entries keep their own resolved
  section, because a codec's decode width is transcript bytes and proof ABI.

- **Equivalence.** P ≅ P' iff canonical(P) = canonical(P') after
  id-stable renaming; ≅ is the trivial kernel equivalence. Coarser
  semantic equivalences (e.g. reorderings proven observation-
  equivalent) are claims of a separate checked judgment
  (`compiler.md`), not kernel judgments.
- **Transformation legality (⊑).** A rewrite P → P' of sealed
  material is judged by the Compiler Core (`compiler.md` §7.2): every
  application runs its family's `recognize → realize → check`
  sequence against the actual authenticated predecessor and successor,
  so legality is *defined* by the checked transform trace — not by
  semantics preservation alone. Structural legality does not by itself
  establish robust preservation, certificate translation or witnessing
  compilation, budget-gated numeric compilation (including FHE), or
  adversary-resource relativization; each requires its own checked judgment.
  For reduce-producing transforms, claim
  correspondence is structural — descriptor-digest multisets plus
  the new reduce's consumption — so no cross-artifact claim matching
  is required. The quantitative side is the typed bound-expression
  relation `candidate ≤ checked source baseline + ceiling`
  (`compiler.md` §7.3) over the security judgments `soundness.md`
  derives, and obligations may not grow. The kernel contributes the
  objects (ids, tables, claim flow) that make the comparison
  well-defined (J4).
- **Re-checkability.** The six seal judgments are deterministic
  re-checks once the artifact-pinned vocabulary content and the cited
  predicate-spec preimages are supplied. The artifact's sealed table is
  the sole digest authority for that content. A consumer re-derives each
  predicate-spec key, resolves the pinned entrypoint, and checks exact
  structural ABI equality before reconstructing the judgments, so it
  needs no registry. This proves proposition identity, not
  opaque-predicate execution.

## 9. Security accounting — the boundary to the Soundness Kernel

### 9.1 The kernel's contribution — authenticated structural facts

The kernel does not prove protocol security and does not name a theorem. A
theorem citation is not protocol content: a conditional security judgment is
derived *about* a sealed protocol by the calculus in
[`soundness.md`](soundness.md), from an explicit signature and an explicit
derivation plan supplied by the caller. The Protocol Kernel's contribution is the
authenticated structural facts that a rule binding may project — reduction
contracts and their round structure, challenge capabilities and their spaces
and counts, material anchors and their transcript positions, and the sealed
identity that scopes them all.

Two consequences are load-bearing and stated here because they constrain the
carrier rather than the calculus. First, §5.2 generates a challenge's binding
requirements from the same contract round structure a rule reads for its
quantitative parameters, so binding facts and analysis facts cannot disagree —
they have one source. Second, a quantity a rule reads must be verified by use:
it is consumed by the verifier from sealed structure, never supplied as a
producer annotation. The one admitted exception is an analysis parameter the
theorem quantifies over, which may be a declared reduce parameter guarded by a
machine condition, sound because the bound holds for every valid choice.

The theorem statements, formulas, parameter windows, and citations this section
previously carried are declaration content. They live with the rules and their
annotations in the signature, and the reference list below is retained so no
citation is lost with the framing.

### 9.2 Binding Lemma (proof obligation — the zkc theorem)

The lemma has three parts; v0.1 conflated the first with the third
("is a function of the prefix" does not imply "binds" — a constant is
also a function of the prefix).

> In a sealed P, instantiate challenges by the construction profile's
> transcript hash over the ≤-ordered absorbed events. Then:
>
> **(a-determinism)** the instantiated value of every challenge c
> depends on the absorbed prefix {e ∈ A : e ≤ pos(c)} and on nothing
> else;
>
> **(a-injectivity)** the absorbed prefix is injectively recoverable
> from the hash input — distinct prefixes present distinct inputs
> (prefix-free framing, §13(e));
>
> **(b-binding, bounded)** replacing fresh sampling by this
> instantiation preserves soundness/knowledge up to the loss stated by
> the Fiat-Shamir rule a derivation applies (`soundness.md`): the
> fresh-sampling ↦ transcript-hash hop, with BIND supplying the
> hypothesis that every satisfied requirement precedes its challenge
> in the absorbed order.

Status: **stated; proof obligation.** (a-determinism) is syntactic —
induction over the spine (in the runner reading, an
interpretation-fusion argument); its negative half ("nothing else")
is a noninterference statement about the *projected program*,
discharged at the conformance tiers (boundaries.md §5) — which is why
it is not a fifth seal judgment. (a-injectivity) is an encoding lemma
against the carrier's framing. (b) is a game hop whose bound is
supplied by the corresponding rule declaration in the Soundness Kernel
signature (`soundness.md`); its statement is aligned with the duplex-sponge
transformation's theorem shape [Chiesa–Orrù Thm 1] so that eventual
mechanization (ArkLib/VCVio are the target vehicles) composes with
the existing formal corpus rather than beside it. Per-profile
hypothesis to record: the **chain shape** — hashing the ≤-ordered
absorbed events themselves (messages-in-chain, zkc's default) needs
plain RBR; a profile that chains only roots/commitments needs strong
RBR ([CMS19 §8.6](https://eprint.iacr.org/2019/834)).

### 9.3 Composition caveat (justified deferral)

The literature's RBR-composition results and ArkLib's generic
theorems cover **sequential** composition of reductions. Kernel
bodies MAY interleave (§1.4), and shared challenges MAY batch (§1.5)
— both exceed off-the-shelf sequential composition. Until a
composition theorem covering the interleaved/shared cases is proved or
cited, dispatch MUST treat interleaved and challenge-sharing reduction
groups as a single composite application (no per-reduction
decomposition of their soundness contribution) — or refuse to price
them.

Three cases remain distinct because their theorem interfaces differ.

**Shared-challenge repetition cannot be priced componentwise by default.** Generic
per-component pricing of a *t*-fold parallel repetition is not merely
unproven but false in general: the FS transformation of such a
repetition admits a dedicated attack far below the naive bound
([AFK Thm 5](https://eprint.iacr.org/2021/1377)). Absent an admitted theorem
covering the exact shared group, dispatch treats it as one composite application
or refuses to price it.

**That citation does not reach every fan-in shape.** A theorem whose
*statement* spans N distinct members — a lookup bus, a grand product,
a batch over an unequal member set — is not a repetition of one
protocol and has no per-component error multiplication, so AFK is
silent about it. This is an **absence**, not a counterexample: a rule may price
such a group only when its conclusion and premises bind the exact member vector
and joint transcript structure. The absence of such a rule is never evidence
for a decomposition.

**Structural interleaving does not license per-reduction pricing.** The kernel
allows disjoint reduction bodies to interleave, but a soundness derivation MUST
apply a theorem whose subject covers the entire interleaved group, treat that
group as one composite application, or refuse to price it. A sequential rule
may decompose occurrences only after its own guards establish the required
noninterleaving span and challenge separation. Carrier acceptance or tool
output cannot weaken this requirement.

Refinements enter as ordinary rule declarations. Shared-challenge conjunction
of special-sound subprotocols with error equal to the maximum of the component
errors ([ProtoStar Lem 7](https://eprint.iacr.org/2023/620)) is one template;
batching that preserves special soundness
([KLPS26](https://eprint.iacr.org/2026/326)) is another. Each admitted rule must
bind the exact contracts, occurrences, transcript relationships, and
assumptions it covers. Everything outside that interface remains a surfaced
conditional antecedent or an unpriced group.

## 10. Boundary signatures

Details belong to `boundaries.md`; the kernel fixes signatures and
totality facts.

```text
seal    : OpenP × Envs                       → Option⟨SealedP⟩
decode  : Artifact                       → Option⟨DecodedSealedP⟩
admit   : DecodedSealedP × Envs              → Option⟨AdmittedSealedP⟩
project : AdmittedSealedP × endpoint_kind    → Option⟨OIRArtifact⟩
link    : OpenP × OpenP × faces × Envs       → Option⟨OpenP⟩
descend : SealedP(verifier endpoint, realized) → RelationPayload'
```

`descend` is a reserved research boundary. The signature records the required
direction of information flow but does not itself admit a carrier form,
projection rule, or security theorem. Those require an explicit versioned
recursion/composition transition under `boundaries.md`.

- `project` on the verifier endpoint of a public-coin sealed P is
  **total on COV_obl-satisfying artifacts whose obligations' discharge
  kinds lie in the endpoint's realization vocabulary**
  (knowledge-of-choice vanishes
  under public coins — protocols are selection-free, so endpoint
  projection needs no merging or pruning;
  [CM16](https://www.fabriziomontesi.com/files/cm16_facs.pdf), cited);
  outside that vocabulary, refusal is named (`unsupported`), never
  silent.
  Projection correctness **factors**: an operational correspondence —
  the endpoint event log is complete and sound against the sealed
  spine (the endpoint-projection theorem shape; the Tier-2
  conformance target) — composed with the FS interpretation priced by
  §9 (the Binding Lemma). The two halves have different proof tools
  and MUST NOT be merged into one statement.
- `link` composes claim flows and splices spines; profile merge
  conflicts are ill-typed; composition obligations discharge here,
  and challenge domains are re-derived under the joint-state rule
  (§5.4).
- `descend` transfers claims across the verifier-as-relation boundary
  **by reference only** (artifact digest citation); assumption sets
  transfer explicitly. Recursion-gap visibility — heuristic RO
  instantiation inside circuits, and more generally statement classes
  able to encode the construction profile's hash function, which
  defeat even full absorption
  ([KRS25](https://eprint.iacr.org/2025/118)) — is a derivation-side
  requirement (a machine condition or an explicit premise in the
  Soundness Kernel signature), not a kernel judgment (deferred;
  candidate research output).

## 11. Derived views (definitions, not truth)

- **Lifecycle** of a claim is a graph query:
  `live` = produced ∧ ¬consumed (never true in a sealed closed-proof
  artifact); `reduced` = consumed by a reduction;
  `deferred`/`accumulated` = consumed by a carrier-transfer reduction;
  `discharged`/`exported`/`assumed`/`residual` = consumed by that sink.
- **Tables** (challenge, event, claim, check, projection) are
  tabulations of χ, E, C, K and COV routes. A carrier MAY materialize
  them; if it does, table–body agreement is a WF check of the
  carrier, and the kernel object remains the single source of truth.

## 12. Vocabulary quarantine and named extensions

Provisional vocabularies (in `vocabularies.md`, with admission rules):
event subkinds; protocol-vocabulary claim profiles, check contracts,
reduction contracts, and terminal rules; reduction families and body policies;
object state alphabets; policy names; construction profiles (κ);
endpoint kinds; admitted security notions and signature declarations.

Named extensions (not in the canonical encoding semantics; each enters only with explicit
kernel-level rules): transcript fork/join (par), dynamic instance
counts (runtime-N folding), partial-order spines, **declared
non-executable event routes** (the per-event route classes of §6.1
beyond `executable`, declared as an additive encoding section with
per-class route/evidence refs and policy admission; vocabularies.md
§4 carries the stub), subject- and relation-bound witness schemas,
anchored-material input verification, confidential input/run binding, a
vector-valued provider ABI, integrated witness generation, QROM rules,
interleaved-composition rules (lifting §9.3's
conservatism), a **zero-knowledge track** of the admitted notions
(simulation-error rules declared beside soundness/knowledge over the
same sealed quantities; additive hybrid composition; per-notion
derivation), **spine
synthesis** from an authored claim DAG (the
authoring frontend: BIND-constrained transcript scheduling),
**security-parameter synthesis** (inverse dispatch: choose parameters
by optimizing cost under the derived security bounds), and
**self-referential recursion identity** (IVC fixed points, where a
recursive claim's child digest is the containing protocol's own
identity).

Named non-goal: private-coin protocols. Verifier randomness that is
not transcript-derived has no χ origin and no Fiat-Shamir meaning in
this kernel; the kernel is public-coin by construction.

## 13. Carrier conformance

A carrier (the MLIR dialects, the encoder, the artifact format)
conforms iff it (a) represents the kernel object losslessly, (b)
  enforces WF/LIN/BIND/COV_obl/ReductionClosureOK/TerminalClosureOK verdicts
identically to the abstract
definitions and realizes COV_realized identically at its projection
boundary, (c) realizes canonical encoding such that id(P) is
carrier-independent, (d) preserves ≤-ordered absorption through
projection (the operational half of the Binding Lemma), and (e)
realizes injective, prefix-free framing of absorbed events in the
transcript-hash input — ambiguous framing voids Binding Lemma
(a-injectivity), independently of everything else being right. A
carrier choice that alters any judgment verdict is a kernel change,
not an implementation detail.

## References

- [BGTZ — On Soundness Notions for Interactive Oracle Proofs](https://eprint.iacr.org/2023/1256)
  (journal version: [J. Cryptology 2024](https://doi.org/10.1007/s00145-024-09520-7))
- [Hol19 — On Round-By-Round Soundness and State Restoration Attacks](https://eprint.iacr.org/2019/1261)
- [BCS16 — Interactive Oracle Proofs](https://eprint.iacr.org/2016/116)
- [CMS19 — Succinct Arguments in the Quantum Random Oracle Model](https://eprint.iacr.org/2019/834)
- [CCHLRR — Fiat-Shamir From Simpler Assumptions (eprint 2018/1004)](https://eprint.iacr.org/2018/1004)
  — the registry rows pin this 6-author eprint and its numbering
  (STOC 2019 merge, whose internal numbering differs:
  [CCHLRRW19 — Fiat-Shamir: From Practice to Theory](https://doi.org/10.1145/3313276.3316380))
- [AFK22 — Fiat-Shamir Transformation of Multi-Round Interactive Proofs](https://eprint.iacr.org/2021/1377)
  (journal version: [J. Cryptology 36(4), 2023](https://doi.org/10.1007/s00145-023-09478-y))
- [Chiesa–Orrù 2025 — A Fiat-Shamir Transformation From Duplex Sponges (TCC 2025)](https://eprint.iacr.org/2025/536)
  (standards-track companion: [draft-irtf-cfrg-fiat-shamir](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/))
- [DMWG23 — Weak Fiat-Shamir Attacks on Modern Proof Systems](https://eprint.iacr.org/2023/691)
  (Dao–Miller–Wright–Grubbs, IEEE S&P 2023)
- [BGKTTZ23 — Fiat-Shamir Security of FRI and Related SNARKs](https://eprint.iacr.org/2023/1071)
- [BCI+20 — Proximity Gaps for Reed–Solomon Codes](https://eprint.iacr.org/2020/654)
- [BCHKS25 — On Proximity Gaps for Reed–Solomon Codes](https://eprint.iacr.org/2025/2055)
  (ECCC mirror: [TR25-169](https://eccc.weizmann.ac.il/report/2025/169/))
- [ethSTARK Documentation v1.2](https://eprint.iacr.org/2021/582)
  (Thm 6: grinding scales per-round RBR error)
- [LPS24 — the ARSDH assumption](https://eprint.iacr.org/2024/173)
- [Last Challenge Attack](https://eprint.iacr.org/2024/398)
- [KRS25 — How to Prove False Statements](https://eprint.iacr.org/2025/118)
- [ProtoStar](https://eprint.iacr.org/2023/620)
- [KLPS26 — Special Soundness and Binding Properties](https://eprint.iacr.org/2026/326)
- [KP23 — Reductions of Knowledge](https://eprint.iacr.org/2022/009)
- [CR03 — Universal Composition with Joint State](https://eprint.iacr.org/2002/047)
- [NS02 — Proof-Carrying Code with Untrusted Proof Rules](https://people.eecs.berkeley.edu/~necula/Papers/sfpol_isss02.pdf)
- [AB20 — Runners in Action](https://arxiv.org/abs/1910.11629)
- [VCVio — Verified Cryptography via Oracle Effects and Handlers](https://eprint.iacr.org/2026/899)
- [CM16 — A Core Model for Choreographic Programming](https://www.fabriziomontesi.com/files/cm16_facs.pdf)
- [ArkLib — Formally Verified Arguments of Knowledge in Lean](https://github.com/Verified-zkEVM/ArkLib)
