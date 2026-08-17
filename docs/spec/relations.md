# zkc Relations

Status: **canonical for the relation domain (2026-08-17).** Companion to
`vocabularies.md`, which reserved the `RelationContract` role this
document admits, and to the opacity rule of `kernel.md` §1.6: the
kernel authenticates claim profiles, anchor shape, and claim flow, and
treats every referenced relation payload as opaque. Any rule that
depends on an external relation fact receives it through an explicit
admitted premise; nothing here weakens that.

zkc consumes and binds relation artifacts; it does not compile relation
source. This document defines the object that makes the binding
sayable: what identifies a relation, how its interface is read, how its
public instance corresponds to a sealed protocol's statement, and —
with equal weight — which parts of that are computed, which are
cross-checked, and which are accepted on a named party's word.

## 1. The RelationContract document

A `RelationContract` is a post-seal, content-addressed registry entry,
envelope `zkc.relation_contract`. It describes the interface of one
relation and its correspondence to sealed protocols that cite that
relation through claim anchors.

**Identity impact.** A RelationContract is evidence-only relative to
every artifact it describes: attaching, removing, or revising a
contract moves no artifact identity, changes no transcript byte, and
alters no kernel judgment. Its own digest is identity-bearing content
exactly where another identity-bearing object pins it — the reserved
bounded artifact verification (`endpoints.md` §3.1) pins a child
relation-contract digest, and a correspondence judgment embeds the
digest of the contract it used.

**Semantic load.** The absence of a contract means only that every
relation fact a judgment needs arrives as a named assumption; the
presence of one conditions the correspondence judgment of §4 and
nothing else. Changing an entry's content moves its digest by
construction.

It is deliberately not a seal-time construct: the sealed artifact
already pins *which* relation (the anchors are inside its canonical
encoding), while the contract states *how that relation's interface is
read* — an external fact, entering through the admitted-premise channel
the kernel requires. A contract is attachable to an artifact sealed
before the contract existed; learning to read a relation better is not
a change to the protocol.

Two contracts may describe the same relation. They must agree with the
sealed anchor digests wherever they are checked against an artifact and
may differ in how much of the interface they read — a difference
visible in the obligations of every judgment that cites them, never
hidden. A contract cannot swap a sealed artifact's relation: the
anchors are sealed.

Entries are digested under the exact ASCII prefix
`"zkc/relation-contract\n"` over the entry's canonical JSON
(`carrier.md` §6's canonicalization). The registry map key is a lookup
handle and is not covered by the digest; no judgment resolves a
contract by name — consumption cites the digest. Loading is
fail-closed: unknown fields, missing required fields, and out-of-domain
values refuse with named errors.

## 2. Fields

The entry schema is closed. Required fields: `claim_profile`,
`relation_anchors`, `instance_anchors`, `format`, `identity`,
`instance_encoding`, `witness_ports`, `statement_correspondence`.
`declared_shape` is optional. No other field is admitted.

### 2.1 Identity

`identity` is an object carrying at least one of two primitives that
are never merged, because they are different kinds of trust:

- `content_digest` — a sha256 digest zkc computed over relation-artifact
  bytes it was handed. Its presence claims exactly: these bytes, this
  digest. It does not claim that those bytes are the relation the
  anchors name (§6).
- `attested_id` with `attestor` — an identifier some named external
  toolchain asserts denotes this relation (a verification-key digest, a
  program image id), and the name of the asserting party. Its presence
  claims exactly: this party says so.

A contract whose identity is attested-only contributes an assumption
naming the attestor to every judgment that reads it; when the attestor
is the contract's own author, the judgment says that too. An
`attested_id` is an external assertion, never a locally minted name.

### 2.2 Format

`format` names the closed reading form for the relation-artifact
bytes. The admitted set is exactly:

- `r1cs-bin-v1` — the iden3 R1CS binary format, version 1, read per §5.
- `opaque` — no reading form; every interface fact in this contract is
  declared, not read.

A format outside the set refuses. The set grows one admitted form at a
time; a name whose reading rules this document does not state is not
admitted. A format and an instance encoding are not independent: a form
that reads a field and a public arity from its header, as
`r1cs-bin-v1` does, admits only a `field_vector` instance, so the
declared field bounds the reader (§5) instead of leaving it unbounded.

### 2.3 Anchor partition

`claim_profile` is `{name, digest}` — the profile's name and its
content digest, so a vocabulary edit cannot change what a fixed
contract means. The correspondence judgment resolves the name in its
environment and refuses unless the admitted profile's content digest is
the pinned one; a pin that is only carried would state the guarantee
without providing it. The contract partitions that profile's anchors:

- `relation_anchors` — a map from anchor name to the `sha256:` value
  the contract is scoped to. One contract serves every artifact whose
  descriptor carries exactly these values at these names.
- `instance_anchors` — a list of distinct anchor names whose values vary
  per artifact and are checked against each artifact's descriptor by the
  correspondence judgment, never fixed by the contract.

The partition MUST cover the profile's anchor set exactly, and it MUST
equal the normative partition this document fixes per admitted
profile:

| Profile | Relation anchors | Instance anchors |
|---|---|---|
| `r1cs` | `a`, `b`, `c` | `public` |
| `opaque_relation` | `contract` | `statement` |

A contract disagreeing with this table refuses. Which anchors of a
profile are instance-varying is a fact about the profile, stated once
here; a profile admitted later arrives with its row. A relation anchor
whose value is a well-known degenerate digest (the digest of empty
input) makes the scope gate vacuous; the correspondence judgment
surfaces that as a named obligation rather than treating the gate as
met.

### 2.4 Public-instance encoding

`instance_encoding` states how the relation's public instance is
represented. There is no default; a contract that omits it refuses.
The admitted forms, discriminated by `kind`, are exactly:

- `field_vector` — an ordered vector of field elements. Carries
  `field_order` (exact decimal cardinality) and `arity` (element
  count). The shape of constraint-family relations.
- `opaque_bytes` — a byte stream the consuming verifier identifies
  through a digest. Carries `digest_function` from the closed set
  {`sha256`}; the hash choice is part of the interface, not a detail —
  two consumers assuming different functions over the same bytes
  disagree about which instance was proven.
- `commitment` — the instance is itself a commitment value. Carries
  `payload_class`, the sealed protocol's payload class of that value.
  The instance-side counterpart of the opaque witness port: in trace
  families the public statement can be a root binding the trace, and
  describing it as field elements or hashable bytes would misstate
  both.

### 2.5 Witness ports

`witness_ports` states the relation's private-input interface,
discriminated by `kind` — two forms, because the relation families
genuinely differ here and forcing one shape onto the other misdescribes
it:

- `enumerated` — `ports`, an ordered list of `{name, count}`, for
  relations whose witness is a declared variable range (constraint
  family). The counts total the relation's private-input arity.
- `opaque` — one `{name}` whose payload is the whole witness object
  (trace family, where the witness is the entire trace and no port
  list exists to declare).

Port names are the stable references later machinery cites — the
anchored-material operands of `endpoints.md` §6.2 and the construction
routes of `carrier.md` §4 consume these names when relation bytes and
witness objects reach prover fills. A contract declares ports; it does
not obligate any endpoint to consume them.

### 2.6 Statement correspondence

`statement_correspondence` is an ordered list mapping the relation's
public-instance positions to a sealed protocol's statement labels:
entry `i` is `{slot, label}` with the list in instance order. This is
the wiring between the two spellings of "the statement" that a sealed
artifact carries — the ordered, typed, transcript-absorbed
`statement_labels` and the opaque instance anchor — which no sealed
carrier relates in full ordered form.

The correspondence is the permutation: it does not have to be
order-preserving against the artifact's ABI, because relation instance
order (fixed by the format) and protocol absorption order (fixed by
the author) are independent. What disambiguates two contracts wiring
the same labels differently is the citation discipline — every
judgment names the contract digest it used.

Statement labels not named by any entry are permitted and remain
protocol-only public inputs (a protocol may bind sizes or context the
relation does not know). What each part establishes follows §3: that a
named label exists in the cited artifact's ABI is computed; that the
correspondence count equals the declared arity (for `field_vector`) is
cross-checked; that slot `i` *means* what the label suggests is
asserted, permanently, because no surveyed format authenticates names —
that assertion is the named assumption
`zkc.assume.statement_correspondence_wiring`. Where the sealed
artifact carries a `pir.material_bind` from a labelled statement value
to any anchor of this contract — instance anchors included, since a
statement anchor is exactly where a sealed binding grounds an instance
— the judgment checks that the bound value's label is one the
correspondence wires; a binding whose label the correspondence does not
wire refuses. A binding to an unlabelled value is reported as such and
grounds nothing.

### 2.7 Declared shape

`declared_shape` optionally carries relation-shape facts a soundness
rule reads, each landing as the existing assumption pattern until
bytes make it checkable: `constraint_count` (the number the assumption
`zkc.assume.constraint_count_matches_relation` prices — declared here
in a checkable place, cross-checked against the header's constraint
count when bytes are present, and still an assumption where no bytes
are).

## 3. Trust tiers — a mapping, not a taxonomy

Every fact a contract contributes lands in the obligation machinery
that already exists; this document adds no parallel trust vocabulary.
The two sides of every comparison are named structurally:
**contract-declared** (a field of this entry) and **byte-derived** (a
fact the reader computed from handed bytes) or **artifact-derived** (a
fact read from the sealed artifact). Three landing patterns cover
every field:

- **Computed.** A fact zkc derived from bytes or from the sealed
  artifact alone: a content digest it took, a header field the reader
  parsed, the presence of a statement label in a cited artifact's ABI.
  Lands as a machine-checked fact of the correspondence judgment.
- **Cross-checked.** A contract-declared value agrees with a
  byte-derived or artifact-derived one. Lands as a machine-decided
  consistency condition with the semantics stated exactly:
  **agreement is consistency, not truth.** Cross-checks catch
  mistakes, not a party checking itself; independence of the two
  sources is never established, and both can be wrong together. No
  output of this judgment claims otherwise.
- **Asserted.** What a slot means; that the relation is not
  underconstrained; that its witness generator is correct; provenance.
  Lands as a named assumption carried by every judgment that reads the
  contract — the pattern `zkc.assume.constraint_count_matches_relation`
  establishes, generalized rather than replaced.

A cross-check reduces an assumption; it does not discharge one. A
declared fact agreeing with bytes establishes that the contract
describes those bytes, and whether those bytes are the relation the
anchors name remains asserted (§6), so the assumption is restated in
its reduced form rather than removed.

A contract may declare everything opaque. The consequence is not a
refusal but a ledger: every judgment over it names the full pile of
assumptions. What this document forbids is the opposite surface — any
output that reads as "the relation is verified" without naming what
remains asserted.

## 4. The correspondence judgment

Given a sealed artifact, a `RelationContract`, and optionally the
relation-artifact bytes, the correspondence judgment:

1. checks the partition against §2.3's table and the artifact's claim
   descriptor — the relation-anchor values must equal the artifact's,
   byte for byte (else refuse), and the degenerate-digest obligation of
   §2.3 is surfaced where it applies;
2. when bytes are supplied and the format has a reader: computes the
   content digest, refuses on mismatch with `content_digest`, and
   parses the header per §5;
3. cross-checks every pair that is present: declared `arity` against
   the header's public arity; declared `field_order` against the
   header's prime; enumerated port totals against the header's
   private-input count; `declared_shape.constraint_count` against the
   header's constraint count; the correspondence count against the
   declared arity; each correspondence label against the artifact's
   `statement_labels`; the declared `field_order` against the field the
   artifact's soundness derivations declare as their `field_order`
   analysis parameter — as a compatibility relation (equality, or an
   admitted extension relationship), never as equality with a
   challenge space, which is by design a subset of the field; and
   every sealed `pir.material_bind` edge covering a contract anchor,
   per §2.6;
4. reports the asserted remainder as named obligations — among them,
   always, §6's permanent set where it applies.

Every failure is a named refusal at the field that failed; a judgment
over inputs the contract does not cover is a refusal, not a silent
pass. The judgment's output is canonical content: it embeds the
contract's content digest, the artifact's identity, each verdict, and
the named obligations, and is consumed the way derivation witnesses
are — cited by digest.

## 5. The `r1cs-bin-v1` format

The reader for the iden3 R1CS binary format, version 1, header only.
The format guarantees no section order, so the reader scans sections
by type:

- magic `0x72 0x31 0x63 0x73`, then version `1` (u32 LE), then the
  section count (u32 LE); anything else refuses.
- sections are `(type u32 LE, size u64 LE, body)`. The admitted
  section-type set is closed: `0x01` (header), `0x02` (constraints),
  `0x03` (wire-to-label map). The reader parses `0x01` and skips the
  bodies of `0x02` and `0x03`; **any other type refuses** — an
  unrecognized section can change what the sections a consumer does
  understand mean, and this reader does not guess. Exactly one header
  section is admitted; zero or more than one refuses. Every section's
  declared extent must lie inside the file under checked arithmetic;
  a body longer or shorter than its parsed content refuses, as does a
  section count disagreeing with the sections present.
- the header yields: `field_size` (u32 LE, a positive multiple of 8,
  and consistent with the byte length of the field order the contract
  declares — an absurd width refuses before any allocation), `prime`
  (`field_size` bytes LE), `n_wires`, `n_pub_out`, `n_pub_in`,
  `n_prv_in` (u32 LE each), `n_labels` (u64 LE), `m_constraints`
  (u32 LE). Truncation anywhere refuses, and the header must be
  internally consistent: `1 + n_pub_out + n_pub_in + n_prv_in` must
  not exceed `n_wires`.

The reader establishes, as computed facts: the prime, the public arity
`n_pub_out + n_pub_in` (outputs precede inputs, wire 0 is the constant
one), the private-input count, and the constraint count. It reads no
constraint bodies, and nothing it establishes touches the asserted
tier: slot meaning, constraint sufficiency, and witness-generator
correctness are outside every header.

## 6. What is never established

The permanent asserted set, stated once so no consumer infers
otherwise: that the relation computes what anyone intended; that it is
not underconstrained (no second witness for a fixed instance); that any
witness generator is correct or complete; what any slot or port means;
the provenance of the artifact bytes; and **that the bytes a content
digest covers are the relation the anchors name** — no anchor-preimage
rule exists, so handed bytes and sealed anchors are connected only by
declaration. These are not gaps a better reader closes — no surveyed
format authenticates them — and every judgment that relies on one
carries it as a named assumption.

## 7. The chain this document heads

Machinery in this specification cites this document rather than
re-deriving it:

- **Anchored material** (`endpoints.md` §6.2's admitted reference set,
  `carrier.md` §4's construction routes): a prover fill's
  anchored-material operand cites a relation anchor this contract
  partitions; the executor verifies handed bytes against the operand's
  anchor digest, with `content_digest`, when present, as an additional
  check, and the format gate is this document's reader.
- **Preprocessed-index binding** (the reserved `index` event subkind,
  `vocabularies.md` §2): the verifier-side answer to relations too
  large to read, committing to the relation the contract identifies.
- **A verifier used as a relation** (`endpoints.md` §3.1): the
  reserved bounded artifact verification pins a child relation-contract
  digest among its bindings; this document is that object's admitted
  form, and it duplicates or contradicts no other item of that list.
