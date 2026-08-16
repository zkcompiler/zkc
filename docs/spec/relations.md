# zkc Relations

Status: **canonical for the relation domain (2026-08-17).** Companion to
`vocabularies.md`, which reserves the `RelationContract` role this
document admits, and to `kernel.md` §1.6, whose membrane it respects:
the kernel authenticates claim profiles, anchor shape, and claim flow,
and treats every referenced relation payload as opaque. Any rule that
depends on an external relation fact receives it through an explicit
admitted premise; nothing here weakens that.

zkc consumes and binds relation artifacts; it does not compile relation
source. This document defines the object that makes the binding
sayable: what identifies a relation, how its interface is read, how its
public instance corresponds to a sealed protocol's statement, and —
with equal weight — which parts of that are computed, which are
cross-checked, and which are accepted on a named party's word.

## 1. The RelationContract document

A `RelationContract` is a post-seal, content-addressed registry
document, envelope `zkc.relation_contract`. It describes the interface
of one relation and its correspondence to sealed protocols that cite
that relation through claim anchors. It is deliberately not a seal-time
construct: the sealed artifact already pins *which* relation (the
anchors are inside its canonical encoding), while the contract states
*how that relation's interface is read* — an external fact, entering
through the admitted-premise channel the kernel membrane requires. A
contract can therefore be attached to an artifact sealed before the
contract existed; learning to read a relation better is not a change to
the protocol.

Two contracts may describe the same relation. They must agree with the
sealed anchor digests wherever they are checked against an artifact,
and they may differ in how much of the interface they read — a
difference that is visible in the obligations of every judgment that
cites them, never hidden. A contract cannot swap a sealed artifact's
relation: the anchors are sealed.

Content digests use the exact ASCII prefix `"zkc/relation-contract\n"`
over the entry's canonical JSON. Loading is fail-closed: unknown
fields, missing required fields, and out-of-domain values refuse with
named errors.

## 2. Fields

### 2.1 Identity

Two identity primitives exist and are never merged, because they are
different kinds of trust:

- `content_digest` — a sha256 digest zkc computed over relation-artifact
  bytes it was handed. Its presence claims exactly: these bytes, this
  digest.
- `attested_id` — an identifier some named toolchain asserts denotes
  this relation (a verification-key digest, a program image id). It
  MUST carry `attestor`, the name of the asserting party. Its presence
  claims exactly: this party says so.

At least one MUST be present. Neither implies the other; a contract
carrying only `attested_id` contributes an assumption naming the
attestor to every judgment that reads it.

### 2.2 Format

`format` names the closed reading profile for the relation-artifact
bytes. The admitted set is exactly:

- `r1cs-bin-v1` — the iden3 R1CS binary format, version 1, read per §5.
- `opaque` — no reading profile; every interface fact in this contract
  is declared, not read.

A format outside the set refuses. The set grows one admitted profile at
a time, each arriving with its reader and its refusal corpus; a name
without a reader is not admitted.

### 2.3 Anchor partition

The contract names the claim profile it describes
(`claim_profile`) and partitions that profile's anchor names into:

- `relation_anchors` — anchors that identify the relation itself
  (for the `r1cs` profile: `a`, `b`, `c`).
- `instance_anchors` — anchors that identify one instance
  (for `r1cs`: `public`).

The partition MUST cover the profile's anchor set exactly — every
anchor in exactly one part. The contract is scoped to the relation:
one contract serves every artifact citing the same relation-anchor
digests, while instance anchors vary per artifact and are checked
there. A partition that disagrees with the profile's anchor set
refuses.

### 2.4 Public-instance encoding

`instance_encoding` states how the relation's public instance is
represented. There is no default; a contract that omits it refuses.
The admitted forms are exactly:

- `field_vector` — an ordered vector of field elements. Carries
  `field_order` (exact decimal cardinality) and `arity` (element
  count). This is the shape of constraint-family relations.
- `opaque_bytes` — an uncommitted-length byte stream identified through
  a digest. Carries `digest_function`, the exact hash the consuming
  verifier applies (e.g. `sha256`). The hash choice is part of the
  interface, not a detail: two consumers assuming different functions
  over the same bytes disagree about which instance was proven.

### 2.5 Witness ports

`witness_ports` states the relation's private-input interface, in one
of two admitted forms — because the surveyed relation families genuinely
differ here, and forcing one shape onto the other misdescribes it:

- `enumerated` — an ordered list of ports, each `{name, count}`, for
  relations whose witness is a declared variable range (constraint
  family).
- `opaque` — one port `{name}` whose payload is the whole witness
  object (trace family, where the witness is the entire trace and no
  port list exists to declare).

Port names are the stable references later machinery cites — in
particular, the anchored-material operands that will hand relation
bytes and witness objects to prover fills consume these names. A
contract declares ports; it does not obligate any endpoint to consume
them.

### 2.6 Statement correspondence

`statement_correspondence` is an ordered list mapping the relation's
public-instance positions to a sealed protocol's statement labels:
entry `i` is `{slot: i, label}`, and the list order is the instance
order. This is the wiring diagram between the two spellings of "the
statement" that a sealed artifact carries — the ordered, typed,
transcript-absorbed `statement_labels` and the opaque instance anchor —
which nothing else relates.

What each part of the correspondence establishes is exactly the tier
discipline of §3: that a named label exists in the cited artifact's
ABI, in the ABI's own order, is computed; that the correspondence
count equals the declared arity is cross-checked; that slot `i`
*means* what the label suggests is asserted, permanently, because no
surveyed format authenticates names. Where the sealed artifact carries
a `pir.material_bind` from a statement value to an anchor this contract
covers, the checker uses that sealed edge as an additional
cross-check source; a sealed carrier for the full ordered
correspondence is a named-extension seat (`kernel.md` §12,
subject- and relation-bound witness schemas), not this document's
claim.

## 3. Trust tiers — a mapping, not a taxonomy

Every fact a contract contributes lands in the obligation machinery
that already exists; this document adds no parallel trust vocabulary.
Three landing patterns cover every field:

- **Computed.** A fact zkc derived from bytes alone: a content digest
  it took, a header field the reader parsed, the presence and order of
  statement labels in a cited artifact. Lands as a machine-checked
  fact of the correspondence judgment.
- **Cross-checked.** Two independent declarations agree — the declared
  arity and the header's arity, the declared field and the artifact's
  challenge space, the correspondence labels and the sealed ABI.
  Lands as a machine-decided consistency condition, with the semantics
  stated exactly: **agreement is consistency, not truth.** Both
  declarations can be wrong together, and no output of this judgment
  claims otherwise.
- **Asserted.** What a slot means; that the relation is not
  underconstrained; that its witness generator is correct; provenance.
  Lands as a named assumption carried by every judgment that reads the
  contract — the pattern `zkc.assume.constraint_count_matches_relation`
  already established, generalized rather than replaced.

A contract may declare everything opaque. The consequence is not a
refusal but a ledger: every judgment over it names the full pile of
assumptions. What this document forbids is the opposite surface — any
output that reads as "the relation is verified" without naming what
remains asserted.

## 4. The correspondence judgment

Given a sealed artifact, a `RelationContract`, and optionally the
relation-artifact bytes, the correspondence judgment:

1. checks the anchor partition against the artifact's claim descriptor
   — the relation anchors named by the contract must equal the
   artifact's, byte for byte (else refuse);
2. when bytes are supplied and the format has a reader: computes the
   content digest, refuses on mismatch with `content_digest`, and
   parses the header per the format profile;
3. cross-checks every pair that is present: declared arity against the
   header's arity, declared `field_order` against the header's prime,
   the correspondence count against the declared arity, each
   correspondence label against the artifact's `statement_labels` (name
   and order), the declared field against the artifact's
   soundness-projected challenge space, and any sealed
   `pir.material_bind` edges covering contract anchors;
4. reports the asserted remainder as named obligations.

Every failure is a named refusal at the field that failed; a judgment
over inputs the contract does not cover is a refusal, not a silent
pass. The judgment's output is consumed the way derivation witnesses
are: cited by digest, carrying its obligations.

## 5. Reading profile `r1cs-bin-v1`

The reader for the iden3 R1CS binary format, version 1, header only:

- magic `0x72 0x31 0x63 0x73`, then version `1` (u32 LE), then the
  section count (u32 LE); anything else refuses.
- sections are `(type u32 LE, size u64 LE, body)`. The reader consumes
  the header section (type `0x01`) and skips section bodies it does not
  read; it refuses a file containing custom-gate sections (`0x04`,
  `0x05`) outright, because their presence changes what the constraint
  sections mean for a consumer that does not understand them.
- the header section yields: `field_size` (u32 LE, a positive multiple
  of 8), `prime` (`field_size` bytes LE), `n_wires`, `n_pub_out`,
  `n_pub_in`, `n_prv_in` (u32 LE each), `n_labels` (u64 LE),
  `m_constraints` (u32 LE). Truncation anywhere refuses.

The reader establishes, as computed facts: the prime, the public arity
`n_pub_out + n_pub_in` (outputs precede inputs, wire 0 is the constant
one), and the private-input count. It deliberately does not read
constraint bodies, and nothing it establishes touches the asserted
tier: slot meaning, constraint sufficiency, and witness-generator
correctness are outside every header.

## 6. What is never established

The permanent asserted set, stated once so no consumer infers
otherwise: that the relation computes what anyone intended; that it is
not underconstrained (no second witness for a fixed instance); that any
witness generator is correct or complete; what any slot or port means;
the provenance of the artifact bytes. These are not gaps a better
reader closes — no surveyed format authenticates them — and every
judgment that relies on one carries it as a named assumption.

## 7. The chain this document heads

Later machinery cites this document rather than re-deriving it:

- **Anchored material** (`endpoints.md` §6.2's admitted reference set,
  `carrier.md` §3's route references): when a prover fill is handed
  relation bytes, the operand cites a relation anchor this contract
  partitions, the executor verifies the bytes against `content_digest`,
  and the format gate is this document's reader.
- **Preprocessed-index binding** (the reserved `index` event subkind,
  `vocabularies.md` §2): the verifier-side answer to relations too
  large to read, committing to the relation the contract identifies.
- **A verifier used as a relation** (`endpoints.md` §7): the
  child-verifier binding list includes a relation-contract digest;
  this document is that object's admitted form, and its fields are a
  subset of that list so the extension is an addition, not a rework.
