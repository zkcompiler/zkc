# zkc Carrier Specification

Status: **canonical for the PIR and OIR carrier.** This document fixes
the load-bearing carrier decisions and deliberately nothing else: concrete ODS
spellings live in `include/zkc/Dialect/`, while canonical identity and admitted
format structure are fixed here and in `versioning.md`.

The artifact carries no theorem citation: there is no reduce `row`, no
container hop citation, and no `theorem_rows` section. Post-seal conditional
security is derived about a sealed artifact by the Soundness Kernel
(`soundness.md`) from an explicit signature and derivation plan.

## 1. The carrier rule

MLIR is the structural carrier, not the semantic source of truth
(kernel §13). A carrier choice that alters any
WF/LIN/BIND/COV_obl/ReductionClosureOK/TerminalClosureOK verdict, the identity
set, or a boundary signature is a kernel change
and must be made there first. Conformance is kernel §13(a)–(e):
lossless representation, identical verdicts, carrier-independent
identity, ≤-ordered absorption preserved through projection, and
**injective prefix-free framing** of absorbed events in the
transcript-hash input (§13(e) — ambiguous framing voids the Binding
Lemma's a-injectivity, independently of everything else).

## 2. Dialects

Two registered ODS dialects: `pir` (the protocol object: events,
claims, transformers, capabilities, containers) and `oir` (the
endpoint artifact: program plus embedded provenance). A shared core
dialect is admitted only if duplication becomes real. Artifact
containers are `IsolatedFromAbove`; the artifact — never a loose
program — is the unit of identity and verification.

## 3. The spine (kernel E, ≤, A)

- The protocol body is a single ordered block. Event order in the
  block IS ≤; there is no other order.
- Events are chained through the **builtin `token` type**, using the
  upstream `TokenProducerTrait`/`TokenConsumerTrait` discipline.
  Scope of the upstream guarantee: **no-forwarding, not linearity** —
  exactly-one-use comes from the container verifier; the token
  commit itself prescribes op-level side effects for stronger
  contracts, which is the resource below. A toolchain-pin change MUST
  revalidate the token isolation and no-forwarding assumptions.
- Absorption (membership in A) is an event property, not implied by
  op kind; unabsorbed slots carry it explicitly (`kernel.md` §5.3).
- A `pir.chal` is a protocol-neutral **challenge capability**, not a value of
  a distinguished `chal` class. It names the semantic class of each sample,
  and its value result is inferred as `!pir.val<"class">`; the producing op
  carries fresh-sampling origin. Consumers use
  `ChallengeCapabilityOpInterface` to obtain that exact SSA result, class,
  count, and sampling rule rather than recognizing an op name or guessing a
  result ordinal. Scalar form has count `1` and rule `uniform`; vector form is
  one capability with a canonical count in `2..2^20` and the PIR-admitted
  rule `uniform_independent`. Its codec route is resolved per event
  as `kappa.codecs[payload_class]`; there is no global challenge codec.
- Every protocol event declares a write effect on the dialect
  `ProtocolResource`, so non-threaded events (checks) and threaded
  events alike are conservative under generic passes. Defense in
  depth, not the safety argument.
- **Transformation safety is a conformance obligation**: generic
  transformations MUST preserve the canonical protocol form, and pattern
  application beneath a sealed artifact MUST refuse rather than silently
  changing semantic content. Every context that can host raw sealed IR and
  execute pattern-driven transformation installs the refusing guard before
  any pipeline runs; the rule derives the installation points, so adding
  such a context adds an installation.

## 4. Claims and transformers (kernel C, R)

- Claims are SSA values of type `!pir.claim<"profile-id">`; **LIN is
  structural**: the container verifier requires every claim value to
  have exactly one use. Fan-out and drop are representable only as
  declared transformers. The claim type is excluded from generic
  type constraints so foreign ops cannot absorb claims. **Citation
  is not consumption**: referring to a claim or check without
  consuming it uses an author label in an attribute, never an SSA operand.
  The profile id resolves through `ProtocolVocabulary` to one coarse kind and
  one exact ordered anchor schema; kind is not independently authored.
- **Sources** (`pir.instantiate`, later object introduction and
  artifact import) produce claims and carry the descriptor
  **anchors**: a `DictionaryAttr` of profile-required anchor names
  to `sha256:`-prefixed digest strings. Anchor *shape* (prefix +
  64-hex) is an op-verifier check; exact anchor agreement is the seal-time
  gate against the resolved profile. Op verifiers must not know registry
  content.
- **Checks** have the stable assembly surface
  `pir.check "label" contract "id" params {...} semantic_args {...} (...)`;
  optional dictionaries may be omitted only when the contract declares them
  empty. `contract` resolves one `CheckContract`; `params` must equal its
  static parameter schema, `semantic_args` must equal its intrinsic semantic
  role schema, and positional SSA operands must have one unique segmentation
  into the contract's typed operand roles. The optional transparent `expr`
  remains artifact data and is normalized to contract roles before a reduction
  slot or terminal predicate is compared. Labels select checks during authoring; canonical form
  uses event positions.
- **Reductions are one generic op**, `pir.reduce`, not named ops per family.
  `ReductionContract`s are registry *data* with fail-closed
  admission, and a new contract never requires a protocol-family branch or a
  recompile. The op carries `label` (authoring selector), `contract` (the exact
  local implication, pinned by registry content digest), and `checks` (an exact
  role-to-check-label dictionary selecting every contract-owned body premise).
  The op names no theorem: which theorem applies to an occurrence is selected
  by a signature, a binding, and a plan (`soundness.md`).
  Unknown registry keys are verifier-legal and seal-fatal. Variadic claim
  operands follow contract input order; variadic value operands are positional
  contract dependencies; `params` is the exact typed instance dictionary;
  `out_anchors` is the positional authored assertion for result descriptors;
  and variadic claim results spell their profiles in their types. Seal derives
  outputs from the contract and compares them byte-for-byte rather than
  treating authored anchors as authority. Two variadic operand groups use
  `AttrSizedOperandSegments`; `operandSegmentSizes` is derived structure, never
  identity.
- **Membership and roles** (kernel bodies ⊆ E, interleaving legal):
  a body **slot** references its owning instance with three
  structured props — `instance` (the reduce's label), `role` (contract
  role name), `idx` (occurrence for declared-multiplicity roles).
  Membership is a slot-only fact: message roles name prover messages; checks
  remain ordinary non-absorbing spine events and are owned by the reduction's
  explicit `checks` map (and, where admitted, by its exact output discharge);
  other event kinds gain membership only with a
  consumer — until then the shape is unrepresentable rather than
  rejected. **The
  round number stays out of the IR**: role + contract reach the round
  through the registry's role→round assignment — the single
  declaration that also prices ε_i (kernel §5.2); an IR-carried
  round would be a mirror that can drift. **One truth per fact**: an
  event whose value is a reduce operand carries no membership props
  — operand position is that fact's only spelling (container rule).
- **Material bindings** use the stable surface
  `pir.material_bind %value to "sha256:..." : !pir.val<"value-class">`.
  `%value` denotes a local
  `ValueRef`; canonical form replaces it with the producer event/result
  position. The target is a stable `MaterialRef` and is preserved through
  link while the local endpoint is reindexed. Bindings are tail members, are
  identity-bearing, satisfy the v0 partial-function/reverse-injectivity rule,
  and must be consumed by real reduction or terminal attachments. There is no
  alias op.
- **Discharges** use the stable surface
  `pir.discharge %claim : !pir.claim<"profile-id"> rule "id" checks {role = "check-label"}`.
  The rule id
  resolves through `ProtocolVocabulary`; the dictionary must bind exactly the
  rule's terminal roles to distinct checks with matching contracts. Labels are
  selectors only. Canonical form replaces the claim with its claim position
  and every selected check with its event position.
- **Construction routes** are optional identity-bearing protocol content for
  prover projection. The closed top-level route dictionary has
  `witnesses` and `instances`: witnesses are ordered `(label, handle class)`
  declarations; each instance binds a proof slot to an exact HoleContract and
  its parameters and to statement, prior-slot, challenge, constant,
  anchored-material, witness, or prior-hole-result inputs. A slot may instead
  bind a route-declared pure expression over the same references. Seal checks
  the closed shape, all references, anchors, parameters, payload/handle classes
  and counts, acyclicity, slot-binding consistency, and HoleContract citation
  (E223).
  Route totality is intentionally deferred to `prover_skeleton` projection,
  so a verifier-only consumer may seal a partially routed protocol. The cited
  HoleContract content is stamped into `vocab.hole_contracts`; an authored
  route or label is never an executable supplier.
- **Body layout**:

```text
[sources]*  begin  [spine events]*  end  [reduces]*
             [material_bind]*  [sinks]*
```

  Reduces sit after `end`: SSA dominance then *proves* every
  challenge a reduction consumes was sampled before the reduction is
  formed, and body events forward-reference instance labels through
  attributes (two-pass resolution in the verifier). Sinks close the
  block. ≤ is block order between begin/end; the tail is the claim
  graph read as a string diagram (kernel §4). Tail order is
  **normalized, not authored** (§6). The seal boundary stamps the vocabulary
  evidence required by downstream judgments and one closed container `vocab`
  table. Its
  four always-present protocol-entry sections — `claim_profiles`,
  `check_contracts`, `reduction_contracts`, and `terminal_rules` — are the sole
  digest authority for every cited claim profile, check contract, reduction
  contract, and terminal rule; a fifth protocol-entry section,
  `hole_contracts`, is present exactly when construction routes cite at least
  one hole. Consumed construction entries are pinned separately in
  `construction_profiles`; the full closed `vocab` section set is §6's.
  Operations carry ids, never a
  second protocol-entry digest that could disagree.
  Identity therefore pins vocabulary semantics, not names, while uncited
  environment entries do not enter the artifact (kernel §8).

## 5. Container verification

Three layers, and the container walk is interface-driven:

1. ODS/op verifiers — types, attributes, token discipline, local
   shape (label formats, anchor shape, challenge space format). Op
   verifiers are hermetic: no registry, no IO.
2. Container verifier — the layout automaton
   (Sources→Spine→Reduces→Bindings→Sinks), thread-chain = block order, label
   uniqueness and citation/membership resolution, claim single-use,
   local `ValueRef` resolution, binding shape, and the one-truth-per-fact
   membership rule. Members implement a
   minimal `ProtocolMemberOpInterface` — `getPhase`,
   `getMemberLabel`, `getThreadIn/Out`, `isAbsorbing`,
   `getMembership` — so new member kinds declare their category once
   instead of growing a closed switch (the CIRCT SOST / linalg
   shared-interface-verifier pattern). The walk stays fail-closed:
   an op without the interface is not a protocol member, full stop.
   Challenge consumers separately use `ChallengeCapabilityOpInterface`; it
   identifies the one sampled SSA result of a multi-result producer, so the
   threaded token can never be mistaken for challenge data.
3. Seal boundary — the full
   WF/LIN/BIND/COV_obl/ReductionClosureOK/TerminalClosureOK batteries with stable
   per-axis diagnostic ids (`boundaries.md`), including the PIR
   rules: the encoding-domain judgment (kernel §3, item 4), requirement
   generation from contract round structure (kernel §5.2), the
   statement-binding default (kernel §5.3), contract profile/arity
   cross-checks, exact profile-anchor agreement, check-contract agreement,
   contract-owned check selection/material/output reconstruction,
   material-binding exactness, and terminal-rule matching. `SealEngine`
   centralizes these judgments and owns no IO; pass and tool adapters resolve
   environments and invoke it.

Diagnostic ids remain the conformance surface; every id exercised by
a negative test in the same commit that introduces it. A new check
takes the next number in its layer's range, never a new range; the
allocation itself — every range, its component, and its live and
reserved ids — is declared in `versioning.md` §3 and lint-enforced
against the source tree. Refusals by the sealed guard and fail-closed loader
MUST remain distinguishable from successful execution. A machine-readable
audit claim additionally requires those refusals to be carried by a typed,
structured channel.

## 6. Identity and encoding

- id_kind = `SHA256(tag_kind ‖ canonical bytes)` with the kernel's
  fixed domain tags (`zkc/pir` for PIR, kernel §8); references use the
  `sha256:<hex>` prefixed form.
- The canonical encoder walks **op state, never text**: typed
  property accessors, operand groups, block order — printed pretty
  form elides defaults and derived props by design and is not the
  identity surface. The encoding is **fully positional**: author
  labels never appear, and every reference — challenge deps, check
  inputs, terminal selections, consumed claims, membership instances,
  material-binding endpoints — is one of
  three position spaces (event position in ≤ order, claim position in
  production order, transformer position in the normalized sequence).
  Labels in the encoding would collapse kernel §8's id-stable renaming
  (≅) to string equality; semantic strings that are NOT labels —
  profiles, contracts, classes, domains, roles, routes — stay. The top level is
  `{policy, kappa, vocab, transformers, events, material_bindings, sinks}`
  plus optional `routes` and `segments` sections;
  `vocab` is the seal-stamped resolved-vocabulary table. A container without
  it has no canonical identity. Identity-bearing construction routes are
  encoded in the `routes` section when present. The `vocab` section set is closed
  and flat:
  `claim_profiles`, `check_contracts`, `reduction_contracts`, and
  `terminal_rules` contain the exact transitive cited protocol subset, and
  `construction_profiles` maps the consumed construction-profile entries — the
  kappa sponge and every codec a payload class routes through — to content
  digests whenever kappa consumes them. `hole_contracts` is present exactly
  when routes cite at least one HoleContract and contains that exact cited
  subset. Construction entries are pinned unconditionally on hopped versus
  unhopped use (zkc-E229). An unknown
  section is refused rather than carried into identity. `transformers` is the sources-then-reduces sequence,
  each source and reduce producing claims in position order. A
  segmented container additionally carries `segments` as an optional,
  additive section (the later-segment start positions, judgment-bearing
  by `kernel.md` §5.3); a one-segment container omits it and encodes exactly as
  before.
- **Claim and material rows.** A claim descriptor is
  `[profile_id, canonical_anchor_dictionary]`; its position-free descriptor
  digest uses exact prefix `"zkc/claim\n"`. `material_bindings` is sorted by canonical
  `ValueRef` then `MaterialRef`, and duplicates or reverse-injective conflicts
  refuse before identity. A discharge row contains the consumed claim
  position, terminal-rule id, and role-sorted selected check event positions.
  The PIR event rows, which §6 fixed only by description, are exactly:

  ```text
  ["bind",  payload_class, stage, value_or_null]
  ["slot",  payload_class, absorbed, membership_or_null]
  ["chal",  payload_class, label, domain, space, dep_positions, mode_or_null]
  ["check", contract, input_positions, params, semantic_args, expr_or_null]
  ```

  `absorbed` is the integer `1` or `0`, not a boolean, and `membership` is
  `[transformer position, role, idx]` or null. Author labels appear only where
  a row lists one above; every other reference is a position.

  A reduction row is exactly
  `["reduce", contract, consumed_claim_positions,
  dependency_event_positions, produced_profiles, params, out_anchors,
  role_sorted_[role,check_event_position]]`. Evaluated material expressions and
  closure verdicts do not enter the row; the identified inputs from which they
  are reconstructed do.
- **Transformer normalization**: kernel C and R are sets; block
  order of sources, reduces, and sinks is carrier-invented. The
  encoder normalizes before hashing — sources sort by content (profile,
  then canonical anchor bytes; exact-content duplicates keep authored
  order, a named limitation), sinks by their claim's producer position, and
  reduces by a deterministic ready-set walk: repeatedly take the ready reduce
  — one whose consumed claims are all produced — that is smallest under the key
  `(contract, consumed positions, dependency positions, produced profiles,
  params, out_anchors, role-sorted checks, authored index)`, compared as
  canonical bytes field by field. The authored index is last and breaks
  exact-content ties, so the order is total. Two implementations agreeing on
  "topological with a content tie-break" is not enough: a stable sort after a
  content sort and a global min-key ready set are both readings of that phrase
  and they produce different orders on the same graph.
  Two IRs denoting one kernel object get one id. Any cited profile, check
  contract, reduction contract, or rule absent from the sealed
  protocol-vocabulary table has no
  identity — the encoder rejects it. A same-point batch sorts complete member
  descriptor records in these canonical descriptor bytes, permuting
  commitments, values, and coefficients together; duplicate descriptor bytes
  refuse. Its output `members` anchor is
  `SHA256("zkc/claim-vector\n" || canonical(descriptor_array))`, where
  `descriptor_array` is precisely that sorted array of full `[profile,
  anchors]` records. Sorting commitments or values independently, using source
  visitation order, or hashing a projection of each descriptor is
  nonconforming.
- A challenge event row carries its semantic payload class, exact cardinality,
  requirement-set positions, and optional vector mode. Thus changing
  the semantic payload class from `fr` to `ext_field`, changing the
  independently represented count/shape, or changing a per-event codec route
  changes identified content; origin is not re-encoded as a fake class.
- The **encoding domain is enforced**, not assumed (kernel §3, item 4):
  printable-ASCII strings, strict signed-i64 integers, larger
  numerics as decimal strings — a seal judgment with its own
  diagnostic id, mirrored by the oracle. The enforced domain, not
  escaper agreement, is the byte-parity argument. Dictionary
  attributes (kappa, params, anchors) are canonical by construction
  (sorted-key uniquing). `protocol_name` is also printable-ASCII-gated because
  it is published in diagnostics and derived views, although it remains a
  human handle outside PIR identity.
- A sealed artifact carries the body and **no derived materialized tables**:
  tabulations of E, χ, C, K and the obligation rows are views
  (kernel §11) computed on demand. The encoder walks the body,
  policy, kappa construction data, and identity-bearing `material_bind`
  operations — never a
  derived view and never an author-label table. The terminal role map is real
  semantic content, but its canonical form contains rule roles and event
  positions rather than labels.
- The stored PIR id is excluded from its own preimage. Every raw-input
  boundary recomputes it and the applicable judgment battery; projection and
  recheck refuse a mismatch with zkc-E171. A downstream operation may instead
  accept an opaque authenticated capability that unforgeably binds an immutable
  subject or closed derived view to its identity and the authority used at
  admission. A derivation binds the exact identity of that sealed subject and
  refuses when the plan names another subject. Serializing or cloning does not
  invalidate the original capability, but a serialized or mutable copy is raw
  input when it later enters another semantic boundary and must be authenticated
  there. Thus a judgment derived about one artifact cannot be reported for
  another, and no mutable handle or cached verdict can stand in for admission.
- Historical encodings are not migration inputs. The the canonical encoding clean break
  removed the reduction theorem citation, the container hop citation, and the
  sealed `theorem_rows` section. The loader accepts only PIR and never
  reinterprets an earlier identity. Identity-bearing changes are therefore
  landed as one explicit re-mint batch rather than incrementally moving
  goldens through intermediate states.

### 6.1 The endpoint carrier (OIR)

Canonical OIR has identity
`SHA256("zkc/oir\n" || canonical_bytes)`. Its load-bearing rules are:
**provenance is inherent**
(`src` — canonical event positions on each operation that realizes a source
obligation; framing, finalizer, and pure construction operations need not
carry it, so the ProjectionMap remains a derived view); **linearity is the same
verifier pattern** (sponge and stream are exactly-one-use, closed by
`decide`/`finish` and `expect_end`/`end_stream` — the frame rules in
`endpoints.md` §§2–3); **protected effects vs. free algebra** — protocol events write
an `EndpointResource`, pure computation is the first
legally-optimizable region of the stack. The artifact stores one id. OIR
also defines a provenance-independent `semantic_id` as a computable view; it is
not a second stored identity field. Its preimage is the canonical document
under an exact erasure — the PIR `source` citation is dropped and every row's
`src` position list is emptied — hashed under the domain tag
`"zkc/oir-semantic\n"`. Two artifacts that differ only in source citation or
projection provenance therefore have equal semantic ids, and any
endpoint-semantic change (entry signature, codecs, labels, pins, or any row)
changes the id.
The stored id is excluded from its own preimage. Every execution boundary and
every attributable derived view recomputes the OIR id and refuses a mismatch
before using the artifact. This includes execution, vector-evaluation,
proof-size, and transcript-schedule consumers; matching a sidecar vector to
the stored string is not an identity check. Raw canonical/id
translation remains available only as an authoring diagnostic that computes
the value to store.
**Label asymmetry, deliberate**: PIR author labels do not enter PIR identity,
but endpoint labels do enter OIR identity. Statement and witness labels define
input lookup and ordering; check, squeeze, read, write, and hole labels provide
stable endpoint naming. Changing any of them changes the OIR id even when the
source PIR id is unchanged.

Projection preserves each challenge capability as exactly one `oir.squeeze`.
The row carries semantic payload class, explicit count (`1` or `2..2^20`),
domain, sampling rule, exact sample-space cardinality, and source event
position. The result type is `!oir.val<"class", "sampled">`, and the program's
baked codec map is indexed by that class for both scalar and vector events.
This is an exact schedule declaration; projection does not execute the sponge
or compute challenge values.

An opaque `pir.check` projects only after its CheckContract content digest is
resolved from the sealed vocabulary. OIR v3 carries both the human-readable
contract id (`kind`, diagnostic only) and `contract_digest` (dispatch
authority); both enter OIR identity. A missing or malformed digest refuses at
projection, and a directly authored `oir.check_call` without a canonical
`sha256:` digest is invalid.

OIR admits two frames. The verifier frame threads a read cursor
through `read`/`expect_end` and closes the sponge at `decide`. The
`prover_skeleton` frame threads a write cursor through `write`/`end_stream`,
closes its replica sponge at `finish`, and admits `hole_call` plus linear
`!oir.handle<class>` values. On successful `pir-project` output, its ordered
`witness_labels` and exhaustive `counterparty` rows are identity-bearing
endpoint data. Projection derives both frames from the same sealed spine and
checks their lockstep correspondence. Exhaustiveness is authenticated only in a
validation context that has both the sealed source PIR and the OIR artifact. A
source-free OIR validator can establish internal row well-formedness, but it
cannot establish source-obligation coverage from the rows alone.
The full endpoint semantics and nonclaims are in `endpoints.md` §6.

### 6.2 The canonical OIR document

Everything below is identity: the OIR id is `SHA256("zkc/oir\n" ‖ these
bytes)` under the canonical JSON rules of §6. It is written out here because
byte parity across implementations is this project's acceptance gate, and a
gate over an unstated grammar tests agreement rather than conformance — a
second implementation must be derivable from this section alone.

The document is an object with exactly these keys:

```text
codecs            class → codec name, baked from kappa at projection
endpoint          "verifier" | "prover_skeleton"
entry             the typed block signature, in argument order
param_digests     sorted "kind:name=sha256:<hex>" construction pins
program           the rows, in block order
source            "sha256:<hex>", the sealed PIR this projects
statement_labels  the public statement argument names, in order
witness_labels    prover only: ordered [label, handle class] pairs
counterparty      prover only: [event position, discharge kind] rows
```

`witness_labels` and `counterparty` are present exactly on a prover document
and absent exactly on a verifier one. `source` is dropped for the
`semantic_id` view (§6.1) and present otherwise. The stored id is excluded
from its own preimage.

**References.** A value is named by where it comes from, never by label:
`["a", n]` is entry argument *n*; `["r", row, k]` is result *k* of program
row *row*, numbered in block order from zero.

**Entry.** One element per block argument, in order: `["val", class]`,
`["handle", class]`, or `["stream"]`. A counted value is a single argument
carrying its count; it does not expand into positions.

**Provenance.** Every row that realizes a source obligation ends in a `src`
array of canonical PIR event positions (§6, the encoder's numbering), possibly
empty. Framing and pure-construction rows carry no `src` field at all: `init`,
`expect_end`, `decide`, `end_stream`, `finish`, and `hole_call` — a hole
covers no obligation.

**Rows.** The complete grammar, one line per admitted row:

```text
["init",        sponge, iv]
["absorb",      sponge, value, src]
["squeeze",     sponge, label, payload_class, count, domain, rule, space, src]
["read",        stream, label, payload_class, src]
["read_vec",    stream, label, payload_class, count, src]
["write",       stream, value, label, payload_class, src]
["write_vec",   stream, value, label, payload_class, count, src]
["const",       value, payload_class, src]
["f_neg",       operand, src]
["f_add",       lhs, rhs, src]
["f_mul",       lhs, rhs, src]
["g_exp",       base, exponent, src]
["g_mul",       lhs, rhs, src]
["assert_eq",   lhs, rhs, label, src]
["check_call",  inputs, label, kind, contract_digest, semantic_args, src]
["hole_call",   operands, results, label, kind, contract_digest,
                params, semantic_params]
["expect_end",  stream]
["end_stream",  stream]
["decide",      sponge]
["finish",      sponge]
```

`count` and `space` are canonical decimal strings; `count` is `"1"` for a
scalar and `2..2^20` for a vector. The counted stream families carry
`count` of at least 2 — a scalar keeps its own family, so the scalar
encodings never move — and decode or encode that many elements of the
payload class at its fixed width, in order: the schedule is the only
width authority, and the wire carries no length framing. The whole
vector is one value, exactly as a vector squeeze's whole sample is; a
count-n value fills n units of a check contract's operand segmentation
and never splits across two segments. A `hole_call`'s `results` are
typed the way `entry` elements are, with a counted result carrying its
count as a third element (`["val", class, count]` — the scalar form is
unchanged); `operands` are references, and `params` / `semantic_params`
are the cited contract's static and semantic bindings in that
contract's own name order. `check_call`'s `semantic_args` is the
role-sorted list of semantic argument references.

The verifier frame ends `expect_end` then `decide`; the prover frame ends
`end_stream` then `finish`. A row family absent from this table has no
canonical encoding and refuses.

## 7. Registries

All JSON vocabularies use one `zkc::registry` loading discipline: versioned,
closed-field schemas; unknown fields, constructors, ids, and versions fail
closed. Duplicate object keys refuse at every nesting depth before schema
validation, so no authority input has a parser-dependent last-wins reading.
The verifier/seal split remains: unknown ids in authored IR may parse, but seal
refuses them. Candidate registries are seal-time environment and do not enter
identity wholesale; only their resolved cited content does.

The protocol-semantic surface is one cross-admitted file,
`registry/protocol-vocabulary.json`, with envelope
`zkc.protocol_vocabulary`, with six required source sections:

```text
predicate_specs    CheckPredicateSpec preimages
claim_profiles     ClaimDescriptorProfile
check_contracts    CheckContract
hole_contracts     HoleContract
reduction_contracts ReductionContract
terminal_rules     TerminalRule
```

Each entry has canonical content and a tagged content digest under the exact
ASCII prefix `"zkc/check-predicate-spec\n"`,
`"zkc/claim-profile\n"`, `"zkc/check-contract\n"`,
`"zkc/hole-contract\n"`, `"zkc/reduction-contract\n"`, or
`"zkc/terminal-rule\n"`. Admission is joint, not six independent loader
successes: it resolves every profile reference, role, contract pin, producer
  reduction-contract content/version, normalized predicate, material
  expression, and attachment source/target;
detects cycles where forbidden; and rejects stale or ambiguous content before
the vocabulary can be supplied to seal. The five protocol entry families in
the sealed `vocab` table — `claim_profiles`, `check_contracts`,
`reduction_contracts`, `terminal_rules`, and `hole_contracts` — are the sole
digest authority for protocol-entry semantics and contain exactly the
transitive cited subset; `hole_contracts` is omitted only when no construction
route cites one, and consumed construction entries are pinned separately in
`construction_profiles` (§6). A CheckContract
digest commits to its predicate descriptor, which in turn pins an opaque
predicate-spec content digest and entrypoint. The sealed artifact does not
duplicate the predicate-spec preimages as a second digest namespace: a
consumer that must re-admit them resolves the cited `predicate_specs` closure
from `registry/protocol-vocabulary.json` against the CheckContract digest
already pinned in `vocab`. No operation carries a parallel protocol-entry
digest.

- A **claim profile** carries one coarse `kind` and one ordered,
  duplicate-free `anchors` vector. Exact instance agreement is checked at
  seal. Adding a profile is additive; changing the content under an existing id
  changes its digest and therefore every citing artifact id.
- A **check contract** has a human-readable entry id used only for lookup and
  diagnostics. Its exact content digest is the projection and dispatch
  authority: that digest binds `mode`, one predicate descriptor, sorted
  `parameters`, sorted `semantic_parameters`, and ordered operand segments.
  It does not identify or attest an executable adapter implementation. There
  is no second carrier-kind namespace. A segment has
  a role, value class, and multiplicity `exact(n)`, `capture(name, min)`, or
  `same_as(name)`. Parameter, semantic-parameter, and operand-role namespaces
  are pairwise disjoint. `exact` and `capture.min` are positive; a contract has
  at most one independent capture, and `same_as` may reference only that
  earlier capture. These restrictions make operand segmentation unique; an
  instance with no solution refuses.
- A **hole contract** has the same content-addressed authority discipline on
  the prover side. Its digest binds a closed hole kind, typed value and handle
  operand/result segments, anchored-material operands, static parameters, and
  digest-shaped semantic parameters. Segment counts and every parameter are
  part of the ABI. The digest is the sole `hole_call` dispatch authority. A route
  citation does not identify a supplier or prove the supplier's internal
  computation. A conforming execution profile supplies the exact declared
  operands and parameters and validates the exact declared result shape.
- A **reduction contract** owns both transcript shape and exact local
  transition: consumes, dependency slots, rounds, typed instance parameters,
  body-check roles with pinned contracts/parameters/predicates/attachments,
  material constraints, and positional output constructors. Each consume entry
  is one exact profile, except that its sole consume may be variadic with a
  positive minimum. The digest transitively covers every referenced profile and
  body-check contract. It declares no security theorem and the reduce names
  none: a rule binding anchors on this exact contract from the signature side.
  The contract round view generates `P_req` and supplies the rounds a rule's
  contract-derived sequences read.
- A **terminal rule** is check-backed in PIR. It carries one consumed-profile
  pattern, an optional exact producer contract/output pattern,
  terminal-role-to-contract pins, a closed attachment list, and one normalized
  predicate for every transparent role. Its digest transitively covers the
  consumed profile, optional producer contract, and selected check-contract
  digests. The attachment-source set and relation set are exactly kernel §4.2;
  absence or an unknown constructor is refusal, never an open-world extension.

The construction-profile registry remains the authority for sponge/codec
shape. There is no theorem authority on the carrier side at all: a rule and its
binding live in the signature the Soundness Kernel resolves, and a binding's
protocol anchor is checked against the exact reduction contract already pinned
by `vocab.reduction_contracts` at APPLY rather than at seal. Loader vocabulary
that reaches canonical encoding is held to the encoding domain.

Realization boundaries:
**variable-length codec framing** — every committed codec has a fixed wire
width, and counted rows carry statically declared multiplicity over it, so
every minted wire layout is a constant of its protocol instance. A width not
statically declared must be computable from transcript state strictly before
the read — no surveyed opening shape needs more, and none is minted. A future
variable-length class that is absorbed needs explicit length framing whose
injectivity joins the Binding Lemma's a-leg; one that is only read — an
unabsorbed slot under `kernel.md` §5.3's default — owes unambiguous decoding
and no transcript obligation, which counted unabsorbed rows discharge by
construction;
**profile-scoped value models** — an execution profile defines the value
operations it supplies, and an operation outside that declared model MUST
refuse explicitly; **registry-keyed `check_call`
adapters** — an opaque predicate spec supplies the proposition's denotation,
while projection emits a digest-keyed `check_call`. The spec supplies no
adapter implementation and attests neither execution nor conformance; a
landing adapter needs separate execution and conformance evidence.

## 8. Where the carrier stops

The carrier represents and identifies a protocol. It does not evaluate one.
Post-seal conditional security is the Soundness Kernel's judgment over an
explicit signature and derivation plan (`soundness.md`), and the only thing crossing
that boundary is the authenticated structural view: claim and reduction
occurrences, contract rounds, challenge capabilities, material anchors and
their transcript positions, and the sealed identity that scopes them. That
projection vocabulary is finite and kernel-owned; a context cannot extend it.


## 9. Bytecode and versioning

Artifacts ship as `<id>.mlirbc` with producer marker `zkc_v<release>`; the
marker is error locality, and acceptance rides on the identity recheck and
the dialect version blob. The loader re-verifies IR and recomputes the id
under `zkc/pir` before returning an artifact. PIR defines no predecessor
decoder, upgrade hook, compatibility flag, or prior-version encoder/id API. Rules
(from upstream Test-dialect versioning practice):

1. The pir/oir dialects carry a **version blob** through
   `BytecodeDialectInterface`; conforming readers and writers MUST preserve it
   across a bytecode round trip.
2. Any op whose properties may evolve uses custom properties
   encoding from day one — generated readers cannot consult the
   dialect version, and post-parse upgrade hooks cannot rescue an
   unreadable layout. Otherwise the layout is frozen.
3. The PIR bytecode layout is dialect 0.0, and the OIR bytecode layout is
   exactly dialect 0.0. These bytecode-dialect
   versions are distinct from the canonical PIR/OIR identity formats.
   Any other bytecode version spelling fails closed at
   read; property slots are never guessed or upgraded after parse.
4. Inherent state is **properties**, discardable metadata is the
   attr dict; every prop is spelled in the assembly format. `expr`
   trees and `kappa`/`params`/`anchors` dictionaries stay attributes
   (that is what attributes are for).

## 10. Deferred

Region-bodied authoring sugar and named reduce spellings (both:
deterministic pre-seal expansion to the flat/generic form; identity
is defined over the expanded form only), graph regions for unordered
sections (rejected while BIND's precedence half rides SSA dominance
— that unrepresentability is load-bearing), transform-dialect/PDL
authoring, IRDL, DLTI, eqsat/DialEgg for OIR algebra (trigger: first
cost-driven OIR optimization pass). Each enters through
`vocabularies.md`-style admission: with evidence, additively.
