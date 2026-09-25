# Constructed artifact format

This page owns the current concrete artifact profiles implemented by
the compiler, Rust host and independent Lean source interpreter. They specialize the selected
model; it does not redefine arbitrary PIR protocols or establish Fiat–Shamir
security. See [artifact execution](artifact-execution.md) for architecture, use
and assurance boundaries.

## Common transformation

Input is an admitted `zkc.protocol/1` or constrained `zkc.library/1` source and
this exact array descriptor:

```
["zkc.construction/1", entry, producerRole, validatorRole,
 [[publicLabel, [[role, sourceEntryPort], ...]], ...],
 [validatorRngEntryPort, [[sourceFunction, drawOperationSite], ...]],
 validatorBooleanResultIndexDecimal,
 "merlin3.bls12-381.fr64be/1",
 "normalized" | "exact"]
```

Each public binding has a nonempty UTF-8 label of at most 128 bytes and a nonempty
list of ports. Bindings are unique by label and by source port and refer to
serializable admitted ports. Several distinct ports of the same role may share
a label. Labels are application identities, not source symbols; their exact bytes
are retained without Unicode normalization. They authorize equality of those concrete values;
the entry host must check it. A label with only a V port can add a generated P
port. Configuration and application context are additional mandatory root-bound
bytes, not implicit source arguments. The selected acceptance index addresses V
results in source order and must have Boolean type. Rng selection is by actual
root resource flow and allowed operation occurrence, jointly. The occurrence
allowlist may be empty when no selected draw executes. The current construction
supports two roles, static selected dependencies and public counted loops; other
cases must receive explicit refusals rather than an invented implementation.

The last field is the identity policy. `normalized` uses
[normalized source occurrence and root identity](../runtime/artifact-identity.md);
`exact` keeps the whole-source roots specified below. Both are current, the
source notation defaults to `normalized`, and a missing or unknown policy is a
malformed descriptor. The result retains the original descriptor.

Independent artifact admission adds a **public validator profile** on top of
common construction. Every serializable V entry port must occur in a public
binding, including inputs used only in checks or currently unused. V verifier
keys are bound through public configuration. The selected RNG is interpreted by
the transcript; other V resource inputs are refused. P private resources retain
their ordinary custody and issuance rules. An original module with `transcript`
in any local/protocol signature is refused as already constructed. These rules
are checked independently by the native artifact host and Lean reference before
proof execution. The compiler's common transformation may still represent more
general private-verifier flows; successful construction alone does not establish
this artifact profile or any cryptographic security claim.

Output is a constructed ordinary common protocol plus a manifest:

```
["zkc.construction-result/1", descriptor, constructedCommon,
 [[role, generatedEntryPort, ["source", sourcePort] |
                            ["public", publicLabel] | ["transcript"]], ...],
 [[generatedFunction, generatedOperationSite,
   sourceProtocol, sourceLocalCallSite, sourceFunction, sourceOperationSite,
   sourceRole, "original" | "recipe" | "construction"], ...],
 [[role, generatedResultIndexDecimal,
   ["source", sourceRoleResultIndexDecimal] | ["transcript"]], ...]]
```

For library sources, `sourceFunction` names a **configuration**, never a generic
definition or a compiler-generated shared callable. A draw selector names a
configuration or a generic definition; a definition selects the named primitive
in each of its materialized configurations and in every nested copy
([selectors](../spec/profiles/compiler/local-algorithms.md#origins-selectors-and-identity)).
Construction prepares demanded configurations with their original names;
ordinary compilation can still share identical specializations. Every original
declaration is formed,
and the original library tree (including unused declarations) remains the
admission and exact candidate-checking subject. Exact identity also binds it
into the transcript root; normalized identity uses the specified selected closure. `protocol-prepare` exposes the source-shaped closed intermediate; it
is not a replacement source authority or an independently proved elaboration.

Explicit generated helpers have a sixth function field `[generatedName, []]`,
the ordinary logical-definition origin convention. Their separate construction
manifest identifies the original source operation. Full nominal types and explicit
contract/static arguments survive construction. The finite suite selects its
`ChallengeField`; selected draws must match it. Observe helpers bind the exact
payload identity and codec. Codec selection currently requires a unique installed
codec for that kind/domain; adding a second refuses rather than silently changing
an existing construction. A future choice must be explicit and root-bound.

The generated protocol retains source instance identities and call/loop sites.
It may specialize definitions by selected instance, but logical paths refer to
the original instances. Under normalized identity, sites refer to the
independently resolved original source. Common source messages P→V remain messages. V→P messages
become P derivations. Every original message, including erased delivery, is
observed by both roles in source order. All V operations and failures stay in
order; P obtains only demanded admitted recipes. Calls/loops remain compact.
Generated function names never define transcript identity.
The final result mapping is mandatory: removing the selected source RNG output
can shift a later Boolean result. Acceptance is selected through this checked
mapping, never by assuming the original and generated result indices coincide.

`transcript` is an affine, nonserializable capability. Each constructed role has
its own input and output, threaded through calls and loop-carried values. It is
distinct from private `rng`/`nonce` and replaces the selected V draw interpretation,
not every randomness resource. Selected source RNG succession is interpreted by
an explicit mapping, not by equality with transcript transition counters.

The current materialization retains the original selected RNG input and internal
call/loop carriers. The host identifies the selected entry carrier by the checked
descriptor's validator/RNG port and its `source` input-map row and issues it
internally with zero budget. Selected draw successors alias that carrier while
the explicit transcript advances. Entry results originating from the selected
RNG are omitted, so they cannot be mistaken for live fresh-randomness state.
An unconverted sampler (including `random.vector`) anywhere on the selected RNG chain is refused with `construction-selected-rng-sampler:<contract>`, before or after a selected draw. Independently owned private RNG chains remain available. Other original resource results retain their source result mappings. Exact RNG
result provenance is calculated separately from conservative recipe availability;
loop resource permutations compose in logarithmic trip-count work.

Local operation contracts (logical names; physical selection remains explicit):

| Operation | Inputs → outputs | Attributes |
|---|---|---|
| `transcript.observe.TYPE` | transcript, public TYPE → transcript | source protocol, message site, schema, source sender, source receiver |
| `transcript.challenge` | transcript → field, transcript | source protocol, local call site, source function, draw operation site, source role |
| `transcript.draw_index` | transcript, index bound → index, transcript | same logical origin tuple; the installed sampler's bound restrictions still apply |

TYPE denotes an installed serializable logical type. No arbitrary operation is
made pure by having this signature. These operations retain explicit resource
effects. Original/recipe operations map back to source origins in the manifest.
Constructed-common formation and projection do not replace the original-source
execution comparisons. Neither is a proof of the native construction algorithm.

## Canonical logical encoding

Use a binary tree of strings and arrays. A string is byte `0`, u64 little-endian
UTF-8 byte length, then its exact UTF-8 bytes. An array is byte `1`, u64
little-endian item count, then the encodings in order. Reject other JSON kinds;
counts/indices use canonical decimal strings. Logical tree encoding has a
16 MiB total byte ceiling, at most 16 MiB per string, 200,000 nodes, 32,768 items
per array, and maximum depth 64 with the root at depth zero. Source admission
retains its separate 1 MiB source and 4 KiB source-string limits. The root codec
must accommodate canonical public tables/vectors larger than a source identifier.
Check structural ceilings before allocating the JSON tree. This avoids relying on JSON serializer whitespace or
escaping. No Unicode normalization is implicit.

Logical occurrence tree:

```
["zkc.logical-origin/1", entry, currentSourceInstance,
 [["call", sourceCallSite, childSourceInstance] |
  ["loop", sourceLoopSite, iterationDecimal], ...],
 ["message", sourceProtocol, site, schema, sender, receiver] |
 ["challenge", sourceProtocol, callSite, function, operationSite, role]]
```

No local session, worker address, physical kernel or generated helper appears.
The source role/sender/receiver fields use the names written in the original
protocol definition, before its instance role mapping. The identified original
instance supplies that mapping. Actual role ownership is checked separately;
renaming a generated role or helper cannot rewrite source occurrence identity.
Under exact identity the root binding tree is exactly the first record below;
normalized identity binds the tree specified by
[normalized identity](../runtime/artifact-identity.md). Host inputs and configuration have
one form under either policy:

```text
["zkc.artifact-binding/1", originalSource, descriptor, applicationContextHex,
 [[publicLabel, fullNominalType, canonicalPublicWireHex], ...], configuration]

["zkc.artifact-inputs/1", applicationContextHex,
 [[publicLabel, fullNominalType, canonicalPublicWireHex], ...],
 roleSourceInputRecords, configuration]

configuration =
["zkc.public-configuration/1",
 [[verifierSourcePort, fullVerifierKeyType, canonicalVerifierKeyHex], ...],
 [[role, sourceEntryPort, verifierSourcePort], ...],
 [[sourceInstance, receivingRole, messageSite, verifierSourcePort], ...]]
```

Public records in the root follow descriptor order. Input envelopes are keyed
by label and may list public values in a different order; validation associates
each value with its declared label before selecting its setup. Configuration key records follow the
source V entry-port order; include every actual V verifier-key input, and no
proving material. A group-only entry has an empty key list. The host checks
actual inputs against these values and checks P proving material against the
corresponding admitted V key. All hex is lowercase without prefixes. The full
nominal type is the exact type identity representation, with its mathematical
domain defined by the installed table. The source already binds selected
instances, parameters and dependencies. The exact whole-source identity is not
an equivalence hash of source syntax.

The second configuration list selects an authorized setup for **every** original
commitment/proof entry port, across both roles. The third selects a setup for
every executable commitment/proof receive in the constructed entry, under its
fixed public loop counts. Exact zero-trip bodies and callees reachable only
through them are excluded; no compiler-generated inactive instance name belongs
in application configuration. The original-source reference computes the same
coverage from source calls and counts. Unknown, duplicate or missing selections refuse.
The selected receive also retains its admitted schema and full physical type.
A public label targeting several ports requires identical nominal types and
setup selections. The host carries entry selections through the checked
construction map to physical input constraints. Other input shapes are checked
by their operations and finite backend policy; no global PCS rank is inferred.

Verifier-key records follow source validator-port order and may contain different
authorized setups, including equal ranks with different identities. Byte-identical
material may be reused; distinct material claiming identical metadata is rejected.
Proving material is still authenticated against its specifically associated
verifier source port. The proof cannot register or select a setup from its header.
Selection arrays retain their exact order in the root. Applications using a
shared child with different setups on different visits need a dynamic decoder;
the current artifact CLI assigns one setup per static receiving coordinate.

Private wire records also carry full nominal types. Host-issued `rng`,
`nonce` and `prover_key_file` records retain their issuance/import tags and are
checked against the declared nominal source port. An optional verifier-key
duplicate uses the full `verifier_key:multilinear.kzg.bls12-381/1` type, with bytes
identical to its configured key. The selected RNG cannot be
injected. An unused generic definition whose signature already contains a
transcript is refused by the artifact profile, even when preparation omits it.

The proof framing magic remains `ZKCPRF01`. Exact identity binds the whole
original source in the root; normalized identity binds the tree from
[normalized identity](../runtime/artifact-identity.md). Both roots are
`zkc.artifact-binding/1` and each embeds its descriptor, whose policy field
separates them. This does not change the Merlin suite itself.
The original-source operation observation uses `zkc.logical-origin/2` and includes
contract static arguments before attributes. Message/challenge origins absorbed
by Merlin retain `zkc.logical-origin/1`; changing the observation schema does
not change that encoding. Private binding keys, implementation
names and inserted representation conversions are not source operation identities.
Mathematical literal attributes are the canonical specialization of original
literals. Passing the Lean participant checker compares the physical candidate
with the **constructed common source**, not directly with the original library.
Native construction recomputation supplies that separate trusted connection.
The generator and candidate checker reuse the same C++ construction analysis;
recomputation checks consistency and custody, not independent soundness of that
analysis. A shared analysis defect can survive this check.
The independent `Tools.Artifact` interpreter instead starts from the original
library or common source, derives its own configurations, follows source control,
checks application setup selections and consumes the actual proof. Its
primitive requests carry full nominal types and static contract arguments.
Merlin supplies 64 raw bytes; Lean performs big-endian field reduction. Finite
trace comparisons are execution evidence, not a construction-correctness theorem.

Merlin 3 initialization uses static protocol label `zkc.artifact/1`, then
`append_message(b"binding", rootBindingBytes)`. A message observes
`append_message(b"origin", originBytes)` then
`append_message(b"value", canonicalPublicBytes)`. A draw appends its origin with
the same origin label, then `challenge_bytes(b"challenge", 64)` and reduces the
64 bytes big-endian modulo BLS12-381 Fr. Subsequent delivery is still a separate
message observation. Zero is allowed; this is not an exactly uniform sampler.

## Artifact execution

The selected construction turns the remaining P sends into proof writes and V
receives into proof reads. A role runs independently; no source schedule executes
a hidden peer. Explicit local transcript operations perform all framing; the
transport must not absorb a second time. V reads exactly a bounded payload,
canonically decodes it, then reaches the following observation and source checks.
Both roles retain completed transitions on failure. V returns acceptance only
after the actual selected Boolean output is true and the candidate is exhausted.
P writes a complete file atomically only after successful execution.

Proof framing: magic `ZKCPRF01`, 32-byte SHA-256 of canonical root binding, then
each expected message as u64 little-endian payload length and payload. The magic
and digest are redundant checked context; they never authorize configuration.
Expected types and occurrences come from the admitted artifact. Total bytes,
per-message length, instruction and resource ceilings are independently enforced.

Public proving material is persisted and loaded against expected material and V
key identities. No original witness table or proving key is supplied to V. The
independent source reference must request crypto by full public operands and
frame history; an ordinal Boolean/challenge tape cannot establish correspondence.

The configuration is supplied by the invoking application, never extracted from
the proof. Its full canonical V key bytes are the expected public configuration.
Source inputs for public values use `[port, fullNominalType, canonicalWireHex]`. The host
can fill an owned source port from a declared public binding or a configuration
key; an explicitly supplied duplicate must agree exactly. P proving material uses
`[port, "prover_key_file", path, expectedMaterialFingerprintHex, verifierSourcePort]`.
P nonce issuance uses `[port, "nonce", transitionBudgetDecimal]` and the OS source.
The selected transcript input is constructed by the host, not supplied as a token.
The Lean V reference accepts only its actual source inputs and configuration;
it never loads the P proving-material record or private witness.

## Second construction over BLS12-381 Fr

The duplex construction installs
`spongefish0.7.4.keccak.bls12-381.fr64be/1`, associated with `bls12-381.fr`.
It is admitted under either identity policy, with protocol or library source.
The descriptor, artifact root and transcript resource type retain the exact
nominal suite; equal challenge fields do not imply equal challenges or compatible
proof artifacts. Arithmetic/PCS still select arkworks while these transcript
operations select `spongefish/transcript.*`.

The installed byte state is spongefish 0.7.4
`instantiations::Keccak = DuplexSponge<KeccakF1600,200,136>`: overwrite duplex,
136-byte rate, 64-byte capacity, upstream Keccak-f[1600]. It is not SHA3, SHAKE,
STROBE, or spongefish's default high-level protocol. Its frame is
`tag:u8 || label_length:u64be || label || payload_length:u64be || payload`.
Initialization starts from `Keccak::default()` and absorbs tag-0 frames
`("domain", "zkc.artifact/1")`, then `("suite", exact-suite-UTF8)` and the tag-1
`("binding", canonical-root)` frame. The root uses the existing descriptor-version
rules, including context, public inputs and configuration.

Each observation absorbs tag-1 `("origin", logical-origin-bytes)` and
`("value", full-canonical-zkcv-wire)` frames. Each draw absorbs tag-1
`("origin", logical-origin-bytes)`, then tag-2 `("challenge", u64be(64))`, then
squeezes exactly 64 bytes. The next event continues that state. Fr reduction
interprets the wide bytes as a big-endian integer modulo Fr; zero is allowed and
the sampler is not exactly uniform. Existing canonical field/group/PCS decoders
remain strict; received values are not reduced modulo Fr.

The original framing/root rules and affine authority, generation, owner, scope,
budget and failure rules apply. No transcript cloning/reset API is exposed.
The independent Lean reference owns these frame bytes and requests
`["zkc.duplex-request/1", exact-suite, steps]`, with steps
`["absorb", lowercase-hex-bytes]` or `["squeeze", "64"]`. The public primitive
service supplies only upstream byte-state execution and returns the last squeeze;
it does not authenticate source or validate zkc frame semantics. Malformed
requests and unsupported suites/widths fail closed.

This is one construction over one field; there is no all-fields,
protocol-equivalence, side-channel or FS-security claim.

## Installed real algebra contract

The installed BLS12-381 bindings distinguish the field `bls12-381.fr`, the group
`bls12-381.g1`, and the PCS construction `multilinear.kzg.bls12-381/1`.
A logical type retains its kind and nominal identity. Explicit domain and
implementation tables determine the curve; its meaning is not inferred from a
coincidentally named operation. This is a finite installation, not arbitrary
field/domain/plugin support.

For these bindings, `field` carries Fr, `group` carries G1, `groups` carries a
bounded G1 vector, and `nonce` retains a private Fr scalar plus stage/custody.
The curve operations use the same library as the PCS. The installed contracts
include `pcs.equal` on public commitments and:

| Logical kernel | Inputs → outputs | Attributes |
|---|---|---|
| `curve.generator` | → group | none |
| `curve.add` | group, group → group | none |
| `curve.scale` | group, field → group | none |
| `curve.equal` | group, group → bool | none |
| `curve.empty` | → groups | none |
| `curve.append` | groups, group → groups | none |
| `curve.at` | groups → group | canonical natural index |
| `curve.commit` | groups, nonce → groups, nonce | none |
| `curve.response` | field (witness), field (challenge), nonce → field | none |

`curve.commit` consumes an issued nonce once, produces k-scaled bases, and moves
to ready. `curve.response` consumes the ready nonce once and returns k+c*x, then
spends it. No repeated one-base commit, private nonce export, or whole argument
verification callback. Public equations use ordinary curve/field operations.
Transcript state is bound to its selected nominal construction, independently
of the curve implementation. Real group serialization is validated canonical
compressed G1, with bounded vectors and exact consumption.

### Explicit vector and Ristretto domains

Explicit bindings additionally install `ristretto255.scalar`,
`ristretto255.group` and `merlin3.ristretto255.scalar64le/1`. Scalar/vector and
group/MSM operations use their nominal associations. A compatible numeric width
does not allow substitution for Fr or BLS G1. The source's explicit binding
format determines domain admission; both exact and normalized identity support
these domains.

The named Ristretto transcript suite retains the construction's full root,
origin and canonical-value framing, and reduces the raw 64 Merlin bytes in
little-endian order. The existing Fr suite retains big-endian reduction. Public
primitive `/3` transcript requests name the exact suite; a reply for another
suite cannot answer them.

The canonical six-byte ZKCV header distinguishes the value kinds. The domain-specific tags and
payloads are:

| Tag | Logical value | Payload |
|---|---|---|
| 11, 12 | Fr vector, polynomial | u32 LE count, canonical 32-byte scalars |
| 13 | Ristretto scalar | canonical 32-byte scalar |
| 14, 15 | Ristretto vector, polynomial | u32 LE count, canonical 32-byte scalars |
| 16 | Ristretto point | canonical 32-byte compressed point |
| 17 | Ristretto point vector | u32 LE count, canonical compressed points |
| 18 | Ristretto quadratic round | exactly three canonical scalars |
| 19 | KoalaBear field | canonical u32 LE residue, strictly below 2130706433 |
| 20, 21 | KoalaBear vector, polynomial | u32 LE count, canonical u32 LE residues |
| 22 | KoalaBear quadratic round | exactly three canonical u32 LE residues |
| 23, 24, 25 | Fr, Ristretto scalar, KoalaBear matrix | canonical sparse COO; dimensions and entries as below |

Polynomial coefficients are in ascending degree, with no trailing zero; zero
has no coefficients. Sequence limits and exact lengths are checked before
allocation. Domain tags, noncanonical scalars/points, normalization and trailing
bytes are checked independently of the compiler. A quadratic round remains a
distinct fixed-degree value. Availability of a Ristretto round value does not
imply a Ristretto multilinear-table or PCS implementation.

Matrices prefix entries with rows, columns and nonzero count, each u32 LE. Each
entry is row:u32 LE, column:u32 LE and a canonical scalar (32, 32 or 4 bytes).
Entries must be strictly lexicographically ordered, distinct, in bounds and
nonzero. Dimensions are at most 65,536 and the nonzero count at most 1,048,576;
wire and retained-value byte budgets apply independently. Shape, exact length and
canonicality are checked before allocating matrix backing. The logical
`matrix:F` type does not fix storage. The first representations are
`arkworks.fr-sparse-coo/1`, `dalek.scalar-sparse-coo/1` and
`plonky3.koala-bear-sparse-coo/1`, with codec `zkcv.matrix.<field>/1`.

The numerical-only identity `koala-bear` installs field/vector/matrix/polynomial/round
carriers through Plonky3. Codecs are `zkcv.{field,vector,matrix,polynomial,round}.koala-bear/1`;
representations are `plonky3.koala-bear/1`, `plonky3.koala-bear-vector/1`,
`plonky3.koala-bear-polynomial/1` and `plonky3.koala-bear-quadratic/1`.
There is no associated group, RNG, transcript or PCS, nor an installed table or
evaluation-point carrier. These bytes support interactive numerical execution;
they do not make the existing BLS or Ristretto proof construction a KoalaBear
protocol. Domain and service support are checked separately.

### Octic KoalaBear extension

`koala-bear.ext8-binomial3` identifies the extension and ascending basis specified
in [domain values](../spec/domains/values.md#nominal-field-extensions). One scalar
payload is exactly eight canonical u32 little-endian base coordinates (32 bytes),
in ascending power order. Every coordinate must be strictly below `2130706433`.
There is no decimal encoding of an entire extension element. Host `wire` and
`host` inputs carry non-base elements; ordinary natural constants embed into
coordinate zero.

| Tag | Logical value | Payload after `ZKCV 01` and tag |
|---|---|---|
| 26 | extension field | exactly eight base coordinates |
| 27, 28 | extension vector, polynomial | u32 LE element count, then 32 bytes per element |
| 29 | extension quadratic round | exactly three extension scalars (96 bytes) |
| 30 | extension matrix | rows, columns, nonzero count as u32 LE, then canonical COO entries |

Matrix entries contain row and column as u32 LE followed by one 32-byte
extension scalar. The existing order, bounds, nonzero and normalization rules
apply. All eight coordinates participate in equality and zero checks. Unknown
or wrong-domain tags, truncated/trailing bytes, incorrect lengths, noncanonical
coordinates, and malformed COO data refuse. Sequence sizes and byte budgets are
checked before allocation. Wire tags supplement the required explicit nominal
type; sharing a scalar width with Fr or Ristretto does not make their codecs
compatible.

Codecs are `zkcv.<kind>.koala-bear.ext8-binomial3/1`. Default representations are
`plonky3.koala-bear.ext8-binomial3/1` for field, and the same stem followed by
`-vector/1`, `-polynomial/1`, `-quadratic/1` or `-sparse-coo/1`. Native vectors and
polynomials charge `256 + 32*n` retained bytes; matrices charge `256 + 40*nnz`;
scalar and round values charge 512 bytes. The independent logical reference
computes all five carriers; its existing physical-local accounting interpreter
continues to refuse this domain.

The extension also has an explicitly installed RNG and the transcript suite
specified below. Its vector commitments use separate nominal schemes. It adds
no multilinear table, point, group or KZG association. Existing construction
suites do not acquire extension payload or challenge support from these codecs.

Physical diagonal views have no wire or transcript codec. Native observation
records expose their typed factors and backing for diagnostics; they must be
interpreted explicitly for logical observation comparison. They cannot escape
local function boundaries or become ordinary input/output values. The
[domain guide](protocol-libraries.md) records supported operations, physical
choices and the independent registration/checking obligations.

### Checked index values

`index` and `indices` have no nominal field parameter. Their default physical
representations are `native.index/1` and `native.indices/1`; their canonical
codecs are `zkcv.index/1` and `zkcv.indices/1`. Following the existing five-byte
`ZKCV\x01` prefix, tag 31 carries exactly one u64 little-endian value; tag 32
carries a u32 little-endian count and that many u64 little-endian values.
Decoding rejects wrong tags, truncation, trailing bytes and resource-limit
violations. The sequence count and total length are checked before allocation.

The MLIR logical carriers are `ui64` and `tensor<?xui64>`, respectively. They do
not inherit unchecked `arith` wrapping semantics: the registered `algebra.index_*`
operations implement the checked source contracts. `native/index.*` and
`native/indices.*` are the installed runtime implementations.

### Authenticated table wire values

The [vector commitment schemes](../spec/domains/oracles.md) share the existing
`ZKCV\x01` prefix. A root carries exactly one 32-byte digest; a path or root
sequence carries a u32 LE count followed by that many 32-byte digests.

| Tag | Value |
|---|---|
| 33, 34 | base-field scheme root, path |
| 35, 36 | extension-field scheme root, path |
| 37, 38 | base-field, extension-field root sequence |

Decode requires the expected nominal scheme and exact byte length. Paths are
bounded to 24 digests; actual verification separately requires the expected
height's exact depth. Roots do not carry a trusted shape. Private opening states
and state sequences have no wire encoding. These roots and paths require no
KZG setup; nominal KZG values retain their existing setup requirement.

### Octic-field transcript and index sampling

`merlin3.koala-bear.ext8-binomial3.rejection31le/1` is a distinct installed
construction suite. It binds the existing artifact context and structured
origins and observes canonical base/extension scalar and sequence values,
matching Merkle roots/paths, Boolean and index values. Payload domain and
challenge domain are independently checked; observation does not embed or
re-encode a base-field value as an extension value.

For a field draw, append its origin, then request 64 bytes with label
`challenge`. Interpret sixteen little-endian u32 words, mask to 31 bits and
accept coordinates strictly below 2130706433. The first eight accepted words
are the extension element in ascending basis order. Continue with the same
label if necessary, for at most sixteen blocks. Exhaustion reports
`challenge-rejection-limit`; no rejected word is reduced modulo the field.
Discard unused words of the final block. Retries consume one logical transcript
action in total, while every actual block remains in primitive replay history.

`random.index<F>(rng,bound)` and its selected `transcript.draw_index<T>`
interpretation return a non-field `index`. The bound must be a positive u64
power of two, hence at most 2^63. Invalid bounds refuse with `query-bound`.
Append the origin and `query-bound` with its u64 LE bytes, then draw 64 bytes
under `query-index`. Mask the first u64 LE word by `bound-1`. The exact uniform
map is conditional on uniform input bytes; Merlin security is a separate
premise. Bounds and query occurrences remain explicit in the source schedule.

The construction recognizes selected field and index draws. It reconstructs
eligible public operands under its existing bounded recipe rules; the
admitted `index.constant` recipe does not make arbitrary pure kernels replayable.
The independent Lean sampler includes forced retry and exhaustion tests.

### Diagnostic trace policy

The `produce-artifact` and `validate-artifact` CLI commands accept a trailing
`--trace=full|none`. Full tracing is the default. Its report includes
`"trace":"full"` and the existing source-normalized `events` array. Disabling
tracing reports `"trace":"none","events":null`; an absent observation is not an
empty successful observation. The flag does not change the proof format or
binding identity.

Both modes admit the source, construction and physical candidate, perform actual
backend checks and transcript transitions, validate proof framing, and enforce
runtime/resource limits. The disabled mode skips diagnostic origin lookup,
public-value event encoding and observer budgets. Consequently it can succeed
where full tracing exhausts diagnostic memory. Observer-specific consistency
checks are also omitted; mandatory source/construction/physical checking remains
in admission. No full observational or resource-equivalence claim is made across
these modes. Use full tracing for differential observation comparisons and name
the policy in performance evidence.

### BN254 scalar and pairing groups

The BN254 extension uses separate nominal identities `bn254.fr`, `bn254.g1`,
and `bn254.g2`. Following `ZKCV\x01`, the installed tags are:

| Tag | Value | Payload |
|---|---|---|
| 40 | scalar | canonical 32-byte little-endian Fr |
| 41, 42 | vector, polynomial | u32 LE count, followed by Fr elements |
| 43 | quadratic round | exactly three Fr elements |
| 45 | matrix | rows, columns, nonzero count as u32 LE, followed by canonical COO entries |
| 46, 48 | G1, G2 | arkworks 0.6 canonical compressed point, 32 or 64 bytes |
| 47, 49 | G1 vector, G2 vector | u32 LE count, followed by corresponding compressed points |

A matrix entry is row/column as u32 LE and one Fr value. Existing shape,
ordered-nonzero COO and normalized-polynomial rules apply. Group decoding checks
canonical encoding, curve membership and prime-order subgroup membership. Sizes
and budgets are checked before allocation; wrong nominal tags and trailing bytes
refuse. These types install no PCS, transcript suite or Fiat–Shamir construction.

The snarkjs adapter is a separate codec. It uses exact `groth16`/`bn128` JSON
objects with canonical decimal base-field coordinates, fixed projective shapes,
and G2 coordinates in `[c0,c1]` order. It does not use Solidity's coordinate
order. Unknown, duplicate, missing or extra fields and noncanonical scalars or
points refuse. Bare snarkjs JSON carries no zkc invocation context: importing
it explicitly reconstructs internal framing under the application's expected
statement/key and then runs the actual verifier equation. Internal `ZKCPRF01`
bytes and external JSON are distinct formats, even when proof points agree.

### Logical resource-unit ports

The closed logical type `resource_unit:D` and physical type
`resource_unit:D@logical.resource_unit/1` use the exact nominal slot grammar and
operation contracts in [logical resource units](../spec/domains/values.md#logical-resource-units).
They have no wire encoding or generic static-sort interpretation. A physical
binding selects `logical/resource_unit.create`, `logical/resource_unit.pass`,
or `logical/resource_unit.consume`, with exactly one nominal slot argument and
no operation attributes. Ordinary ordered ports and affine use checks remain
present even though the value payload is empty. Runtime ownership metadata is
not a serializable permission or cryptographic credential.
