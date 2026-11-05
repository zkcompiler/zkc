# Shared declaration catalog

`zkc.contract-declarations/0` is neutral declaration data. It contains no MLIR
objects, backend function pointers, Lean declarations or admission certificates.
The catalog owns operation identities, kinded signatures, requirements, type
permissions and semantic facets. Implementations and mathematical laws remain
independently interpreted. The [foundation cutover](foundation-interfaces.md)
records its delivery status and consumer-visible changes.

The declaration contribution set is the source of truth. Build-time generation
checks uniqueness, dependencies, term scopes, facet positions and signature
agreement. C++/Language, MLIR and Rust consume generated projections of these
same declarations. The neutral serialized inventory is also the data face for
a later formal consumer; generation creates no files under `lean/` and assigns
no theorem or semantic function to a catalog row.

The built-in contribution is authored in the [shared source](../../../common/catalog/README.md),
independent of C++ or Rust syntax. Compiler configuration projects ordinary
TableGen records; the native generator validates them before producing C++ and
MLIR inputs. Cargo independently validates the same source and projects static
typed Rust metadata. Neither build invokes the other language's compiler.
Generated files stay in build outputs. A projection may select consumer data;
it must not silently discard a malformed declaration or grant a privilege from
an authoring-class name. Native contribution assembly remains explicit and
does not install a runtime implementation by adding a declaration.

## Inventory

The root has exactly `format`, `sorts`, `types`, `operations`, `members`, `rules`,
`capabilities`, `exports`, `families`, `associatedTypes`, `mathematicalIdentities`,
`mathematicalIntrinsics`, `consumerProfiles`, `frontendDeclarations`,
`frontendRules`, `frontendNotations`, `frontendConstructors`, `frontendHomes`,
`serviceSignatures`, `serviceMethods`, and the [installed-instance](#installed-instances)
tables `domains`, `logicalTypes`, `frameTags`, `codecs`, `aggregateFrames`,
`randomServices`, `limits`, `finiteDefinitions` and `domainConstructors`. The
format tag is `zkc.contract-declarations/0`. Every list follows the contribution dependency
order and then its explicit declaration order. No consumer may infer meaning
from an ordinal instead of the declared identity. Unknown fields, duplicate
identities or keys, invalid Unicode and unresolved references refuse.

The following record fields are exact; `?` marks an optional field, not a
field containing a question mark. Indices and counts in declaration records are
nonnegative JSON integers. Static naturals and arbitrary precision literals use
canonical strings as defined below.

```text
Kind       = {kind, sort}
Type       = {name, parameters, copy, drop, custody, nativeLocal,
              mathematical, participants, constructible, message,
              sourceData, collection, setup}
Capability = {name, parameters, requires, permits}
Member     = {name, owner, result}
Rule       = [premise, conclusion]
Family     = {family, elementConstructor, resultConstructor}
Associated = {sort, member, constructor}
Export     = {module, name, constructor} | {module, name, predicate}
Operation  = {name, scope, stage, parameters, signature, requirements,
              facets, derivedCounterpart?}
Meaning    = {name, laws}
Intrinsic  = {name, identity, domainKind, naturals, domainPoints, scalar}
ConsumerProfile = {name, implementation, typeConstructors,
                   parameterValidators, operations}
ConsumerOperation = {operation, scope, stage, parameters, signature, requirements}
```

`sorts` is the list of declared sort names. A Kind has `kind` equal to `Domain`,
`Type` or `Nat`; `sort` is a declared sort exactly for Domain, and empty otherwise.
`parameters`, `owner` and `result` use ordered Kind records as applicable.
Custody is `PublicValue`, `PrivateImmutable` or `Affine`. Permissions are
Booleans with the existing type contract: affine types are not copyable;
ordinary immutable values are copyable and droppable. Transport, codec
availability and authorization remain separate facts. The retired
`commonGeneric` interpreter-profile field is absent. Native container names
`scalar` and `capability` are not logical constructors and have no catalog
rows. Actual logical fields, randomness, transcripts and resource slots retain
their own constructor identities.

The source-vocabulary columns describe how the frontend uses a constructor.
`sourceData` is true when source declarations may name the constructor as
native data. `collection` is null or `{rank, element}`: `rank` is 1 or 2 and
`element` is `parameter` (the element is the value type of the first
parameter: `field` over a Field domain, `group` over a Group domain, or the
Type argument itself; a constructor whose first parameter is none of these
has no `parameter` element), `index` or `byte`. A `byte` collection has an
extent, but source declarations do not traverse its elements. `setup` is null, `prover` or
`verifier` and marks the setup-key constructors. These columns grant no
codec, transport or execution authority.

An operation's scope is an ordered list of exact tagged terms:

```text
Term = {kind: "root", name, parameter}
     | {kind: "project", member, parent}
     | {kind: "apply", constructor, arguments}
     | {kind: "natural", value}
Signature = {kind: "fixed", inputs, outputs}
          | {kind: "numerical", fieldTerm, result}
Port = {term} | {constructor, arguments}
Requirement = {capability, arguments}
```

`parent` and `arguments` refer to earlier scope terms; roots introduce static
parameters. Projected kinds come from the named Member, application kinds from
the named constructor, and natural terms have kind Nat. Logical ports use an
explicit complete-Type term or constructor application. Complete-Type ports are
kind-checked independently of authoring stage and TableGen class inheritance.
Consumer profiles separately select supported instantiated signatures; the
complete-Type form does not grant arbitrary source operations or interpretations. Requirements are kind-checked capability
applications. The stage is `Source`, `Construction`, `CompilerGenerated` or
`Physical`. A fixed signature has ordered Port lists. The numerical signature
is an explicit closed family, rather than a hidden generic-verifier exception:
`fieldTerm` selects its Field scope term and `result` is `map`, `sum` or
`product`. Its static actuals are the scope roots followed by one Boolean mask.
Inputs are a u64 row count followed by one field vector for each true mask bit
and one field scalar for each false bit, in mask order. The output is one field
vector for `map`, otherwise one field scalar. This closed family has exactly one Field root and its Field requirement; it
has no fixed-port approximation. The mask has at most 1,023 bits.
The numerical expression independently checks that complete positional ABI.

Facets preserve the installed closed vocabulary. Every facet is an object with
`kind` and exactly the fields below. Port indices refer to the indicated input
or output of the resolved signature. Optional ports use null, not a negative
sentinel. An unknown facet is refused by a consumer requiring a complete facet
interpretation and grants no positive optimization fact.

| Kind | Fields beyond `kind` |
|---|---|
| `PublicReplay`, `DeterministicData`, `AcceptanceGuard`, `Conjunction`, `SourceHistory`, `ManagedHistory` | None |
| `Mathematical` | `identity`: a declared mathematical identity |
| `History` | `stateInput`, `stateOutput` |
| `Succession` | `stateInput`, `stateOutput` |
| `Observation` | `stateInput`, `payloadInput`, `stateOutput` |
| `Sampling` | `provider` (`Entropy` or `Transcript`), `domain` (`Field`, `FieldVector`, `BoundedIndex` or `IndexBlock`), `stateInput`, `valueOutput`, `stateOutput`, `boundInput` (port or null) |
| `Diagonal` | `factorsInput`, `valuesInput`, `resultOutput` |
| `Contraction` | `coefficientsInput`, `valuesInput` |
| `Coset` | `shiftInput`, `sizeInput`, Boolean `sizeIsLength` and `foldedOutput`, `vectorOutput` (port or null) |
| `DomainValue` | `rule`, `output`; `Constant` additionally has `parameter`, `Length` has `input`, and `Multiply`/`Divide` have `input` and `otherInput` |

`DomainValue.Constant` reads the declared static parameter, not an operand of
a nullary operation. Unused legacy default fields are absent. The other rules
derive values under their mathematical domain contract; they do not license
removing a reached check or assume nonzero divisors.

`Succession` states a resource identity transfer: output `stateOutput` is the
successor of the exact resource received at input `stateInput`. The operation
consumes that input and returns the same resource identity, with the same
`resource_unit` type and Slot, at that output. Both ports are `resource_unit`
applications of the same scope term, the operation's scope has that Slot root,
and the signature has no other `resource_unit` input or output, so custody is
neither duplicated nor dropped. The facet establishes identity succession
only: it grants no value equality, purity, reordering or speculation, and no
operation acquires it from a matching signature shape. Validation refuses
ports outside the signature, ports of another type, unequal resource types and
any additional resource input or output. The native exact-root analyses at the
Protocol and Exec stages connect a successor to its received root only through
this facet, never through an operation's name. The operations whose scope has
a Slot root are the resource-unit operations, and their bound ports are the
declared `resource_unit` ports over the selected Slot.

### Deterministic data

`DeterministicData` is the nullary operational facet
`{"kind":"DeterministicData"}`. Under the same installed exact admitted
implementation, equal complete logical inputs and parameters have equal normal
results or the same logical stop. The interpretation includes partial
operations. It asserts neither totality nor speculative execution, equal
resource exhaustion or budgets, sampling/randomness laws or cryptographic
security. It grants no mutable-state, setup or private-service authority.

The native projection is `OperationContracts::deterministicData`, default false;
the Rust typed projection is `Facet::DeterministicData`. The exported object
has no fields beyond `kind`; unknown fields, unknown facet kinds and duplicate
facet kinds are refused. This widens the closed facet vocabulary at
`zkc.contract-declarations/0`; it does not introduce an alternate arity or
compatibility reader. Independent formal readers require their own vocabulary
update before consuming these rows; this native projection establishes no
formal correspondence.

Each operation is enrolled explicitly in the authored declaration source.
Neither a naming prefix nor mathematical meaning, purity or Copy grants this
interpretation. An unknown operation or an operation lacking the facet has no
positive deterministic-data fact. A custom/selected implementation does not
inherit the unselected interpretation; its exact installed interpretation must
be established separately. A declaration alone never installs executable code.

Consumers must additionally admit the exact binding, complete nominal data
types and parameters, and every transitive closed function and outcome path.
Generic containers can carry Type parameters and variant payloads: recursive
immutability remains a call-site obligation. Scope/outcome administration does
not become ordinary data. The distinct `PublicReplay` facet retains its total,
restricted public-construction contract; partial deterministic operations do
not acquire it. The [request construction contract](../ir/verifier-requests.md)
defines how continuing prefixes and replicated stopped outcomes are used.

The initial finite installation covers checked scalar index/word/Boolean/field
operations and guards; immutable sequence, indices, field-array, fixed-vector,
commitment-list and field-vector data operations; polynomial and coset/domain
arithmetic; bytes and deterministic codecs; fixed hashes and explicit immutable
SHAKE snapshots; and `oracle.check`/`oracle.check_many` verification on supplied
commitments, coordinates, rows and proofs. Logical vector/point/table
conversions and Montgomery byte codecs do not authorize physical representation
conversion. Variants use structural execution operations rather than separate
catalog operation rows.

The eleven installed relation-table operations are also deterministic partial
operations over an immutable admitted Bundle: rows, shape, input, scope, point,
points, widths, policy, interactions, interaction and record-points. Their exact
asset identity, table, carrier and input values are part of the interpretation.
The exact admitted asset bytes are an interpretation premise, not a conclusion
from digest equality or a hash injectivity theorem. The asset registry admits
those bytes against their identity and refuses duplicate replacement; it is
read-only during invocation. Missing assets and resource
admission remain execution obligations. A dependency report must retain the
asset parameter and exact selected binding; it may not erase them because the
asset is not an SSA operand. This enrollment grants no relation soundness,
compiler correspondence, transcript binding or general asset lookup purity.

Randomness, transcript, external and resource operations, physical conversion,
arbitrary callbacks, oracle commitment/opening operations, PCS operations and
private opening-state/setup services receive no such authority. Their types,
copy permissions or a deterministic-looking implementation name do not enroll
them. Exact current coverage is the authored facet inventory, checked by the
finite witness in `common/catalog/test_deterministic_data.py`.

### Mathematical laws

A mathematical identity's `laws` is null or exactly `{algebra, signature,
associative, commutative, total, leftIdentity, rightIdentity, annihilator,
scalarAction, access}`. `associative`, `commutative`, `total` and `scalarAction` are Booleans;
the other fields use the following closed vocabulary:

| Field | Values |
|---|---|
| `algebra` | `FieldRing`, `GroupModule`, `Access` |
| `signature` | `FieldConstant`, `FieldBinary`, `GroupBinary`, `GroupAction`, `ElementAccess`, `MatrixAccess` |
| `leftIdentity`, `rightIdentity`, `annihilator` | `None`, `Zero`, `One`, `GroupIdentity` |
| `access` | `None`, `Element`, `MatrixCell` |

Generation checks compatible combinations, including the domain of an identity
and the matching access signature. These are declarations of mathematical obligations, not
generated proofs or execution-effect facts. An intrinsic names its meaning,
domain kind (`Boolean`, `Index`, `Collection`, `Field`, `Group` or `Quotient`)
and number of static natural arguments, with Boolean domain-point
and scalar eligibility flags. These internal intrinsic bindings do not publish
ordinary source function names; library declarations own those APIs.

Catalog presence grants no purity, totality, admissibility or permission to
remove a reached call. Mathematical totality does not erase execution budgets
or allocation failures. Installation metadata is a separate projection, checked
against complete logical and represented signatures.

## Installed instances

The installed-instance tables declare which nominal domains, logical type
instances, codecs and frames exist. They separate four facts:

1. **Declared meaning:** domains, their associated members and capabilities,
   field structure, and the named transcript and commitment algorithms.
2. **Permitted logical use and encoding:** logical type instances, codecs,
   frame tags and aggregate frames, random services, shared limits and the
   source vocabulary.
3. **Available physical choices:** representations, provider preferences,
   installation units, arithmetic forms and calling conventions, in the
   separate [native installation](native-installation.md) document.
4. **Actual compiled support:** the selected target's registered handlers,
   exact signatures, storage owners and enabled contributions.

The first three are generated facts. The fourth stays an independent check:
a declared domain, codec or representation without a registered handler is
refused by that target, and a provider preference is not an installation
grant. This document never references the native-installation document.

Every table is an explicit list of rows. No identity is formed by
concatenation, by a family of rows or by a loop, and no row inherits facts
from a name, prefix or spelling. Row order is declaration order and is part of
the published bytes: the [structured-source catalogue](structured-source.md)
emits domains with their members and capabilities, and random services, in
this order. Identities use the catalog name rule: 1 to 256 characters, a
letter or `_` first, then letters, digits, `_`, `.`, `-` or `/`. Counts in
these tables are JSON integers from 0 to 1,048,576; a limit's `value` has its
own range.

```text
Domain         = {identity, sort, members, capabilities}
                 plus exactly {field} for sort Field, {transcript} for sort
                 Transcript, {commitment} for sort Commitment
Field          = {characteristic, structure, twoAdic}
Structure      = {kind: "prime"}
               | {kind: "extension", over, degree, reduction}
TwoAdic        = null | {convention, maximalRoot, twoAdicity, ordering}
Transcript     = {family, hash, decoder, bindsSuite}
Commitment     = {scheme: "keccak256Rows", digestBytes}
               | {scheme: "poseidon2Rows", permutation, digestBytes,
                  digestWordBytes}
               | {scheme: "multilinearKzg"}
LogicalType    = {kind, domain}
FrameTag       = {tag, layout, shared}
Codec          = {identity, kind, domain, frame}
AggregateFrame = {constructor, domain, tag}
RandomService  = {contract, field}
Limit          = {name, value, unit, owner, scope, phase}
FiniteDefinition  = {identity, mode, operation, collection, filtered}
DomainConstructor = {identity, kind, axis}
```

### Nominal domains

A domain's identity is unique across `domains` and `codecs`. Its sort is a
declared sort other than `Codec` and `Slot`. `members` is an ordered list of
`[member, identity]` pairs: each member is a declared Member whose owner sort
is the row's sort, at most once per row, naming a domain of the member's
result sort. `capabilities` is an ordered list of unique declared unary
predicates over the row's sort, closed under `rules`.

A capability's `requires` and `permits` name members of its sort, each at most
once across both lists; a capability that names a member is a unary domain
predicate. A row holding a capability has every member that capability
requires, and a row has a member that some capability names only while holding
a capability that names it. `PairingField` requires `PairingG1` and `PairingG2`
and permits `PairingGT`; `ExtensionField` requires `BaseField`. The pairing
groups of a `PairingField` row are distinct and each holds `ScalarAction` with
this field as `Scalar`. `PointField` and `EvaluationField` members occur only on
`multilinearKzg` commitments.

`characteristic` is the field's characteristic as a canonical decimal at most
1,024 digits long, at least 2; for a prime field it is also the order. It
bounds the canonical representatives of natural casts. `CharacteristicNotTwo`
holds exactly when it is not 2.

`structure` fixes each element's coordinates:

- `prime`: the element is one canonical integer below the characteristic.
  Exactly the rows holding `PrimeField` have this structure, and they have no
  `BaseField` member.
- `extension`: the field is `B[X]/(X^degree - sum(c * X^e))`, where
  `reduction` is a nonempty list of the `[e, c]` terms in strictly decreasing exponent order,
  each exponent below `degree` (at least 2), and each coefficient a nonzero
  canonical decimal below the characteristic, read in the prime subfield of
  `B`. `over` names `B`: `BaseField` is the row's `BaseField` member, which
  has the same characteristic; `PrimeSubfield` is `GF(characteristic)`. The
  ordered basis is `1, X, ..., X^(degree-1)`, and each coordinate is a `B`
  element in `B`'s own basis, recursively. Rows over `BaseField` are exactly
  the rows holding `ExtensionField`. A row over `PrimeSubfield` holds neither
  `PrimeField` nor `ExtensionField` and has no `BaseField` member.

For example, `koala-bear.ext4-binomial3` is over `BaseField` with degree 4 and
reduction `[[0, "3"]]`; `gf2-64.pentanomial-4-3-1` is over `PrimeSubfield`
with degree 64 and reduction `[[4, "1"], [3, "1"], [1, "1"], [0, "1"]]`; its
cubic extension is over `BaseField` with degree 3 and reduction
`[[1, "1"], [0, "1"]]`, so an element is three GF(2^64) coordinates of 64 bits
each. Primality, irreducibility and root orders are trusted mathematical
declarations: validation checks their shape and references, not these
properties. Independent witnesses, such as the field tables of the native
tests and the Python field references, check them separately.

`twoAdic` is non-null only on `prime` rows. `maximalRoot` is a canonical
decimal below the characteristic, declared to be a primitive
`2^twoAdicity`-th root of unity,
`twoAdicity` is between 1 and 64, and `convention` is a unique identity naming
the coset convention. `ordering` is `powers`: the coset of size `2^k` with
shift `s` lists `s * w^i` for `i = 0 .. 2^k - 1`, where
`w = maximalRoot^(2^(twoAdicity - k))`. An extension uses the convention of
its prime base. `TwoAdicField` holds exactly when the row, or its prime base, has a
convention.

A transcript row names its algorithm by `family`; the other columns are typed
facts about that specified algorithm, not a recipe. Equal columns never make
two suites interchangeable, and a consumer admits a suite by its exact
identity. The row has a `ChallengeField` member.

| Column | Values and their specified laws |
|---|---|
| `family` | `merlin3`: Merlin 3 with domain `zkc.artifact/0` ([transcript state](../ir/construction.md#transcript-state-and-occurrence-identity)); `spongefish0.8.0`: the Spongefish 0.8.0 Keccak sponge with the frame encoding of [hash-chain suites](../ir/construction.md#encoding); `hash-chain`: [native hash-chain suites](../ir/construction.md#native-hash-chain-suites) |
| `hash` | `keccak256` exactly for `hash-chain`, otherwise null |
| `decoder` | `fr64be` and `rejection31le` as in [decoders](../ir/construction.md#decoders); `rejection64le` as in [UniformIndex realization](../runtime/services.md#uniformindex-realization); `scalar64le` reads one 64-byte answer as a little-endian integer and reduces it modulo the challenge field's characteristic |
| `bindsSuite` | Whether initialization absorbs the complete suite identity under label `suite` before the binding root |

`fr64be` and `scalar64le` require a prime challenge field; `rejection31le`
and `rejection64le` require a characteristic below `2^31` and `2^64`
respectively. A transcript row holds `Transcript` and `FieldTranscript`.

A commitment row names its scheme. `keccak256Rows` is the
[binary Keccak row scheme](../domains/oracles.md#installed-binary-merkle-schemes)
with `digestBytes` 32. `poseidon2Rows` is the
[digest-generic row scheme](../domains/oracles.md#digest-generic-merkle-schemes)
over the [Poseidon2 instance](../domains/oracles.md#poseidon2-instances)
named by `permutation`: `koala-bear.poseidon2-16`, `baby-bear.poseidon2-16` or
`goldilocks.poseidon2-8`, each the pinned Plonky3 0.8.0 default parameter set
for that field and width. The permutation's field is the `ValueField` member
or its prime base, `digestBytes` is 32, and `digestWordBytes` is the element
width of that field's codec frame. `multilinearKzg` is the
[multilinear KZG scheme](proof.md#pcs-message-bytes); it requires an
authorized setup, and logical types of the constructors with a non-null
`setup` exist only over `multilinearKzg` commitments. Every commitment row has a `ValueField` member. A hash,
permutation width and digest width alone never identify a scheme.

### Logical type instances

`logicalTypes` lists each admitted instance of a declared nullary or unary
constructor, other than `variant` and `resource_unit`, which have their own
formation. A nullary instance has the empty domain; a unary instance names a
domain whose sort is the constructor's Domain parameter sort. Pairs are
unique. An instance supplies or requires no codec, representation, capability
or implementation.

### Frame tags and codecs

Every canonical value frame begins with ASCII `ZKCV`, byte 0 and one tag byte.
`frameTags` owns the tag space: each `tag` is unique, between 1 and 255. The
[message chapter](messages.md#canonical-value-frames) specifies each
`layout`: `Scalar`, `Vector`, `SparseMatrix`, `MerkleRoot`, `MerklePath`,
`DigestRoot`, `DigestProof`, `PcsCommitment`, `PcsProof`, `Table`, `Sequence`,
`Variant` or `FieldArray`.

`shared` is null when exactly one codec or aggregate frame uses the tag.
Otherwise it is `{kind, scheme}`: the tag is used by exactly the codecs of
logical kind `kind` over commitment domains of scheme `scheme`, at least two of
them, all with the tag's layout. Such a frame does not name its scheme. It is
decoded under the expected type, whose commitment row supplies the digest and
word widths and the canonical word rule; bytes never select among the
sharers. The same bytes may be canonical under two sharers, and the declared
type, not the frame, carries the scheme.

A codec has a unique identity, a `(kind, domain)` pair in `logicalTypes`, and
the declared predicate `Encodes.<kind>` over `Codec` and the domain's sort
(only `Codec` for a nullary payload). At most one codec exists per pair.
`frame` is null or an object whose `tag` names a frame tag; its other fields
follow the tag's layout:

| Layout | Frame fields |
|---|---|
| `Scalar`, `Vector`, `SparseMatrix` | `tag`, `elementBytes` |
| `PcsCommitment` | `tag`, `bytes` (the complete frame) |
| `PcsProof` | `tag`, `bytes` (the complete frame for arity zero), `bytesPerArity` |
| `MerkleRoot`, `MerklePath`, `DigestRoot`, `DigestProof`, `Table` | `tag` |

A codec has a frame exactly when its kind's type row has `message`, except the
standalone public table input frame, layout `Table`, which is input-only. The
codec's kind fixes its tag's layout: `field`, `group`, `bool` and `index` use
`Scalar`; `vector`, `groups`, `indices` and `bytes` use `Vector`; `matrix`
uses `SparseMatrix`; `table` uses `Table`; and `commitment` and `proof` use
`MerkleRoot` and `MerklePath` for `keccak256Rows`, `DigestRoot` and
`DigestProof` for `poseidon2Rows`, and `PcsCommitment` and `PcsProof` for
`multilinearKzg`. Only aggregate frames use `Sequence`, `Variant` and
`FieldArray`, each for its own constructor.
Merkle and digest frames take their widths from the commitment row. For a
`field`, `vector` or `matrix` codec, `elementBytes` follows the structure:
the least number of bytes holding `characteristic - 1` for a prime field;
`degree` times the base's element width over `BaseField`; and `degree / 8`
over `PrimeSubfield` of characteristic 2. A field whose structure gives no
width, an extension over `PrimeSubfield` of odd characteristic or a degree not
divisible by 8, has no `field`, `vector` or `matrix` codec. The `group` and `groups` codecs of
one group have equal `elementBytes`. These facts fix bytes; they do not grant
transport, which also requires a canonical-frame representation and an
installed implementation.

### Aggregate frames

An aggregate frame row grants a message frame for one constructor: `sequence`
and `variant` with the empty domain, and `field_array` with the one Field
domain it names; that field has a `field` codec with a `Scalar` frame, which
encodes the array's elements. Each `(constructor, domain)` pair has at most
one row. Encoding restrictions stay separate from type formation:
`field_array` over a field without a row is a valid logical type without a
message frame, and a row is required before any reader admits such a frame.

### Random services

A random service names a unique `contract` and the Field domain it draws
from. Services and the `rng` logical types correspond one to one through that
field. The random-service consumer selects `serviceMethods` owned by the nominal
frontend declaration `service.random`, then gates them by the field's capabilities.
Another constructor's methods do not enter that profile through a shared name.

### Limits

`limits` holds the installed policy ceilings that independent implementations
in more than one language enforce for the same contract. A format's own bounds,
such as an interface document's node ceiling or a program's carrier bounds,
belong to that format's specification, and shared conformance cases at each
bound keep its readers in agreement. `name` follows the catalog name rule
and is unique; `owner` and `scope` are nonempty; `value` is a JSON
integer from 0 to 2^63 - 1; `unit` is one of `roles`, `bytes`, `elements`, `entries` or `steps`;
`owner` names the owning component; `scope` states what one count covers; and
`phase` is `formation`, `admission`, `publication` or `execution`. A shared
value does not merge two contracts: native, export, message and target
ceilings keep separate rows or owners even when numerically equal. A reached
ceiling is an observable refusal, not an implementation detail. The table below
states the rows; the documentation check compares it with the catalog.

| Name | Value | Unit | Owner | Scope | Phase |
|---|---:|---|---|---|---|
| `protocol.roles` | 1,024 | `roles` | IR / Protocol | Ordered role roster of one protocol, participant or Entry | `admission` |
| `record.roles` | 1,024 | `roles` | Frontend / Language | Role parameters of one distributed record telescope | `admission` |

### Source vocabulary

`finiteDefinitions` lists the admitted finite-definition identities. `mode`
is `math` or `local`; `operation` is `fold` or `collect`; `collection` is
null for `fold` and otherwise one of `vector`, `groups`, `sequence`, `indices`
or `field_array`; `filtered` selects the predicate form and is false for
`field_array`. `domainConstructors` lists the finite domain constructors with
their `kind` (`Elements`, `Indices`, `Range`, `Zip`, `Product`, `MatrixRow`,
`MatrixColumn`, `MatrixCoordinates` or `SourceArray`) and `axis` (0 or 1).
Identities are unique within each table. A library finite or domain
declaration names a row;
the identity is a lookup key and the columns are its meaning.

### Validation

The generator, the native TableGen backend and the Rust build independently
check every rule in this section, including exact record shapes, unique keys,
reference resolution, sort and member typing, rule closure, structure and
characteristic agreement, convention placement, codec and frame agreement,
tag ownership, the service correspondence and the vocabulary sets. They check
the published schema; they are not three proofs of a field or cryptographic
algorithm. Tests against the actual kernels and codecs, independent byte
vectors and negative mutations remain separate evidence.

## Static values and typed signatures

Closed declaration arguments are:

```text
Argument = ["domain", sort, identity] | ["type", Type]
         | ["nat", decimal] | ["mask", [boolean...]]
```

`Type` here is the [logical type tree](logical-types.md), not a catalog Type
declaration record. Domain identities retain their declared sort and nominal
identity. The `Slot` sort names a compiler-generated resource slot, not an
algebraic domain or a global installation. Its identity is 1–128 ASCII
characters, starts with a letter, and continues with letters, digits, `_`, `-`
or `.`. `resource_unit` has one Slot parameter, and its create/pass/consume
contracts share that explicit root. The existing byte spelling is unchanged.
Closed slot formation grants no setup, construction or source authority. The mask case is restricted to the compiler-generated numerical
family's positional signature; it is neither a natural nor a nominal domain.
Its complete input/output signature is derived from the mask and field and
must agree in every generated projection. No generic extension may introduce
an unchecked argument escape.

MLIR realizes these values through immutable types and attributes. Resolved
signature checks compare their structure directly. Native neutral APIs use
their own typed representation. Canonical text conversion belongs to external
format boundaries; ordinary verification does not print and reparse values.

## Invocation parameters

An operation parameter schema is exactly `{validator, minimum, maximum,
fieldTerm?, assetFormat?}`. `maximum` is a nonnegative count or null for a
variadic schema. A required field term selects the actual nominal field.
The validator names below are the complete current vocabulary. They specify
structured parameter values, not arbitrary string arrays or callback names.

```text
Parameter = ["natural", decimal]
          | ["field_literal", domain, "natural"|"bits", digits]
          | ["asset", format, digest]
          | ["expression", expression]
          | ["origin", origin]
```

Decimal naturals match `0|[1-9][0-9]*`; ordinary indices fit u64. A field natural
is below the selected modulus. Binary field bits use the existing minimal
lowercase `0x` spelling and declared presentation width; zero and one retain
their natural forms. No reduction or identity coercion is implied.

| Validator | Ordered parameter content |
|---|---|
| `None` | Empty |
| `Natural` | One u64 natural |
| `Extent` | One natural at most 1,048,576 |
| `FieldLiteral` / `FieldLiterals` | One / variadic field literals with the signature's field |
| `MatrixShape` | Two naturals at most 65,536 |
| `MatrixIdentity` | One `asset` with format `zkc.matrix/0` and the owning matrix digest |
| `AssetIdentity` | One `asset` with the schema's exact `assetFormat` |
| `MatrixVector` | Three naturals at most 1,048,576; the third is 0 or 1 |
| `GatherIndices` | Variadic naturals at most 1,048,576 |
| `ScatterIndices` | One or more u64 naturals |
| `NumericalExpression` | One actual structured Ring expression, checked against every positional input and output |
| `NativeOrigin` | One structured native-origin record with the required message/query method |

An asset digest is the owner's existing 64 lowercase hexadecimal digits, not
new hash authority. Expressions and origins contain their owning structured
JSON value, not an encoded JSON string; their existing grammar, canonicality
and work limits apply. The program-byte encoder alone converts them to the
current `zkc.program/0` parameter spelling. A typed attribute is not evidence
that a mutable asset or setup has been authorized.

Generator and consumers enforce the same declaration limits: at most 16
constructor parameters, 1,024 operation scope terms, 1,024 ports per side,
1,024 facets and requirements per operation and 100,000 declaration records.
Serialized data is at most 64 MiB with JSON depth 64. Existing stricter
domain/expression/origin limits still apply. Generation must fail for an
unrepresentable contribution rather than emit a partial projection. These are
declaration-data bounds, not automatic increases to an interpreter or proof
search budget. The native requirement-certificate profile retains its separate
128-term bound and expanded-work checks; a larger declaration does not bypass
that profile.

## Consumer profile ownership

Declaration presence and consumer admission are separate decisions. An export
profile selects exact catalog identities and their applicable parameter and
structural forms; it cannot be a self-approval bit on an operation declaration.
Its owner fixes the selection before processing a candidate. Generated
membership data can replace a hand-maintained operation list, provided generation
checks declaration references and complete signature/type dependencies. Unknown
entries and unsupported parameter families refuse rather than acquire meaning
from a generic serialization callback.

`consumerProfiles` is a required list, including when empty. The former root
shape without that field is refused under the same development `/0` tag. A
profile has a unique nonempty `name`; `implementation` is exactly `unselected`.
`typeConstructors` lists unique declared constructor identities.
`parameterValidators` lists unique validator names from the invocation parameter
vocabulary, excluding `NumericalExpression`. `operations` is an ordered list of
ConsumerOperation records with unique `operation` identities within the profile.
All fields and nested record shapes are exact; unknown fields refuse.

Each ConsumerOperation references an installed operation and separately records
the consumer's expected `scope`, `stage`, `parameters`, `signature` and
`requirements`. These use exactly the corresponding operation record schemas.
Generation requires equality of each expected field with the actual declaration,
including root names/kinds, projection parents/members, ordered ports and
requirements, validator bounds, scoped literal field and asset format. The
expectation is authored by the consumer owner; regenerating it automatically
from a changed operation would defeat this correspondence check. Facets remain
operation-owned obligations and are not a generated interpretation table.

The current closed profile family supports fixed signatures only. Every
selected operation's parameter validator must occur in the profile's list.
Every constructor application in its scope and ordered ports must occur in
`typeConstructors`. This checks nested complete-Type dependencies through the
entire scoped term graph, including non-port terms. Domain and Nat roots and
associated projections are allowed. A scoped Type must be a known constructor
application: open Type roots or associated Type projections refuse. Supporting
those forms or variable signature families requires an explicitly specified
profile extension. General declaration formation remains independent of this
narrower consumer family.

The initial owner-fixed profile is `structured-source-primitives`. It requires
unselected implementations, lists constructors `index`, `bool`, `field`,
`vector`, `resource_unit`, and validators `None`, `Natural`. Its exact operation order is:

```text
index.constant, index.add, index.sub, index.mul, index.div, index.mod,
index.equal, index.less, vector.empty, vector.length, vector.sum,
vector.split, vector.append, vector.equal, field.equal, field.embed,
resource_unit.create, resource_unit.pass, resource_unit.consume
```

The eight index operations have no static roots. Every field/vector operation
has exactly one Domain root of sort Field. `field.embed` additionally projects
the associated `BaseField`; that projection is not another caller argument and
its declared `ExtensionField` requirement remains mandatory. `vector.equal`
retains its declared `CommRing` requirement. The three resource-unit operations
have one exact Domain root of sort Slot; Slot identities are nominal custody
identities, not installed algebraic domains. Their native export enrollment
does not establish an independent formal interpretation.
`index.constant` uses the exact
`Natural` validator with bounds `[1,1]`; the others use `None` with `[0,0]`.
There is no enrollment by operation prefix, authoring stage, contribution
installation, MLIR interface or inherited TableGen class.

Native consumers query `consumerProfile(name)` and
`consumerProfileOperation(profileName, operationName)` from
`zkc/Contracts/Declarations.h`; either returns null when unknown. The operation
query returns `ConsumerProfileOperation`, with its exact nominal `operation`
and ordered kinded `staticParameters`, derived from the checked formal roots.
`consumerProfiles()` enumerates the immutable profiles, including their
implementation policy, constructor and validator sets. Existing catalog
signature and parameter queries supply the declarations whose expectations
were checked. Rust exposes the corresponding `CATALOG.consumer_profiles`,
`consumer_profile` and `consumer_profile_operation` APIs. Consumers choose the
fixed profile name before inspecting candidate declarations. Contributions may
install declarations or separate profiles, but cannot add entries to that fixed
selection by declaring themselves supported.

Membership and root metadata are queries, not binding validators. Consumers
still check actual static argument kinds and nominal domains, reject a selected
implementation, resolve the exact logical signature and capabilities, validate
invocation parameters, and admit actual calls and CFG structure. The profile
does not expand the structured exporter's aggregate policy, install executable
behavior or extend an independent interpreter's primitive semantics. In
particular, exporter membership for `field.embed` does not assert interpreter
support for it.

MLIR interfaces expose structural behavior to compiler algorithms; they do not
replace this selected consumer profile. In particular, implementing a call or
export interface cannot register a formal interpretation. A formal consumer may
project the same identities into its installation table, but independently
supplies meanings, implementation laws and admission evidence. Extending profile
membership as data is sufficient only when those semantics already exist.
No broader formal support follows from serializing the complete catalog.

## Independent behavior

Generated signatures can detect mismatches between declaration and backend
registration. They do not make backend dispatch a generated mathematical
interpretation. Runtime tests exercise actual kernels, refusal precedence,
resource successors and custody. Native source/candidate comparisons retain
their own checks. A formal consumer selects and proves its own interpretation
after this data contract is available; an unimplemented interpretation stays
explicitly unsupported.

`IndexBlock` sampling produces one logical `indices` block, with count and bound
fixed by the composite `NativeIndexBlock` static invocation parameters, rather
than a scalar bound operand. Its `boundInput` is null. Source service fact
`IndexBlockRandomness` and explicit suite fact `IndexBlockTranscript` are
independent of scalar index facts. Search and gate-check operations declare
History only. No sampling facet asserts a compound-query security theorem.

`NativeIndexBlock` has exactly three parameters for
`transcript.native.indexed.indices`, and exactly four for its `.search` and
`.gated` declarations. The ordered carriers are structured origin (query method
`indices`), natural N, natural Q, and optionally natural b. Naturals use the
full u64 carrier: N is power-of-two in [1,2^63], Q in [1,2^20], b in [0,64].
The [native block format](native-index-block.md) owns the exact bytes.

## Frontend declaration associations

The exact version-0 envelope also contains `frontendDeclarations`,
`frontendRules`, `frontendNotations`, `frontendConstructors`, `frontendHomes`,
`serviceSignatures` and `serviceMethods`. These source-facing rows grant source resolution and typed
elaboration facts, never executable implementations, physical installation or
formal interpretations; backend choices stay in the
[native installation](native-installation.md). All objects reject unknown
fields. The rows describe the current installation, not permanent limits of
the language: later descriptor, role-family and staged-construction interfaces
extend their owning typed contracts.

### Installed source declarations

`frontendDeclarations` lists every installed source declaration in declaration
order. A row has exactly:

| Field | Meaning |
|---|---|
| `identity` | Unique installation identity, such as `record.unpack`, distinct from every frontend declaration and service method identity. |
| `owner` | The installed module path that declares it, a `zkc::` path. |
| `name` | Its identifier in that module. |
| `kind` | `Math`, `Local`, `Interface` or `Requirement`. |
| `statics` | Ordered static parameters, each `{name, parameter}` with a `{kind, sort}` of `Domain`, `Type` or `Nat`. |
| `inputs` | Ordered data inputs, each `{name, type}`. |
| `output` | The result type, or null for an interface or consumer requirement. |
| `association` | Exactly one `{kind, target}`: a `primitive` or a `rule`. |
| `prelude` | Boolean membership in the installed prelude scope. This does not grant fallback permission after a selected binding fails. |

A type is `{static}`, the index of a static parameter, optionally with an
associated `member` of that parameter's sort from `members`, or
`{constructor}`, a parameterless installed type constructor. A `primitive`
association names a mathematical intrinsic for a `Math` declaration and an
executable operation for a `Local` one; interfaces and consumer requirements have no primitive. A `rule`
association names a `frontendRules` row, and the declaration's kind, static
kinds, inputs and output must equal that row's shape. Identities, the owner
and name pair, static and input names within a row, and prelude names are
unique; an installed declaration shares no owner and name with an export.

A rule row has exactly `name`, `kind`, `statics` (parameter kinds), `inputs`
(types) and `output`. Rule shapes are data: a validator checks a rule
association against the declared shape, not against a fixed list of rules.
The frontend implements the semantics of the rules it names and refuses others.

`Requirement` rows have only static indices: `inputs` is empty and `output` is
null. They install consumer demands, with no executable body, descriptor value,
user implementation or general capability implication. The current
`NativeMessage` rule has exactly one `Type` static index. Its export is
`zkc::transport::NativeMessage`, identity `consumer.native-message`.
The source checker resolves it through the declaration index, including normal
imports and aliases. Its expansion and discharge are defined in the
[consumer requirement contract](../language/definitions.md#installed-consumer-requirements).
This extends the existing frontend kind vocabulary; all version-0 row fields
and exact unknown-field validation remain unchanged. The Python, TableGen and
Rust catalog readers validate and project the new kind independently. The
independent Lean Python installed-catalog reader accepts its exact static shape
without adding any formal interpretation or changing numerical profile rows.


The installed modules are the distinct owners. The frontend reads each module's
rows as its checker input: the module keeps an empty installation buffer at
`<installation>/catalog/<module>`, nothing is lexed or parsed, and a row the
frontend cannot express refuses with `source.installation`. Captured source
with the same spelling cannot install an association. Prelude membership is
explicit scope membership. Lexical and static binders and selected roots stay
terminal: a failed declared call never retries an intrinsic. The old `implicit`
field is refused, including when `prelude` is also present. Ordinary authored
source syntax is unchanged. The installation identity frames every field of
every declaration, notation and service method row, including `prelude`, method
identity and constructor ownership.

### Installed notations

`frontendNotations` owns installed notation only; authored source declares its
own notations. A row has exactly `owner`, `symbol`, `fixity`, `target` and
Boolean `public`. The target names a declaration of the same owner, so the
notation resolves through that checked declaration and its visibility; it
never installs an intrinsic by spelling. `fixity` is null, keeping the symbol's
fixed syntax, or `{associativity, precedence}` with `left`, `right` or `none`
and a precedence from 1 to 99. The frontend admits the symbol as an operator
and keeps ASCII operator syntax fixed. The owner, symbol and target triple is
unique.

The record rules derive payload types in declared field order from the actual
nominal schema, retaining phantom arguments. Inspect and repack require an
explicitly restricted ordinary or fixed-roster distributed record whose payload
fields are Copy and Drop. Distributed inspection returns the same wrapper
placement plus the exact placed payload tuple; repacking requires that payload
placement and preserves the nominal instance and ordered role application.
Unpack retires a restricted wrapper and transfers all required children. Each
operation checks constructor authority against its authored lexical caller.
Specialization preserves that caller, and independent witness checking
reconstructs the schema and authority. The intrinsic's module supplies no
constructor authority. Ordinary unrestricted unpack is pure; custody retirement,
inspection and repacking require ordered execution and an outer `<-` in layout
source. Custody-retiring restricted destructuring has the same ordered requirement.

`frontendConstructors` lists the structural type heads the source language owns
that are not catalog type constructors. A row has exactly `name` and `form`.
The name is the head's spelling, an identifier that is unique and names no
`types` row. The form is the structural meaning the frontend gives the head:
`OracleHandle`, one logical oracle handle over an oracle kind;
`OracleHandleSequence`, a bounded ordered sequence of such handles with a
static maximum; or `FiniteDescriptor`, a static traversal descriptor with one
ordinary Copy/Drop item parameter. Exactly one row has each form; the installed
rows spell them `oracle`, `oracle_sequence` and `finite`. The Finite form is
a descriptor category, not an ordinary `Type`, logical handle or runtime
representation. An installed source alias may export it as `Finite<I>`;
that alias's visible name grants no family authority. The rows own the spelling
and the frontend owns each form's meaning: it forms, prints, encodes in static
terms and looks up the home of these structural heads through their rows.
A spelling that no row names grants no frontend-constructor authority.
The interface schema kinds `oracle` and
`oracle_sequence` belong to the [Entry format](entry.md) and do not follow the
rows. The installation identity frames each row's name and form.

A frontend home contains exactly `constructor`, `module` and `members`. The constructor
names a `types` row or a `frontendConstructors` row; validators check that
membership as data, not against a fixed list of names. Lookup uses checked type category and
catalog identity, never a printed alias or type name. Nominal wrappers retain
their own home; aliases retain their target. A home association supplies no new
methods, capabilities, role inference or implementation.

A service signature contains exactly `name` and `capability`: the empty
capability or an installed unary Field predicate. A `serviceMethods` row contains
exactly `identity`, `constructor`, `name`, `signature` and `capability`:

- `identity` is explicit and nonempty, unique across frontend declarations and
  service methods. No identity is derived from a name or constructor.
- `constructor` references a `frontendDeclarations.identity` whose association
  is exactly `{kind: "rule", target: "RandomConstructor"}`. Its declaration must
  match that rule's declared shape. An arbitrary `Interface` or a source
  declaration named `Random` grants no service authority.
- `name` is an identifier unique within its constructor. Different constructors
  may declare the same method name.
- `signature` names a `serviceSignatures` row and `capability` equals that row's
  capability.

The installed rows are `service.random.draw`, `service.random.index` and
`service.random.indices`, all owned by `service.random`. Today
`RandomDraw` requires no capability, `RandomIndex` requires `IndexRandomness`
and `RandomIndices` requires `IndexBlockRandomness`. These rules retain the
existing ordered request signatures and independently selected provider roots.
Member spelling is separate from rule identity. No unknown rule falls back to a
textual signature.

A home also carries an exact `members` list of canonical source declaration
paths. It permits deliberate API forwarding, such as Vector's primitive
reexports. A forwarded member is eligible only when that home actually exports
the selected declaration and its first authored data parameter has the same
semantic constructor family. Unlisted imports and reexports add no methods.
