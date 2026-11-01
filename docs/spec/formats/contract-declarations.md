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
`mathematicalIntrinsics` and `consumerProfiles`. The format tag is
`zkc.contract-declarations/0`. Every list follows the contribution dependency
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
              mathematical, participants, constructible, message}
Capability = {name, parameters}
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
`vector`, and validators `None`, `Natural`. Its exact operation order is:

```text
index.constant, index.add, index.sub, index.mul, index.div, index.mod,
index.equal, index.less, vector.empty, vector.length, vector.sum,
vector.split, vector.append, vector.equal, field.equal, field.embed
```

The eight index operations have no static roots. Every field/vector operation
has exactly one Domain root of sort Field. `field.embed` additionally projects
the associated `BaseField`; that projection is not another caller argument and
its declared `ExtensionField` requirement remains mandatory. `vector.equal`
retains its declared `CommRing` requirement. `index.constant` uses the exact
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
