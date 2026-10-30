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

## Inventory

The root has exactly `format`, `sorts`, `types`, `operations`, `members`, `rules`,
`capabilities`, `exports`, `families`, `associatedTypes`, `mathematicalIdentities`
and `mathematicalIntrinsics`. The format tag is
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
| `PublicReplay`, `AcceptanceGuard`, `Conjunction`, `SourceHistory`, `ManagedHistory` | None |
| `Mathematical` | `identity`: a declared mathematical identity |
| `History` | `stateInput`, `stateOutput` |
| `Observation` | `stateInput`, `payloadInput`, `stateOutput` |
| `Sampling` | `provider` (`Entropy` or `Transcript`), `domain` (`Field`, `FieldVector` or `BoundedIndex`), `stateInput`, `valueOutput`, `stateOutput`, `boundInput` (port or null) |
| `Diagonal` | `factorsInput`, `valuesInput`, `resultOutput` |
| `Contraction` | `coefficientsInput`, `valuesInput` |
| `Coset` | `shiftInput`, `sizeInput`, Boolean `sizeIsLength` and `foldedOutput`, `vectorOutput` (port or null) |
| `DomainValue` | `rule`, `output`; `Constant` additionally has `parameter`, `Length` has `input`, and `Multiply`/`Divide` have `input` and `otherInput` |

`DomainValue.Constant` reads the declared static parameter, not an operand of
a nullary operation. Unused legacy default fields are absent. The other rules
derive values under their mathematical domain contract; they do not license
removing a reached check or assume nonzero divisors.

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
