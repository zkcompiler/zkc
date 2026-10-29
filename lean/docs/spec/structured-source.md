# Structured native import

The [native export contract](../../../docs/spec/formats/structured-source.md)
owns `zkc.structured-source/0`. This page specifies its independent Lean
admission and logical meaning; [formal support](../support.md) records the
theorems proved about particular imported subjects and how far each claim
reaches toward native compilation and execution.

## Checked subject

`Structured.Snapshot` retains source identity, selected entry, all domains,
relations, bindings, definitions and protocol contracts, exact function kinds, per-protocol rosters and port
scopes, visibility, origins, preconditions, sites and ordered operands/results.
There is one strict wire schema. The reader rejects unknown tags, extra
fields, objects and noncanonical numeric tokens, including in unused bodies.
Canonical decimals use the shared bounded ASCII-digit fold, which reduces in
the Lean kernel. JSON parsing and the match between an export digest and its
MLIR are executable steps outside kernel reduction.

Admission accepts at most 16 MiB of source text. Protocol template paths have
at most 2048 UTF-8 bytes; other strings have at most 512 UTF-8
bytes; binding and preparation names have the stricter limits stated with their
rows. A unit has at most 128 domains, 128 relations, 128 bindings and 128
definitions. A signature has at most 512 types, and source instructions and
references are limited to 4096. Ordinary lexical JSON nesting, region nesting
and helper dependency depth are each limited to 64. Stored internal marks add no source
instructions. Admission refuses operations outside the vocabulary specified on
this page, including conditional completion and construction-start, even in
dormant declarations.

Bindings are separate noncallable metadata in the exact eleven-slot envelope
`[format, original, digest, entry, domains, relations, bindings, definitions, contracts, catalogue, source-declarations]`.
Each row is `["binding", name, contract, arguments, implementation]`. All rows,
including unused rows, are checked. Names match ASCII
`[A-Za-z_][A-Za-z0-9_.-]*`, occupy at most 256 bytes and share the domain,
relation and definition namespace. Binding rows are retained in encounter
order. The implementation string must be empty. There is no missing
field default or compatibility reader. Binding names cannot be called or
selected as roots, domains or callbacks.

Relations are noncallable metadata. Their input types, Boolean result, purposes,
kind, key, revision, ordered typed static arguments and optional formula symbol
are retained. Relation wire rows have eleven required slots, with static
arguments immediately after revision. `RelationChecking` reuses `OriginTerm`
validation and checks aggregate limits, admitted catalogue domains (including
phantom domains) and signature/purpose consistency at equal closed identities.
A relation of kind `zkc.language.formula/0` must name a private Math helper of the unit with exactly
the relation's input and output types. Other relation kinds must omit this link.
Admission checks the link, not the formula's totality or mathematical adequacy.

`OpaqueRegistry` fixes one `OpaqueFamily` per vendor `(kind, key, revision)`;
its partial typed instantiation function determines the predicate, ordered
input/output types and purposes for the exact `OriginTerm` argument list.
Duplicate family ownership is refused. `resolve` checks canonical arguments,
exact signature/purposes and the absence of a formula link. Formula and captured
`zkc.` kinds cannot resolve as opaque. `RegisteredRelations` admits every opaque
row against a registry fixed before evidence, including unused declarations.
`ContractMeaning` and `DomainContract` consume this environment. Their predicates
are derived from lookup rather than supplied independently by evidence;
`Binding.unique_meaning` and `RegisteredRelations.meanings_exact` prove the exact
adapter law. Structural `check` alone does not supply registered meaning or a
security theorem. Formula helpers and captured assets retain their own meaning
owners. A caller must supply its actual family registry and any protocol theorem.

A statement retains its relation, exact entry operands, role selectors,
Boolean acceptance-result index and optional target name. A named target must
resolve to the containing protocol's retained target clause and agree with that
projection; the clause also fixes the decision participant. Without a name,
a standalone statement has no exact selected-Entry evidence. When targets are
present, its projection must still match a retained target. A statement evaluates
no relation and does not identify different participants' acceptance values.
`Function.origin` is an optional `FunctionOrigin`, with separate `local` and
`protocol` constructors. A Local function requires its existing ordered string
bindings, with nonempty bounded keys and values and unique keys. Math requires
no origin. Every protocol requires a `ProtocolOrigin`: a qualified template path
and declaration-ordered named `OriginTerm` arguments, including an empty list
for a nongeneric protocol. Missing origins and mismatches with the function kind
are refused. There is no reader for a legacy absent protocol origin.

`OriginTerm` retains naturals as canonical decimal strings, field and group
identities, domain and asset sort/identity pairs, Boolean/index/unit types,
tuples, arrays, four distinct nominal kinds, and closed builtin and formal
constructors. Runtime `Ty` and display strings do not replace these trees.
The decoder checks exact array arities and tags. Decoder and raw-record header
admission both check canonical decimals, string bounds, qualified path and
parameter syntax, exact key uniqueness, 128 named arguments, 512 children per
recursive list, 64 term levels and 4096 total terms across the arguments.
Before JSON parsing, arbitrary bracket nesting is capped at 134: six enclosing
arrays (snapshot, definitions, function, origin, arguments, binding) plus at most
two arrays per each of 64 term levels. After parsing, ordinary lexical array
depth is capped at 64. Only slot 8 of an exact ten-slot protocol-function row in
the definitions table of the exact current original-stage envelope is exempt;
that slot must pass the strict origin decoder. Standalone origins, wrong envelope
tags or arities, and other slots receive no exemption. Other schema fields remain
subject to snapshot decoding. Empty child lists count toward
bracket depth. Typed term depth, total-node and list limits remain independent.

The pinned Lean string libraries provide no NFC checker used by this reader.
Unicode NFC is the native frontend admission contract. Lean neither checks nor
normalizes it: keys and paths compare as exact UTF-8 strings, including for
hand-constructed records. Thus Lean shape admission alone is not evidence of
native NFC admission. Local binding values remain opaque metadata; Lean does
not reproduce the native static-identity registry.

Generated source aliases retain the Local/protocol distinction. Their names
hex-encode canonical tagged JSON arrays, preserving every constructor, nominal
kind and argument position without using `Repr` as identity. Protocol selectors
come from the actual admitted `UnitPayload.protocols` dependency order, and
generated associations select `imported.program.payload.protocols`; Local
selectors continue to use the checked helper table. The generated symbol and
raw-origin equations establish metadata association only. The source body's
bottom-up correspondence against checked callee associations remains a separate
proof obligation; no name, hash or matching origin discharges it.

The contract table contains exactly one row per protocol, including protocols
with no clauses. Missing, duplicate and non-protocol owners are refused.
`ContractAdmission` checks all clauses, including dormant components: clause
names, input/output direction, relation ABI, available role-local selectors,
residuals and Boolean decisions. Admission infers no property or theorem from
the presence of a clause. The [verification specification](verification.md#structured-contracts)
defines the independent semantic interpretation and proof obligations.

`check` resolves kinds, signatures, exact bound provenance, capture forwarding,
rosters and scopes, then forms `Source.Region` bodies through
`RawRegion.elaborate`. There is no additional source IR. One checked body is
stored per named helper; calls retain names and never expand syntax.

`formDefinitionDiagnostic` and `formProtocolDiagnostic` expose raw formation
failures as a declaration name and the exact `RegionFormationError`. The
`formDefinition` and `formProtocol` adapters retain the stable
`structured-formation` refusal code. Diagnostic display text is bounded; the
stored cause remains exact. These in-process APIs do not change the wire schema
or bypass lowering and profile admission.

`UnitPayload` separates kinded Math/Local `CheckedDefinition`s from
`CheckedProtocol` declarations. Helpers use `dialect`; protocols use
`protocolDialect` on the same carrier. A `ProtocolSignature` contains all six
fields: name, ordered roster, ordered input and output types, and resolved input
and output scopes. Scope order is retained. Protocols never inhabit a `Helper`
signature or helper table. The calculation boundary admits only Math references
and region-free calculations; Local invocation carries a checked Local
signature and owner. Selection chooses an admitted protocol without changing
its callable kind.

The dependency order computed by `orderDefinitions` is a candidate,
independently checked by `DeclarationsLinked`. Exact signatures include
Math/Local kind, ordered inputs and ordered outputs, including both finite
callbacks. Dormant callbacks and stopped suffixes count as dependencies. `ProtocolDeclarationsLinked` additionally
checks each protocol's exact helper inventory against the complete helper table
and its complete protocol signatures against the strict earlier protocol prefix.
All supplied declarations are checked, including dormant callers and cycles.
Identity summaries order their Math call subgraph for bound discharge;
availability reuses the final checked orders.

`Imported snapshot` carries successful admission of that exact constructor
subject. `Imported.exactSubject` and `check_ok_inversion` retain subject identity
and successful checking. Typed erasure/formation laws recover exact stored
bodies. Protocol admission also retains the exact
association between original protocol functions and checked declarations,
including resolved scopes and the lowered raw body, in both directions.
Signature equality alone does not identify an original body.

For authored typed views, `BodyIn.of_mem` packages membership of the actual
checked declaration, full helper-signature equality and raw-body equality.
`exact_body declaration` constructs these obligations with list constructors
and kernel-checked definitional equality. It uses neither a name nor a digest,
and it does not normalize admission of the whole unit. `BodyIn.perm` transports
association across a declaration permutation; valid linking of the reordered
calls is a separate obligation.

`checkFormedPayload`, provided by the `Structured.ModelAdmission` module, is an
opt-in bounded checker returning the same `UnitPayload` without native
application-expansion budgets. It retains stored-source limits, role and
service rules, linking, availability, effective-site identity and that traversal's
capacity limits. `check_payload_ok_iff` proves that standard admission succeeds
with exactly the same payload if and only if this checker succeeds and native
budgets pass. The standard `check`, which the CLI uses, applies the native
budgets. A small shared helper graph can pass model admission while exceeding
the expanded native work budget. Authored repeat maxima constrain execution
under both checkers.

## Bounds and availability

Bound facts identify exact index/container positions. Result binding shifts
both positions. `IdentitySummaries` follows returned-input aliases and select
arms with the same known identity; two unknown origins never prove equality.
Math preconditions must be discharged at each call. An indices domain supplies
the bound for its selected vector in the state, item, domain-argument and
capture interface. Mutable state
is not assumed invariant across iterations; equal lengths do not identify
vector contents. Local regions begin without Math bound premises.

`Availability` is a separate formed-tree analysis. Math summaries retain one
dependency footprint per result and individual requirements for every
intermediate computation. Named calls substitute both collections through their
actual arguments. A forwarded output can ignore an absent unused input;
constants have empty dependencies. An unused mixed-owner calculation still
fails admission. `select(c,x,x)` still requires `c`. Independent requirements
are checked individually, so calculations at distinct participants need not
share a single owner. Zero-result calls do not discard requirements.

The analysis allows 100000 stored traversal nodes, with separate budgets of
1000000 dependency units and 1000000 participant-replay units across the whole
unit. SSA footprints use indexed persistent arrays; helper argument tuples keep
their bounded list lookup costs. Summary substitution, requirement expansion
and footprint unions are charged incrementally before construction. Reusing a
checked Local summary charges no hypothetical dynamic call expansion. These
budgets are a representation-aware admission policy rather than allocation or
running-time bounds, and their costs need not equal those of the native
bit-vector analysis. Source-size limits alone do not bound transitive
requirement expansion.

Multi-role roots refuse Math folds and checked reads, including transitively
through named calls. Singleton roots admit the full finite profile, and owned
Local finite/control work is available in multi-role roots. This restriction
bounds the partial Math fragment.

Each protocol checks every requirement, owned operand, nonempty restriction
subset and declared output scope. A retained application must supply every
mapped declared input scope, including unused operands, and its result
footprints are precisely the mapped declared output scopes. Each callee body is
checked under its own declared inputs.

Service values originate only at singly owned formal protocol input ports.
Draw and protocol forwarding check their exact contract and mapped singleton
owner through the lexical SSA origin. Equal runtime handles do not identify
lexical ports. Services cannot be selected, restricted, exchanged, returned,
passed to helpers or used in statements. Same-owner aliases are legal;
executable alias validation precedes root masking. Service independence or
uniform sampling does not follow from handle identity.

`UnitPayload.available` records `checkUnitAvailability ... = .ok ()`, which is
computational admission evidence. Denotation alone never licenses admission.

## Domain catalogue

Every identity a unit names resolves against catalogue rows
(`Structured.Catalogue`): the field and group identities of types and
operations, binding roots, map fields and random-service contracts. Admission
never compares an identity with a fixed name. The last envelope slot is
`[nominal-rows, service-rows]`, the rows of the identities the unit uses, with
the spelling and meaning of the [native export contract](../../../docs/spec/formats/structured-source.md#envelope-and-types).
A nominal row is `["nominal", identity, sort, members, capabilities, modulus]`
and a service row is `["service", contract, sampled-field, methods]`.

`Catalogue.check` applies the rules of the native catalogue constructor to the
exported rows: identities are valid and unique; a modulus appears only on a
field row and is at least two, and the decoder reads it as a canonical decimal
string of at most 1024 digits; members
are unique, each declared for the row's sort and naming a row of the member's
sort; capability facts are unique and declared for the row's sort; a
`PairingField` row names distinct source groups, and a target group when
present, that act by scalars of that field; a service samples a field row,
offers `draw`, and offers `index` exactly when that field has
`IndexRandomness`. The modulus of a field row is its characteristic, for a
prime field and for an extension alike. No rule assumes a characteristic: a
characteristic-two prime field and an extension field without `PrimeField` are
well-formed rows.

`Catalogue.agrees` requires every exported row to equal the installed row for
its identity. `admittedCatalogue` combines `blsCatalogue` and
`koalaBearCatalogue`: BLS12-381 scalar/group/service rows, KoalaBear, and its
`koala-bear.ext8-binomial3` extension and random service. The installed instances
include BLS scalar/vector/G1 and KoalaBear base/extension scalar/vector types.
Every stored type, including dormant signatures and region results, must name
an exported row of its sort and an installed instance. Installing a row does
not prove its arithmetic, sampler or native implementation correct.

Operations require facts of their rows. Field arithmetic, constants and
equality require `Field`, and a constant is below the field's modulus. Group
identity, addition and equality require `ScalarAction`, and scaling also
requires the group's `Scalar` member to be the named field. A bounded read
names a field row. A binding root is a field row with its family's capability.
A draw requires a service row that samples the field and offers `draw`, and its
participant query names that service `random.` followed by the field identity
and `/0`. A map lifts the field of its vector result, which requires `Field`.
Admission refuses with the failed condition: `structured-catalogue-identity`,
`-modulus`, `-duplicate`, `-member`, `-capability`, `-pairing`, `-service`,
`-unknown` and `-mismatch` for rows; `structured-domain-unknown`, `-sort`,
`-capability` and `-member` for resolution; `structured-type-unadmitted` for a
sort instance outside the environment; `structured-field-canonical` for a
constant at or above the modulus; and `structured-service-contract` for
services.

`Catalogue.Justified` states the data facts that meanings rely on: the modulus
of a field row is prime, and the modulus of a `CharacteristicNotTwo` row is not
two. `blsCatalogue_justified` proves it for the BLS subcatalogue, with the
BLS12-381 scalar modulus prime by a Lucas certificate whose modular powers the
kernel evaluates (`blsModulus_prime`).

## Shared mathematical and component meaning

`assignment F G` maps Boolean/index/field/vector/group/service sorts to
`Bool`, `Nat`, `F`, `List F`, `G`, and `Nat`. Admission resolves the nominal
identities of these sorts against the [domain catalogue](#domain-catalogue).
Sequences interpret as ordered lists of their element interpretation. Nominal
products interpret as heterogeneous products of their ordered component types.
`ProductFields.pack` and `unpack` are inverse; construction and projection are
total and use that same representation in the uniform and per-domain models.
`Collection` selects a field vector or sequence for a finite domain. Elements
and indices preserve exact container identity, order and the u64 length check.
`DomainBody` retains a typed SSA sequence of constructors and the returned
reference. Data argument variables and previously admitted domain variables use
separate contexts. Zip and product concatenate heterogeneous item tuples without
creating a nominal product identity. Range and every unused constructor retain
their checks. `DomainSpec.bounds` derives item/container provenance from that
syntax; the wire cannot assert it. Only field-vector bounded reads are currently
admitted.

Folds and collections share this domain admission. Collection bodies and optional
predicates receive the complete item/domain/capture tuple. Collection uses a
private reversed accumulator and restores source order once. Generic process
interpretation and helper-table framing preserve callback effects and stopped
prefixes. These laws do not establish native capacity or provider correspondence.
The bounded executable tool checks domain traversal and collection size before
concrete evaluation. Uncertain product radices and uncertain sequence result
shapes may be refused by tool policy without restricting the logical semantics.
The evaluator uses explicit `CommRing F`, `AddCommGroup G`,
`Module F G` and decidable equality laws. Group scaling is scalar action with
group operand first in the source. No arbitrary group is silently equated to
its scalar field.

`Evaluation` implements scalar, group, Boolean and finite/control operations
once. The generic `HelperTable Value interface` checks exact signatures;
closures capture their already interpreted prefix. `ComponentTables` builds
closed and optional closures from the same body. Math calls pass optional tuples
directly to their named optional closure. Other operations delegate to the
shared evaluator after operand sequencing. Nested callbacks retain their
nonoptional meaning through `Region.component`.

All-present adequacy preserves the complete process, including stops, nested
callbacks and zero/multiple results. Generic frame laws require both closed and
component agreement because callbacks use closed meanings. Prefix linking and
full-table equations exclude missing/mismatched lookup fallback for checked
references; they do not exclude legitimate reads or stops in a callee.

Folds use `Finite.execute`: domain admission precedes iteration, predicate
precedes step, false preserves state, and stopping bypasses the suffix. Checked
reads refuse invalid indices. Counted loops retain state/capture packing and
conditional completion. The logical semantics has no depth fuel. Finite theorem
families use the same explicit `F,G` assignment and evaluator.
`SiteObservations` abstracts only internal marks; arithmetic is pure and shared.
There is no separate scalar arithmetic or unsupported-sort fallback.
Selection is interpreted for every admitted type, including products and sequences.
The Common scalar effect adapter refuses aggregate messages. The nominal
construction runtime transports data as one exact `Ty` paired with its existing
`Carriers.Value` and a proof that it contains no service capability. Products and
sequences, including differently typed empty containers, retain their complete
nominal sort; decoding requires exact sort equality. This runtime support does
not bypass the separate construction rule, projection or generated ABI admission
gates. The logical public-value binding representation retains products and
sequences injectively; neither representation establishes a canonical byte
encoding.

### Domain carriers and models

Exported sorts name domain identities by their native catalogue strings. The
semantics interprets identities in two layers. `Carriers` assigns a type to
every field identity and every group identity and nothing else, so
`Carriers.Value` interprets every sort without instance arguments. A
`FieldModel` adds a commutative ring and decidable equality per field identity,
an optional computable inverse and embeddings between field identities; a
`DomainModel` adds an additive group and decidable equality per group identity
and the scalar actions between field and group identities. No layer assumes a
characteristic, a prime field or a particular identity. Which identities exist,
which pairs are related and which laws a theorem may assume are facts of the
catalogue rows that admission checks.

The evaluator over models (`Primitive.evaluateOn`, `Evaluation.operationOn`,
`Evaluation.meaningOn`) gives each field operation the ring of its own field
identity, each group operation the group of its own group identity and scaling
the model's action of the named field on the named group. The nominal operation
`Op.fieldEmbed extension base` takes `[.field base]` to `[.field extension]`
and applies `model.embed extension base`. Its direct descriptor is
`["field.embed", extension, base]`. Admission calls `Catalogue.requireEmbedding`:
the extension must have `ExtensionField` and `Field`, the base must have `Field`,
the extension's `BaseField` member must name that exact base, and both rows must
carry the same present modulus. Algebraic embedding laws remain separate from
these checks. The operation is total in the operational model; normal forms
retain its application even to a literal, without assuming a law about `embed`.
The uniform model interprets the operation by the identity of `F`, as specified
by its own embedding function. Helper tables,
component tables (`ComponentTablesOn`), the participant interface and site
observations (`participantInterfaceOn`, `ObservedActionOn`), protocol
operations, retained repeats, protocol tables and participant views
(`protocolOperationWithOn`, `Program.participantOn`), and relation and contract
interpretations (`RelationInterpretationOn`, `ContractInterpretationOn`) are
defined over carriers or models in the same way. Definitions that only name
values take carriers; definitions that compute take a model.

The uniform interpretation is the instance of this semantics: `uniformCarriers F
G` reads every field identity as `F` and every group identity as `G`, and
`ringModel F G` adds the instance structures, the module action of `F` on `G`
for every pair and no inverse. `assignment F G` and `(uniformCarriers F G).Value`
share one case analysis and are equal by reducible unfolding. The uniform
definitions keep their own text, so existing statements and the proofs that
unfold them are unchanged, and equations relate each to the generic definition at
the uniform model: `Primitive.evaluate_eq_evaluateOn`,
`Evaluation.operation_eq_operationOn`,
`Evaluation.componentOperation_eq_componentOperationOn`,
`protocolOperationWith_eq_protocolOperationWithOn` for every effect interface,
`UnitPayload.plainProtocolTable_eq_plainProtocolTableOn`,
`Program.participant_eq_participantOn`, and the `toOn` readings of relation
environments and interpretations with the same truth of every application. The
uniform site-observation interface is its own inductive type; `observedToOn`
translates it, and the observed views agree after that translation.

`Evaluation.denote_inverse_free` transfers denotations between models that
differ only in the inverse, for bodies that never invert; every body of the
current vocabulary is such a body. A model built from a commutative ring has no
inverse, and a model built from a field supplies one, so theorems proved for a
lawful model apply at the ring model for these bodies. The congruence behind it
is `Region.denote_congr`. The executable tools evaluate at `scalarModel`, the
uniform model over the BLS12-381 scalar field with its computable inverse.

`Evaluation.inline_invoke` replaces a helper invocation by
`Region.bind (body.rename arguments.get) next` under an explicit equation
between lookup and body denotation for every actual argument tuple. It applies
to the shared scalar/group evaluator, any effect interface and site observations.
Binding retains ordered helper results above the caller environment. Equality
concerns the complete `PIR.Process`: a stopping body bypasses the suffix, and a
returning body runs that same suffix, including its stops. Empty result lists
are supported. The premise is a process equation, not a totality assumption.
The closed `Structured.inline_invoke` wrapper and `Payload.inline_body_view`
reuse this law, exact declaration membership, linking and table-frame laws.

`Descriptor.multilinearRestrictPrefix` reads the exact two-slot wire descriptor
`["multilinear.restrict_prefix", field-domain]`. Admission requires the
catalogue's field identity, two vectors in that field and one vector result,
with no site or regions, in Math or a protocol calculation. Local use refuses.
The admitted `Op.multilinearRestrictPrefix` returns
`Polynomial.Multilinear.restrictPrefixValues values point` in both uniform
and per-domain interpretations, without a shape, index-bound or native
resource premise. It is a total calculation in preparation, optional-component
and normal-form semantics. Relations separately require the table shape and
prefix-length bounds. These equations establish source-model meaning;
they do not establish compiler or native-provider correspondence.

## Checked primitives and index values

`Primitive` owns a closed vocabulary and ordered ports; `PrimitiveEvaluation`
owns its meaning over `PIR.Outcome`. One `Op.exec` case delegates
through the shared `Evaluation` used by closed bodies, components and participant
helpers. There is no separate carrier, process executor or whole-protocol intrinsic.
Its helper inventory is empty; general framing, effect interpretation, linking,
all-present adequacy, inlining and closed projection apply to it unchanged.

An exec descriptor is `["exec", "exec.apply", binding-name, parameters]`.
Admission requires that exact native operation and resolves the primitive from
the referenced binding's contract, nominal arguments, full ordered data ports
and parameters. Native scope/outcome plumbing belongs to the checked export
boundary; the formal ports are data operands and successful payload results. Exec is Local-only,
region-free and requires a nonempty unique source site. Index constant takes
one canonical u64 decimal string; every other primitive takes no parameters.
No leading zero except `"0"`, sign, whitespace, non-ASCII digit, field reduction
or wrapping is accepted. Values through `18446744073709551615` are admitted.

Here `I` is index, `B` Boolean, `F` the binding's root field identity, and `V`
its ordered vector. All rows use the same native `exec.apply` operation;
retired per-primitive names are refused. Index contracts have no domain
arguments; vector and field contracts have exactly one argument, a field row
of the [domain catalogue](#domain-catalogue) with `Field`, or with `CommRing`
for `vector.equal`.

| Binding contract | Inputs | Outputs |
|---|---|---|
| `index.constant` | none | I |
| `index.equal` | I, I | B |
| `index.less` | I, I | B |
| `index.add` | I, I | I |
| `index.mul` | I, I | I |
| `index.sub` | I, I | I |
| `index.div` | I, I | I |
| `index.mod` | I, I | I |
| `vector.empty` | none | V |
| `vector.length` | V | I |
| `vector.sum` | V | F |
| `vector.split` | V | V, V |
| `vector.append` | V, F | V |
| `vector.equal` | V, V | B |
| `field.equal` | F, F | B |
| `field.embed` | field:base | field:extension |

For `field.embed`, the sole binding argument is the extension identity. Its
`BaseField` member selects the base, and `Catalogue.requireEmbedding` validates
the pair, including for unused bindings. The Local `exec` descriptor lowers to
`Op.fieldEmbed`, preserving the source observation site through the usual
lowering. No additional primitive interpreter or wire record is introduced.
`Construction.Calculation.fieldEmbed` maps to this same operation; constructed
participant rendering recognizes `exec.apply` with the `field.embed` contract
and ordered base/extension ports. Its implementation field must be the empty
string: an explicit implementation or a malformed field refuses the export,
rather than being erased into the mathematical embedding.
Constructed attribute decoding validates every tagged payload before rendering;
bound operations require a symbol binding, a string-array parameter list and a
string site, including when a diagnostic site is omitted from the meaning.

Index values are `Nat` with explicit `value < 2^64` conditions. Exec checks
both index operands, including comparisons. Add/multiply overflow, subtraction
underflow, and division/remainder by zero stop `refused`. No result is reduced
modulo the scalar characteristic. Pure `index.constant` and `index.equal`
represent native `data.index` and `data.index_equal`, require Math/Protocol
ownership and empty sites, and preserve optional component dependencies. Their
constants are range-checked on admission. They cannot authorize Local exec.
At the logical carrier level pure equality is total on `Nat`; relating arbitrary
inputs to native u64 values additionally requires their representation bounds.
Exec equality checks those bounds itself and can refuse.

Vectors denote logical lists. Empty returns `[]`; sum folds field addition from
zero; append returns the entire original list followed by one scalar; equality
returns false for unequal lengths. Split requires positive even length and
returns the contiguous low half followed by the high half, with neither padding
nor truncation. It does not require a power-of-two length. All result positions
and source marks remain ordered. The component exec case sequences every
operand and stops `incomplete` on absence; reached exec cannot be skipped because
its results are unused. An exec stop bypasses every later continuation.

`vector.length` stops `exhausted` if logical length is not representable in u64.
The same explicit representation check in `DomainSpec.denote` also stops
`exhausted`; its successful finite laws keep their range premises. This is a
logical representation boundary, independent of host allocation and of native
or observer work capacity. Callers needing subsequent lengths or index
arithmetic must state those bounds.

## Retained realization and map declarations

The eleven-slot envelope retains two additional definition variants, in original
encounter order:

```text
["realize", name, inputs, outputs, helper]
["map", name, inputs, outputs, helper, rowwise]
```

`RealizationDeclaration` and `MapDeclaration` retain exactly these fields.
Preparation names obey ASCII `[A-Za-z_][A-Za-z0-9_.-]*` with a 128-byte limit;
Math helper references use the general nonempty 512-byte string bound.
`rowwise` contains JSON Booleans, has the input arity and contains at least one
true. A number or string is not a wire Boolean. Both variants count toward the
shared 128-definition limit and each charges one derived operation against the
4096-instruction limit. Unused declarations, metadata, operations and transitive
calls remain subject to admission, closure depth and cycle checks.

Reference permission depends on the original retained variant, before deriving
a semantic Local helper. A Math `call` targets a private defined Math function.
Local `apply` may target an ordinary Local function, fold or collection declaration,
realization or map. Protocol `local_call` targets an ordinary Local function
only. Finite callbacks remain private ordinary functions of the required kind;
derived preparation helpers do not gain callback permission. A preparation's
helper must be an exact private Math reference. Selected entries remain
protocol functions.

Realization requires the declaration's complete input and output ABIs to match
those of its helper, including vector projections and zero or multiple results.
Its general Math computation fragment admits field/group operations, pure
index and Boolean operations, selection, product construction/projection,
Math calls, finite folds, checked reads and positional returns. Local control,
exec and services remain excluded. The root has no external premise; ordinary
formation discharges bounds on internal calls and finite callbacks. Both the
step and predicate remain in the selected closure, even when never reached.

Formation validates the shared typed operations. One `selectMathHelpers`
procedure selects closures using explicit type/body predicates over the actual
checked dependency table. `computationHelpers` is the general realization
admission set. `preparationHelpers` retains the narrower region-free fragment
used by immediate-return proofs and the scalar-map fragment. `mapHelpers`
additionally binds every selected helper port and intermediate result to the
declaration's exact field, including discarded values and dead calls; its
subset theorem supplies the generic immediate-return certificate. Finite folds and
checked reads are excluded from immediate-return evidence.

Ordinary declaration ordering and protocol availability enforce cycles and
depth before profile selection. A separate retained-declaration traversal checks
empty preconditions throughout scalar-map closures; realization checks only its
root's premises. `PreparationRootsSelected` and its `Imported` inversion lemmas
identify the exact admitted Math roots. General realization admission cannot
supply an unconditional return law: reached finite domains can exhaust.
`imported_immediate_realization_returns` instead requires explicit membership
of the exact root in the narrower checked closure, alongside retained declaration,
checked-body membership and raw derivation. It does not assume semantic callee
totality. Finite formula laws use their own explicit input-domain premises.

Map's root helper has only Fr scalar inputs and exactly one Fr scalar output.
An input becomes an Fr vector exactly when its mask entry is true, and the map
has one Fr vector result. Every transitive operation, including dead instructions
and zero-result calls, must be an Fr constant, add, subtract, multiply, exact
Math call or return. Nested Math helpers may return zero or multiple Fr scalars;
the one-result condition applies only to the map root. Equality, selection,
index/group operations and other fields are excluded even when unused.

Both preparations use the typed `Source.Region`, `PIR.Process` and the Math
helper table. A realization derives one `Op.invoke` with positional operands,
followed by positional returns. A map derives one typed `Op.map` and return of
its sole result. `MapSpec` retains the helper name, field and ordered mask; its
computed helper signature enforces the scalar root ABI. Checked formation and
raw derivation equations connect each successful `checkDefinition` call to its
retained declaration. These per-definition equations do not associate a whole
payload with its declarations; a full-unit client proves exact raw-body
equalities for its own checked payload. The
original declaration acquires no invented body, site, origin or visibility
field.

For complete ordered map arguments, the first row length is checked for
representability below `2^64`. Each later row is then checked for representability
and equality with the first length, in source argument order. An
unrepresentable reached length stops `exhausted`; a representable unequal length
stops `refused` before later shape checks. Only after all rows pass does the map
invoke its checked helper at indices `0, …, n-1`, supplying every scalar operand
in its original position, whether selected from a row or broadcast. Unused rows
still participate in shape validation. Equal empty rows return an empty vector
without invoking the helper. Process bind preserves every reached helper effect
and stop prefix; no zip truncation or liveness-based operand removal is implied.

At the model level, direct optional `Op.map` sequences all operands and stops
`incomplete` if any is absent. Admitted source maps occur in derived Local bodies,
so their source-visible absence boundary is the owned Local call; direct optional
map laws also cover raw typed regions used by generic semantics and tests.
Local helper component invocation keeps its own strict wrapper
behavior, and owned protocol invocation requires all inputs before
work; nonowners skip it. Math projection remains optional per result and may
ignore absent unused inputs. These are separate boundaries.

Generic map formula laws require an equation for actual
`invoke table spec.helper` on every reached complete scalar tuple. Concrete
clients discharge that premise using their complete checked helper tables and
exact body views. Helper spelling never supplies a mathematical equation.
Helper inventory, framing, full-table linking, effect interpretation and
all-present component laws use the same node and carrier.

Logical lists and u64 representability are separate from observer vector/work
capacity. Collecting pure row lengths performs no representability
prescan: the stopping decision follows the ordered shape prefix above.

## Retained protocol applications

The exact five-field instruction row is
`[["protocol_apply", callee, roles], operands, resultTypes, [], site]`.
The descriptor has exactly three fields and occupies an ordinary instruction
row of the eleven-slot snapshot envelope. Admission requires a flat nonempty target, exact ordered full ABI,
zero regions, a nonempty site, and one caller role for every ordered callee role.
The substitution is injective and in range. Protocol declaration names, role names and real sites
use ASCII `[A-Za-z_][A-Za-z0-9_]*` with the separate 512-byte source limit;
arbitrary flat symbols and the empty synthetic mark have their own rules.

The retained original reference edge must target a public protocol function.
All protocol headers require the computed public wire visibility. Native
formation rejects explicit source visibility attributes, including explicit
public; that distinction is absent from the wire and is not reconstructed by
Lean. Applied bodies must be statement-free. The selected root may be called
by another acyclic declaration when it meets those requirements. Signature-only
lookup cannot authorize a helper, binding or retained preparation declaration
as a protocol target.

`ProtocolTable` stores closures indexed by the complete six-field signature.
Each closure captures only its earlier protocol prefix and the complete
Math/Local component tables. A finite fold constructs this table; invocation
does not expand source or recursively resolve a new body. Missing entries and
same-name signature mismatches refuse. Exact linkage justifies using a full-table
body equation for a closure defined with its captured prefix.

`Imported.protocolSource` and `Imported.protocolChecked` expose the exact
original/check association in both directions; `Imported.protocolPermutation`
preserves complete checked values and multiplicities. Given actual membership
in a checked protocol's raw operations, `Imported.protocolApplication_source`
provides an inherited lexical environment in which each service operand names
a bounded original input with the exact nominal contract and mapped singleton
owner. This existential consequence does not identify the environment at a
particular lowering path or distinguish two same-contract, same-owner inputs.
Concrete origin-transfer equations and participant process equations establish
that more specific routing. The same theorem identifies the actual instruction
in the original body's recursive `storedInstructions` inventory, and its role
and callee corollaries derive finite role validity and the original
statement-free callee check.
`Imported.protocolApplication_callee_statementFree` proves that the resolved
callee's entire stored body, including nested callbacks, contains no statement.
These are consequences of admission alone, independent of runtime handle
equality and of availability soundness.
`Imported.protocolApplication` retains the flat-source instruction/SSA-offset
consequence under an explicit callback-free premise. Recursive admission supports
reordered service captures without asserting one global offset.

`ProtocolContext` stores an optional application prefix and a map from current
local role indices to selected-root indices. Root self is immutable. Entry
composes the current role map with the call substitution; all owners, peers,
restrictions and port scopes use that composed map. Validity requires boundedness
and injectivity only on the current finite roster, not on arbitrary natural
indices used by the total function's default.

For nonempty sites, qualification is identity at the root, and beneath prefix
`a` it is `p(a,s) = "apply_" ++ decimal(a.utf8ByteSize) ++ "_" ++ a ++ "_" ++ s`.
The empty synthetic site always remains empty. Nested A/B/C therefore renders
`p(p(A,B),C)`, not `p(A,p(B,C))`. Helper tables keep their raw internal marks;
only protocol sites are qualified. Actual service handles pass unchanged.

An application outside the mapped callee roster returns absence at every result
position without invoking the child. This includes the empty result tuple.
Inside the roster, the closure masks actual optional inputs, denotes its one
stored `Region`, then masks returned outputs. Entry never sequences all optional
inputs. Math retains per-result optional behavior; an owned Local call still
requires all inputs, including unused ones. Missing Local inputs stop at the
qualified caller mark, while a reached helper's own stop retains its raw mark.
A zero-result child may perform actions or stop; output arity never erases work.
`ProtocolOp.regions` supplies typed optional callback meanings to the one
operation interpreter. Repeat contributes one such callback; applications use
the captured protocol table.

Static admission has three independent resource checks. Stored-source limits
and combined helper/protocol dependency depth use leaf depth zero and at most
64 edges. Native conservative summaries use original instructions and terminators,
not synthesized marks: at most 64 nodes of expansion depth, 100000 work,
1000000 operands/results/role selectors, 16 MiB conservative site bytes and a
4096-byte longest-site bound. Protocol roots are traversed in original snapshot order and share the module totals; ordinary
Math calls and protocol calls retain distinct accounting. These whole-unit
checks apply the native all-root constraints to every unit, including units
without applications, and cover dormant protocols and reachable pure helper
calls.

Effective-site traversal separately visits every original protocol in snapshot order as a root,
with a fresh collision set but shared cumulative counters. It follows every
call occurrence, including dormant suffixes. Application headers are rendered,
charged and checked but are not inserted as effective leaves. Guard, exchange,
query and Local-call sites share the resulting namespace; helper internals do
not enter it. Limits are 100000 visits, stack depth 64 including the root,
4096 UTF-8 bytes per generated label and 16 MiB cumulative rendered labels.
These checks are independent of self, input values, replies and observer capacity.
The collision collection is `ApplicationMetadata.SiteSet`, a standard balanced
set with an exposed ordinary less/equal string comparator. Empty and insertion
laws preserve exact duplicate membership; module-level kernel controls ensure
concrete admissions can reduce without importing private library bodies.
Visit limits are logical counts, not processor-time bounds.

The outside-roster equation specifies the retained logical process. Absent
inputs alone do not imply absent intermediates, because constants can produce
values.

## Retained protocol repeats

The descriptor is exactly
`["protocol_repeat", carried, maximum, roles, carried_roles]` in the
five-field instruction row of the eleven-slot snapshot envelope. `carried` is a natural
at most 512; `maximum` is a natural at most 1048576. The first operand is the
count. The next `carried` operands are state, and the remaining operands are
immutable captures. Ordered result types equal the state types. There is exactly
one isolated callback with inputs `index :: (state ++ captures)`, results
`state`, and a `yield` terminator. Entry protocols end with `return`.
The callback induction input replaces the outer count; using the original count
inside the body requires a separate explicit capture. No outer SSA reference
is implicitly available in the isolated callback.

`RepeatSpec` retains state and capture types, the resolved ordered roster,
ordered state scopes and maximum. `ProtocolOp.repeat` stores this specification
and its header site. The callback is an ordinary typed `Region`, interpreted
through the same optional region meaning, root participant coordinate and
captured helper/protocol tables. There is no expanded repeat source or second
concrete evaluator.

Admission checks the entire callback even when maximum is zero or the
declaration is dormant. The roster must be a nonempty duplicate-free subset of
the enclosing active roles. The count must be available at every participating
role. Each state scope must be nonempty, contained in the roster, and available
both initially and at yield. Capture footprints are intersected with the roster
and must remain nonempty. Service types may be immutable captures but cannot
be carried state or yielded results. A copyable capture can replace a state
component when its type and footprint satisfy that component's contract.

Callback input origins distinguish lexical authority from data facts. Induction,
state and nonservice captures have no protocol-entry input origin. Only a
service capture preserves its original lexical input identity, contract and
owner through nested capture/application layers. Immutable data facts are
checked separately; neither an induction value nor mutable state inherits an
unjustified equality to the original count or initial value. A nested statement
always refuses with `structured-statement-placement`, including an operand-free
statement or a body with maximum zero. Clearing data origins alone is not this
placement check. Statements inside an applied declaration follow the separate
`structured-applied-statement` rule.

Protocol roots begin with no bound facts and introduce no protocol
preconditions. The generic capture-fact transfer rebases only facts about
explicitly captured immutable values; it grants no additional admitted source
capability or state/induction invariant.

The repeat-specific static diagnostics distinguish `structured-repeat-role`
(an operation escapes the active roster), `structured-repeat-count-scope`,
`structured-repeat-state-scope`, `structured-repeat-capture-scope`,
`structured-repeat-yield-scope`, and `structured-repeat-depth`. ABI, callback
shape and exit failures reuse `structured-protocol-signature`,
`structured-protocol-region` and `structured-protocol-terminator`. Each reader
reports its own first failing boundary; native generated-parent diagnostics need
not equal a Lean raw-wire diagnostic.

Write `M` for `maskValues self (context.mapScopes spec.stateScopes)` and
`active` for membership of `self` in the context-mapped repeat roster. The
logical operation `denoteRepeat` obeys these cases:

- Outside the roster, return an entirely absent state tuple immediately.
- Inside with an absent count, stop `incomplete`.
- Inside with a present natural count above maximum, stop `refused` before
  constructing the range or demanding any capture.
- Inside with count zero, return `M(initial)` without invoking the callback.
- Inside with admitted count `n`, execute the finite range `0..n-1` with
  `Finite.execute` from `M(initial)`. Each callback receives `some index :: (M(state) ++ captures)`;
  mask every successful yielded state before the next iteration and return.

The count refusal applies to every logical natural, including values at least
`2^64`; the u64 limit belongs to native wire admission. There is no semantic
fuel, overflow alternative or count truncation. Mixed-role state keeps each
component optional; sequencing the whole tuple would incorrectly demand values
owned by other participants. Missing captures are demanded only by reached
strict operations. The same optional captures and actual service handles are
passed to every reached iteration.

Iteration preserves ordered effects. A stop retains earlier effects and the
handler state reached at that stop; later iterations and the outer suffix do
not execute. Zero results do not erase callback effects or stopping. Shifted
residual iteration uses `List.range' start count` after the original count has
been admitted, with no reset of the induction index or renewed count check.
Interpretation and framing use the finite execution and `PIR.Process`
laws. Erasing internal marks preserves the process equation while action labels
remain externally visible.

The lowered repeat header mark remains observable outside the roster and at
zero count. Repeat adds no site prefix or per-iteration namespace. Nested
applications qualify sites with the same top-down renderer as ordinary calls.
Static availability, dependency inventories, native summaries and effective-site
checks descend into the stored callback without unrolling it. Summary selector
cost counts the repeat roster, not its state-scope selectors. Effective-site
traversal inserts the surviving repeat header and descends at the unchanged
prefix, including maximum-zero bodies. Expanded repeat nesting is checked
across application edges. Stored JSON depth, expansion depth and executable
preparation capacity are distinct limits; no fixed repeat-count threshold is
implied by the JSON depth limit.

Complete original units retain all declarations and their original order.
Whole raw-tree equality and checked-body erasure identify every
nested callback; signature equality alone is insufficient.

## Participant meaning and observations

`Program.participant` interprets the selected root for a chosen roster index.
Input scopes mask supplied values before evaluation; output scopes filter
returned values after all work. Shared scopes do not equate participant copies.
`Participant.exchange` sends and retains the sender's value, receives an
independent typed reply at the receiver, and produces absence elsewhere.
`Participant.query` uses the actual service handle operand. `Participant.guard`
checks its optional condition only at its owner.

`Participant.owned` sequences every input at the owner, invokes the **closed**
Local closure and preserves stopping even for zero results. Missing owned inputs
stop `incomplete`. Nonowners skip the call. Optional Local helper closures are
not used for protocol dispatch.

`Op.mark` and `ProtocolOp.mark` retain internal site observations before protocol/Local
instructions and explicit Local stops. Math bodies do not insert marks; their
source operations have no nonempty stop sites in the admitted profile. `Program.observed` exposes these to the
scripted observer. `forgetSites` erases only those observations to obtain the
ordinary participant process; `PIR.Stop` itself does not carry a site. Provider
requests, replies and stops remain ordered. Internal marks consume no scripted
reply and are absent from the external request/reply trace.

`ClosedProgram` is an explicit checked closed projection of an admitted root.
It carries `subject.closedPayload = .ok payload`, retains the same subject, and
keeps its projected root separate from helper closures. Arbitrary `Program`s
have no closed `denote`. Finite clients use `checkClosed` and the
closed profile's process laws, with the same `F,G` interpretation.
`ClosedProgram.participant_eq_denote` proves the relation after site erasure,
with exact port transports and complete singleton scopes certified by the
closed-profile check itself. A reachable retained application refuses the
closed view with `structured-open-profile`. A reachable repeat has a nonempty
callback tuple and refuses earlier with `structured-protocol-region`, including
maximum zero. A selected body free of applications and repeats retains its
closed projection even if other dormant protocol declarations contain them;
the projected body is independent of the unused table.
`Program.participant_direct` derives the plain interpreter from the observed
one through generic operation, Region and table-fold interpretation laws.

`CommonAdapter` embeds the Common effect fragment and proves that
projection after embedding preserves the entire process. Projection of extra
index/vector/product/sequence messages refuses explicitly. Concrete contract use must establish
that its actual process lies in the supported fragment; the adapter supplies no
relation binding or security assumption.

## Checked source connections

`ConnectionRoot.RootCertificate` is indexed by an admitted structured program,
a construction routing, a source role and an actual constructed participant.
Its fields contain finite input/output layouts, a reachable source library,
the existing instruction correspondence and an `Alignment` derivation. The
shared `RootCertificate.simulation` theorem produces `Original.Simulation`
against the actual `Domain.participant`. It quantifies over nominal domain
models, all physical input rows, typed external replies and stopping outcomes.
Malformed input rows refuse; they do not acquire invented source values.

The return relation is `Original.CompleteReturns`. It retains the entire
role-visible nominal result row, its sorts and arity, the selected profile
history and the empty root occurrence stack. Acceptance is a later projection
of that relation. Each physical checkpoint retains the input frame and the
source components decoded by the input ABI.

The simulation is relative to the certificate's explicit source input ABI.
Scope preservation alone does not fix the order of visible public inputs or
require every visible component to be present. The common generator derives
source-order data locations and service associations from the source signature.
An admission consumer must pin that ABI to its source/request selection before
using the connection as a required source-stage link; it must not existentially
choose an ABI from proof evidence. The current root interface does not itself
replace that admission boundary.

`RootCertificate.facts` supplies three consequences of the same certificate:
the exact source equation before construction, full simulation and reached-action
coverage of the occurrence source. Coverage is a separate induction over the
alignment derivation, before a missing route could turn construction into a
refusal. It is not inferred from a simulation of two refusing processes, and
it is not an additional protocol-author obligation.

### Source libraries and symbolic composition

A `ConnectionLibrary.SourceTemplate` fixes an actual declaration, its complete
signature, role, input pattern and checked normalization. The library contains
reachable declaration/role pairs in dependency order. The common proposer
finds these from typed applications, including applications under repeats;
author code supplies no declaration indices, per-call slot maps or reduced
source process. Helpers execute their actual admitted bodies. Mathematical
reference equations remain separate library laws.

Library construction runs the existing normalizer in compiled Lean meta code
and prints its result with the existing literal printer. It reduces the closed
input data first; proposal generation does not repeatedly unfold the complete
normalizer call in the elaborator. The resulting `SourceTemplate` retains the
same kernel-checked normalization equation, call identities, role and visibility
obligations. Native evaluation supplies no proof or admitted equation. Normalized
bodies and the checked template records are shared through ordinary declarations.

An application derivation checks a finite prefix of the actual flat target,
its physical extent, every projected result and the caller continuation.
A repeat checks its body/header interface with a symbolic count; no runtime
iteration count is unrolled. The same constructors serve producer and validator
roles, plain delivery, Fiat–Shamir delivery and supported private services.
Unknown shapes refuse rather than become semantic assumptions.

Internal applications carry a finite typed return selection. The
`ConnectionReturnProjection.form_denote` theorem proves that projecting a
callee changes only its successful return leaves: sends, queries, helper and
partial calculation invocations, reached stops, nested applications and repeat
callbacks remain unchanged. An omitted pure returned expression needs no
physical cell. Each selected component still requires exact nominal readback.
The application also checks the finite syntax equality
`continuation selection next = next`. The shared `bind_continuation` theorem
then proves composition with the actual caller for every model and typed reply;
no semantic equation is assumed from an author. The ordinary library template
and full nominal signature stay shared by reference. Root return relations,
ABI assembly and independent route coverage remain complete and unchanged.

A returned history occupies either a fresh cell separate from selected data
outputs, or a checked incoming current-history cell disjoint from those outputs.
The latter case still checks the exact suite, returned history and immutable
caller captures. Layouts keep one logical designation per physical cell, so an
alias-sensitive continuation may still be refused. Return selection supports
any finite subset whose substitution passes the syntax equality; it does not
prove algebraic equivalence of different continuations. Helper expansion handles
a return projection or one total primitive with present operands or a
statically absent operand; arbitrary helper inlining is not claimed. These are
proposer/derivation coverage limits, not restrictions added to the theorem's
runtime quantifiers.

Normalized source syntax and templates are checked constants. Successful
closed body alignments are checked once and referenced by their application;
an imported exact placement may reuse that declaration. Different argument,
frame, SSA or occurrence placements still require different alignments. This
is not a theorem transporting an alignment under arbitrary relocation.
The proposer may cache closed syntax or discover a prefix from residual target
syntax. Those hints do not authorize evidence: the ordinary alignment, extent,
readback and continuation rules check every accepted proposal.

The pure input-layout and routing proposal functions belong to the core
construction package because generated certificate types can mention them.
They confer no authority without the checked certificate fields. Meta-level
search and printing remain in the tooling package. Auxiliary declarations use
Lean's ordinary expression-sharing operation before `addDecl`; their types and
values still receive the same kernel checks.

### Property consumers and remaining admission

The security package derives public source reading, observation coherence,
full-value transport and selected acceptance agreement from a root certificate.
Its public Fiat–Shamir reading requires the selected replacement profile and
no local service routes. Runtime simulation and sampled honest-pair consumers
have their own interfaces and premises. A connection alone supplies neither
soundness nor successful honest execution, a sampling law, an extractor law or
a security receipt.

`Construction.checkCompiled` checks transcript construction and exact source
occurrences. The unproved projection walker has been removed. Receipt admission
requires `ConnectionAdmission.Required` separately, with its canonical source ABI
and routing fixed before proof selection. Missing connection evidence keeps the
claim open. The typed root certificate is the default proof method; a direct
proof of the same fixed proposition remains admissible. See
[the correspondence contract](participant-projection.md).

## Mathematical reference installation

A reference library supplies formulas and dependency laws separately from the
source connection. `BodyIn` associates a complete nominal helper signature and
its exact typed body with an admitted source definition. The optional
`infer_reference_installation` proposer fills finite library-binding data and
constructs ordinary body-association proofs. It does not supply a mathematical
law or change a requested relation. A source-selected relation can anchor the
association record so two matching helper chains cannot be confused. Shared
library theorems then consume that record for the actual helper table.

Search may refuse. An incomplete association record, an unbound data field or a
rigid body mismatch does not create an assumption. Records that require a
premise instead of a body association are outside this proposer. A completed
association that leaves data undetermined is refused without enumerating other
witnesses for that partial interface. This is an authoring diagnostic, not a
completeness claim about inference. The kernel checks successful installations;
receipt meaning, stage links and security proofs retain their separate owners.

## Participant normal forms

`Structured.NormalForm.normalize` computes one role's form of a typed protocol
body by symbolic evaluation under the participant rules above. A form lists the
role's ordered sends, receives and queries; presence splits on an optional
input or on a component of a returned tuple, where an operation first needs it;
guards on equalities, including arbitrary Boolean conditions compared with
`true`; exact Math invocations on optional components; kept helper invocations
and helper laws; repeats
of callback regions; and callee applications at child contexts. It ends in
returned components or a stop. Every step is structural, and a body outside the
fragment is refused with a named reason. A form is indexed by a signature: the
helper laws it may use, keyed by the helper's sorts and pinned to inputs or
literals, and the callee forms it may apply, keyed by callee signature and role.

A Math call can use a checked passing law on components. Otherwise `Form.math`
invokes the exact component helper table and binds its optional output tuple.
It neither sequences all operands before the call nor infers a law from the
helper's name. A closed returning or stopping law is insufficient to replace
this component invocation. Absent inputs, ignored inputs, stops and events
therefore follow the existing component meaning. An arbitrary present Boolean
guard uses `Equality.boolean`; false rejects and an absent condition stops as
incomplete. No premise asserts that a helper result or received Boolean is true.

`NormalForm.normalize_soundOn` proves this equation for arbitrary action
interpretations and iteration observations. Actual source call sites and dynamic
repeat coordinates are retained in that interpretation. `normalize_sound` is its
silent-observation specialization: when normalization returns a form whose law
uses call their laws' own helpers (`CallsMatch`), the body's participant process
at the role is the form's process, in every model, for
every context whose mapped roster roles are distinct from the role
(`RosterDistinct`), on every input the pattern describes, under every helper
table whose invocations satisfy the signature's laws (`LawsHold`) and every
protocol table whose invocations of the signature's callees are the given
callee processes (`CalleesHold`). `sound_uniform`, `callback_sound_uniform` and
`participant_sound_uniform` restate it for the uniform participant meaning, for
a repeat callback's carried state and for an entry's `Program.participant`.
Each generated participant normal form is an instance: the kernel checks by
evaluation that the normalizer returns the printed form and that the form's
process is the readable one.

## Component declaration context

`SourceDeclarations.check` admits the last structured-source slot against all
protocol headers and their retained contracts. It reconstructs only the bounded
source layout fragment in the [shared wire specification](../../../docs/spec/formats/structured-source.md#retained-source-declarations).
It does not infer linearity from a Boolean/field carrier or invent missing
source/static declarations. `Import.checkUnitHeaders` runs this check before
body admission. Old ten-slot snapshots have no compatibility reader.

The selected protocol may be a library root with linear inputs or residual
outputs. Selection alone supplies no final acceptance evidence. The same exact
layout, single holder, sealed linear declaration and successful-exit ownership
checks apply to selected and nested protocols. Clause-free wrappers assert no
relation. Protocols with any retained clauses still require unique relation
coverage of every linear port, consistently across each closed source type.
`EntryContractBinding` separately requires the actual selected root, its unique
named target statement and the target's exact acceptance output. Component
association does not supply that binding or prove its relation.
