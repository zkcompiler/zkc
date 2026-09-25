# Domain values

A domain interpretation gives source values and operations their mathematical
meaning. It declares its sorts, operations, legal inputs and source denotation.
The [language](../language/programs.md#language-signatures) supplies the
typed control structure in which those operations occur.

## Sorts and interpretations

For a language with sort type `Ty`, a value interpretation assigns
`Value : Ty → Type`. Its operation interpretation takes the declared ordered
arguments and produces a [body](../core/execution.md#bodies) returning the
interpreted result sort.

Field, scalar, group, digest, index and shape-indexed values have distinct sorts
when the selected language declares them so. Distinct sorts can have equal
mathematical carriers or native widths without becoming interchangeable source
types. A program can contain multiple field sorts; each operation uses its
declared domain and arguments.

An embedding or layout/index conversion is an explicit operation with the laws
required by its consumer. A storage width, argument position or shared external
name does not establish those laws. A profile that identifies two values through
a quotient or representation relation states that relation explicitly.

## Local Boolean operations

`bool.not : bool → bool` returns Boolean negation. `bool.or` and `bool.and`
take two Booleans and return their disjunction and conjunction. They have no
static domain arguments or attributes. These are strict value operations:
both arguments already exist, and all preceding evaluation, failures and
resource charges remain. They introduce no branch, lazy evaluation or selection
of a capability, opening state, or other resource.

An implication between already computed predicates is `or(not(p), q)`.
A strict Boolean selection can be composed as
`or(and(condition, yes), and(not(condition), no))`; no separate select or
polymorphic selection contract is installed. A successful Boolean calculation
does not authorize erasing its execution costs or operations that produced its
arguments.

## Nominal field extensions

An extension field `E` declares an associated `E.BaseField`. The capability
`ExtensionField(E)` implies `Field(E)` and supplies an explicit embedding
`field.embed<E> : field:E.BaseField → field:E`, with no attributes. Its
mathematical meaning is the declared unital field embedding. Mixed base/extension
arithmetic requires this operation; equal physical widths never insert it.
`ExtensionField` does not imply `PrimeField`.

The installed nominal domain `koala-bear.ext8-binomial3` denotes
`F_p[X]/(X^8 - 3)`, where `p = 2130706433`, with base `koala-bear` and ascending
basis `(1, X, …, X^7)`. Its identity fixes the base, degree, defining polynomial
and basis. Arithmetic is polynomial quotient arithmetic, not integer arithmetic
modulo `p^8`. Embedding sends `a` to `(a, 0, …, 0)`.

Natural casts land in the prime subfield. Generic source natural constants are
specialized modulo the characteristic; closed `field.constant` and
`vector.constant` attributes must be canonical decimal representatives below
`p`. They do not encode arbitrary extension coordinates. The catalog's existing
`modulus` member records this characteristic bound for natural casts, not the
extension's cardinality. Public extension coordinates use the canonical
[artifact codec](../../compiler/artifact-format.md#octic-koalabear-extension).

The native installation uses pinned Plonky3 0.5.1; the executable independent
`Tools.Interactive.ExtensionReference` uses fixed coordinates, convolution and
checked exponentiation for inverses. It asserts no unproved Lean field instance
or native adequacy theorem. Generic formal PIR semantics remains parameterized
by mathematical fields and the embedding laws required by each consumer.

## Pairing field capabilities

`PairingField(F)` implies `Field(F)` and declares distinct associated groups
`F.PairingG1` and `F.PairingG2`. An installed pairing operation uses their
declared bilinear pairing. `pairing.check<F>(left,right)` accepts ordered group
vectors and returns whether the product of their pairings is the target-group
identity. It requires equal lengths; the empty product is the identity. Swapping
G1 and G2 is a type error, even if a representation happens to share a width.
Group scaling separately requires `ScalarAction` and the appropriate scalar-field
association. No setup, relation satisfaction, or security theorem follows from
this capability alone.

The installed instance uses `bn254.fr`, `bn254.g1`, and `bn254.g2`; both groups'
scalar field is `bn254.fr`. Its scalar modulus is
`21888242871839275222246405745257275088548364400416034343698204186575808495617`.
The base field used to encode group coordinates is distinct. The scalar domain
has the pinned generator-5 two-adic root convention and two-adicity 28. Native
group and pairing operations use arkworks; Lean's executable arithmetic is
independent, while group equations and subgroup validation use an explicitly
trusted primitive service.

## Checked indices

The installed `index` value is a natural number strictly below `2^64`.
It is independent of a field and of the target pointer width. `indices` is an
immutable bounded ordered sequence of these values; duplicate entries remain
separate occurrences. Neither type establishes an oracle-domain membership fact.

`index.constant` has one canonical decimal u64 attribute. `index.add`, `sub` and
`mul` refuse overflow or underflow; `div` and `mod` refuse a zero divisor.
`equal` and `less` return Booleans. Arithmetic never wraps. `indices.empty`,
`append`, `at` and `length` construct and inspect a sequence; `at` refuses an
out-of-range position. Allocation ceilings are additional execution conditions.
All these operations have no static domain argument.

`field.from_index<F>` is the explicit natural cast into `F`. It reduces modulo
the field characteristic and generally loses information. It does not authorize
using the resulting field element as an index. An oracle checks the original
index against its verifier-owned shape before authenticating a row.

## Shapes and actual values

A declared shape relates to the actual admitted value, including its domain,
dimensions and element order. An input adapter checks the required lengths and
resolves each used identifier before passing a value to a shape-indexed
operation. A total mathematical lookup does not authorize filling absent input
data with a convenient default.

[Vectors and linear combinations](vectors.md) give the shared meanings of
ordered scalar/group sequences and linear contractions. A dynamically sized
vector is distinct from a coordinate point or a polynomial table; conversions
establish their shape and indexing connections explicitly.

For messages, the [interaction](../language/interaction.md#roles-and-phases)
specifies the entire permitted reply domain, including hostile values of the
declared shape. An honest arithmetic predicate is a separate condition.
The [codec contract](../realization/codecs.md#codec-domains) specifies the
accepted external language, decoding and malformed-input behavior. The public
[dimension syntax](../profiles/source/public-dimensions.md) is one selected profile; a different shape language
specifies its own evaluation and admission rules.

## Domain adequacy

A source-adequacy claim identifies the actual admitted inputs and proves that
their denotation is the stated mathematical object or computation. Type
correctness, source-name equality, successful compilation and finite tests do
not by themselves establish that connection.

An operation can retain a logical computation for later
[interpretation](../core/interpretations.md#interpretation-interface). Its
eventual implementation refines the same declared operation on the same bound
operands, including failure and retained effects under the applicable execution
relation. Keeping an operation abstract does not supply a cryptographic theorem.

## Logical resource units

`resource_unit:D` is a nominal, role-local affine permission with no value
payload. `D` identifies an exact selected nominal slot, independently of its
empty storage representation. Distinct slots are distinct types. It has no
algebraic capability, randomness, cryptographic assumption, proof evidence,
public codec, or transcript encoding. It is not a field/domain parameter or
an escape hatch for arbitrary abstract source types. A frontend maps a selected
opaque zero-storage type to this slot only after checking and coherent linking.
The downstream carrier admits the logical permission independently; it does not
certify that the frontend performed those checks.

The portable slot spelling is a case-sensitive ASCII identifier of 1–128 bytes,
starting with a letter, with subsequent letters, digits, `_`, `-`, or `.`.
Slot selection must preserve exact nominal equality and inequality; truncation
or an unchecked hash collision assumption does not establish that relation.
The physical spelling is `resource_unit:D@logical.resource_unit/1`. Its empty
payload is distinct from runtime bookkeeping for ownership and identity. MLIR
uses `!pir.capability<"resource_unit:D">` and the existing physical data wrapper.
No byte wire encoding is installed, including for the empty payload.

The closed logical operations have one static slot argument `D`, no attributes,
and the exact signatures below. Their implementation identifiers are
`logical/resource_unit.create`, `logical/resource_unit.pass`, and
`logical/resource_unit.consume`; they select logical bookkeeping, not an
external backend or provider.

| Operation | Inputs | Results | Meaning |
|---|---|---|---|
| `resource_unit.create` | none | `resource_unit:D` | Create a fresh role-owned logical occurrence |
| `resource_unit.pass` | `resource_unit:D` | `resource_unit:D` | Consume the current permission and transfer its successor |
| `resource_unit.consume` | `resource_unit:D` | none | Consume the permission without a successor |

Creation establishes no external guard or evidence. Any actual guard remains a
separate operation with its original success/failure behavior. Producer sites,
used ports, and consuming or fallible unit-return calls survive lowering and
admission even when their payload storage is empty. There is no purity or
replay permission inferred from zero storage.

Aliasing, returning the same permission twice, or expanding it into two product
ports cannot duplicate it. Each use consumes its SSA binding; distinct nominal
slots cannot substitute for one another. Local/protocol calls and selected
control regions preserve role custody and the existing affine capture/carry
rules. Dynamic invariant capture of an affine value remains refused. Independent
source/MLIR, Rust physical, and Lean source/physical admission check these rules;
the compiler output alone is not admission evidence. Native execution maintains
an authenticated occurrence, generation and owner, rejects cloned handles at a
multi-port boundary and stale generations after a pass, and transfers newly
created units through explicit results. The reference maintains logical
occurrences, generations and owners independently of native handles.

This permission is affine: unused values may be dropped, including explicit
physical release. A stronger use obligation, such as must-consume, is a
different discipline with its own contract. Existing generic requirement rules and Fiat–Shamir construction refusals
are unchanged; logical resource operations grant no cryptographic replay law.

On a local frame's successful exit, only resource-unit occurrences explicitly
returned from that frame remain live. On a stopped exit, no occurrence from that
frame is returned. Unreturned inputs and newly created units are retired;
previously live units outside the frame and other kinds of consuming resource
state remain untouched. Each participant's own frame closes the same way when
that participant's execution ends: after its return only units among its
returned values remain live, and after its stop or cancellation none do. The
protocol's outcome is a stop when any participant stops, and that stop does not
reopen a participant that had already returned: the units it returned remain
its own. The residual state of each participant therefore holds no unit that it
neither consumed nor returned. This implicit affine
disposal is frame bookkeeping and adds no primitive request/response event. Explicit `resource_unit.consume` still
has its own operation observation.
