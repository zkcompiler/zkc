# Domain values

Typed native algebra and physical value admission use these domain distinctions.
This chapter states shared laws; a native implementation claim needs its
actual instance and evidence. Independent formal examples retain their own
[model scope](../../../lean/docs/README.md).

A domain interpretation gives source values and operations their mathematical
meaning. It declares its sorts, operations, legal inputs and source denotation.
The [language](../../../lean/docs/spec/semantics.md#mathematical-and-participant-layers) supplies the
typed control structure in which those operations occur.

## Sorts and interpretations

For a language with sort type `Ty`, a value interpretation assigns
`Value : Ty → Type`. Its operation interpretation takes the declared ordered
arguments and produces a [body](../../../lean/docs/spec/semantics.md#effects-and-observations) returning the
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
basis `(1, X, …, X^7)`. The installed nominal domain `koala-bear.ext4-binomial3`
denotes `F_p[X]/(X^4 - 3)` with the same base and ascending basis
`(1, X, X^2, X^3)`; `X^4 - 3` is irreducible over `F_p` because 3 is not a
square modulo `p` and `p ≡ 1 (mod 4)`. Each identity fixes the base, degree,
defining polynomial and basis. Arithmetic is polynomial quotient arithmetic, not
integer arithmetic modulo `p^d`. Embedding sends `a` to `(a, 0, …, 0)`. The two
extensions are distinct domains: neither embeds in the other, and a value of one
is never a value of the other.

Both hold `ExtensionField`, `TwoAdicField`, `Field`, `CommRing` and
`CharacteristicNotTwo`; their evaluation domains are the base field's
power-of-two subgroups and cosets. The octic extension additionally holds
`IndexRandomness` and is the challenge field of the installed octic Merlin and
hash-chain suites and of the random service. A sampling service, transcript
suite or row-commitment scheme for another field is a separate installation with
its own identity.

Natural casts land in the prime subfield. Generic source natural constants are
specialized modulo the characteristic; closed `field.constant` and
`vector.constant` attributes must be canonical decimal representatives below
`p`. They do not encode arbitrary extension coordinates. The catalog's existing
`modulus` member records this characteristic bound for natural casts, not the
extension's cardinality. Public extension coordinates use the canonical
[native structured codec](../formats/messages.md). A
[binary field](#binary-fields) writes its constants other than `0` and `1` as
[bit-pattern literals](#bit-pattern-literals).

The native installation uses pinned Plonky3 0.8.0's
`BinomialExtensionField<KoalaBear, d>` for both degrees; the executable independent
`Tools.Interactive.ExtensionReference` uses fixed coordinates, convolution and
checked exponentiation for inverses of the octic extension. It asserts no unproved Lean field instance
or native adequacy theorem. Generic formal PIR semantics remains parameterized
by mathematical fields and the embedding laws required by each consumer.

### Registered residue fields

The native Plonky3 0.8.0 installation registers these additional exact domains:

| Identity | Prime base and characteristic | Degree | Defining polynomial | Coordinate bytes |
| --- | --- | --- | --- | --- |
| `baby-bear` | `baby-bear`, 2013265921 | 1 | — | 4 |
| `baby-bear.ext4-binomial11` | `baby-bear`, 2013265921 | 4 | `X^4 - 11` | 4 |
| `goldilocks` | `goldilocks`, 18446744069414584321 | 1 | — | 8 |
| `goldilocks.ext2-binomial7` | `goldilocks`, 18446744069414584321 | 2 | `X^2 - 7` | 8 |

Each prime base holds `PrimeField`, `TwoAdicField`, `Field`, `CommRing` and
`CharacteristicNotTwo`. Each extension holds the same facts except `PrimeField`,
and additionally `ExtensionField` with exactly the listed `BaseField`.
Extensions use ascending binomial coordinates `(1, X, ..., X^(d-1))`;
embedding sends `a` to `(a, 0, ..., 0)`. Different families and different
extensions never acquire implicit embeddings, including equal-width values.

The registered residue family includes the three existing KoalaBear domains
above. Every member supplies field, vector, polynomial, quadratic-round and
sparse-matrix representations under `plonky3.<identity>/0`, with the respective
suffixes (none), `-vector`, `-polynomial`, `-quadratic`, `-sparse-coo` before `/0`.
Logical codec identities are `zkcv.<kind>.<identity>/0`. Native message payloads
cover field, vector and matrix values; polynomial and round values remain local.
Canonical readable coordinates are decimal integers below the prime
characteristic, including the full Goldilocks range above `2^63`.
Canonical little-endian byte operations use the listed bytes per coordinate,
in ascending basis order, and reject out-of-range words or incomplete elements.
Montgomery32 byte operations are installed only for KoalaBear and BabyBear and
their registered extensions; Goldilocks has no such representation.

The new extension fields separately install `IndexRandomness` and services
`random.baby-bear.ext4-binomial11/0` and
`random.goldilocks.ext2-binomial7/0`. Their explicit Merlin byte suites are
`merlin3.baby-bear.ext4-binomial11.rejection31le/0` and
`merlin3.goldilocks.ext2-binomial7.rejection64le/0`. These profiles are not
inferred from arithmetic capabilities. The explicit [Poseidon2 row instances](oracles.md#poseidon2-instances)
commit base and extension rows; the hash profile remains a separate choice from
the field. The OpenVM adapter retains its independent upstream pin.

## Binary fields

The installed nominal domain `gf2-64.pentanomial-4-3-1` denotes
`K = F_2[x]/(x^64 + x^4 + x^3 + x + 1)` with the polynomial basis
`(1, x, …, x^63)`. The installed nominal domain
`gf2-64.pentanomial-4-3-1.ext3-trinomial1` denotes `E = K[y]/(y^3 + y + 1)`
with base `K` and basis `(1, y, y^2)`. The pentanomial is irreducible over
`F_2`: `x^(2^64) ≡ x` modulo it and `gcd(x^(2^32) - x, x^64 + x^4 + x^3 + x + 1) = 1`.
The trinomial is irreducible over `K`, because a root would lie in
`F_8 ∩ K = F_2`, where `y^3 + y + 1` has none. So `|K| = 2^64` and
`|E| = 2^192`. Each identity fixes its base, degree, defining polynomial and
basis. Arithmetic is polynomial quotient arithmetic over `F_2`; it is not
integer arithmetic modulo `2^64`. `field.embed<E>` and `vector.embed<E>` send
`a` to `(a, 0, 0)`. `K` has no declared base: `F_2` is not an installed domain.

Both fields have characteristic two and hold `Field` and `CommRing`; `E` also
holds `ExtensionField` with `E.BaseField = K`. Neither holds `PrimeField`,
`TwoAdicField` or `CharacteristicNotTwo`. Addition is the exclusive or of bit
patterns, negation is the identity and subtraction equals addition. Operations
that need an integer residue, a two-adic multiplicative subgroup or division by
two are not defined on these fields: coset domains, interpolation and folding
on two-adic subgroups, compile-time prime interpolation, Montgomery residues,
the [Ring](ring-expressions.md) row provider's bulk kernels and
[relation bundles](relation-bundles.md). Ring formulas over them still form,
with the natural literals `0` and `1`, and pointwise maps realize through them.
Inverting zero refuses, as in every installed field.

An element's **bit pattern** lists its coordinates over `F_2`: bit `i` of an
element of `K` is the coefficient of `x^i`, and bit `64 j + i` of an element of
`E` is the coefficient of `x^i y^j`. The pattern of an element of `E` is the
patterns of its three coordinates in basis order. Every pattern of 64 or 192
bits is exactly one element. Natural casts land in the prime subfield `F_2`, as
in every field: `field.from_index(n)` is `n mod 2`, and the catalog's `modulus`
member is `2`.

### Bit-pattern literals

A closed constant of a binary field is written `0`, `1` or a bit-pattern
literal: `0x` followed by lowercase hexadecimal digits without a leading zero,
read as an unsigned integer whose binary digits are the element's bit pattern.
Its value is at least two and below `2^d`, where `d` is 64 for `K` and 192 for
`E`. Every element therefore has exactly one constant spelling: in `K`,
`x^4 + x^3 + x + 1` is `0x1b`; in `E`, `y` is `0x10000000000000000`. Uppercase
digits, leading zeros, `0x0`, `0x1`, decimals above one and values of `2^d` or
more refuse; nothing is reduced. The form applies wherever a concrete binary
field's constant is an attribute: `field.constant`, each element of
`vector.constant` and `algebra.constant`. A symbolic field still admits only
`0` and `1`, and prime fields and their extensions keep canonical decimal
residues. In source, `kernel<K>("field.constant"; "0x1b")` writes such a
constant; numeric source literals remain decimal.

The native installation uses pinned Plonky3 0.8.0's `p3-binary-field` types
`Poly64` and `Poly192`, which store exactly these bit patterns. Their integer
constructors cast through `F_2`, like natural casts. Readable and wire forms
are in the [Entry guide](../runtime/entries.md) and the
[message grammar](../formats/messages.md).

## Group identity

`curve.identity<G> : () → group:G` returns the identity of the exact nominal
`G` and requires `ScalarAction(G)`, including its associated scalar field,
consistently with the other native curve operations. It has no operands or
attributes. For every group value `P` and associated scalar `s`, its denotation
`0_G` satisfies `0_G + P = P`, `P + 0_G = P`, `s · 0_G = 0_G`, and
`0 · P = 0_G`. Empty group sums and empty supported MSMs denote this value.
Neither `curve.generator` nor an empty group vector denotes a group identity.

The total mathematical operation is `algebra.group_identity`, whose result type
supplies the nominal group. It has no source effects or operand dependencies.
Its checked native recipe is exactly the nullary `curve.identity<G>` binding;
substituting a generator, another group, or a provider/codec for another group
is invalid. The native realization retains the ordinary allocation/output
limits and may exhaust resources. Totality of the mathematical denotation does
not make native allocation infallible.

The installed providers are `dalek/curve.identity` for `ristretto255.group` and
`edwards25519.prime`, and
`arkworks/curve.identity` for `bls12-381.g1`, `bls12-381.g2`, `bls12-381.gt`,
`bn254.g1`, `bn254.g2`, and `bn254.gt`. Identity uses the same group
representations and canonical codecs as other operations in each family. For
GT it is multiplicative one; it is not extension-field zero. Dense GT vectors
are not installed.
These are native profile contracts, without a native adequacy or security proof.

## Prime-order Edwards25519

`edwards25519.prime` denotes the prime-order subgroup of Edwards25519, with
scalar field `ristretto255.scalar` of order
`2^252 + 27742317777372353535851937790883648493`. The generator is the usual
Ed25519 basepoint. It has its own nominal type, physical representations
`dalek.edwards-prime/0` and `dalek.edwards-prime-vector/0`, and native codecs.
It is not interchangeable with the Ristretto quotient group. All installed
group operations preserve subgroup membership, including identities and MSMs.

Native input decoding checks canonical compressed Edwards coordinates and
prime-subgroup membership. The explicit [mathematical byte operations](../realization/external-constructions.md#mathematical-byte-encodings)
can instead decode a canonical full-curve encoding and multiply by eight.
That operation changes the represented point. Protocols needing the original
wire observation must retain its bytes separately; a scalar action over the
full cofactor-eight curve is not installed.

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

Two instances are installed. The first uses `bn254.fr`, `bn254.g1`, and
`bn254.g2`; both groups' scalar field is `bn254.fr`. Its scalar modulus is
`21888242871839275222246405745257275088548364400416034343698204186575808495617`.
The base field used to encode group coordinates is distinct. The scalar domain
has the pinned generator-5 two-adic root convention and two-adicity 28.
The second uses `bls12-381.fr`, `bls12-381.g1`, and `bls12-381.g2`, with the
BLS12-381 scalar modulus given above for `bls12-381.fr`. No two-adic root
convention is installed for this field; a protocol that needs a root of unity
states it as a constant. `bls12-381.g2` has the 96-byte compressed
[mathematical encoding](../realization/external-constructions.md#mathematical-byte-encodings),
canonical representation `arkworks.bls12-381-g2/0`, group vectors
`arkworks.bls12-381-g2-vector/0`, and codecs `zkcv.group.bls12-381.g2/0`
(tag 51) and `zkcv.groups.bls12-381.g2/0` (tag 52). Native group and pairing
operations use arkworks. The current scalar Lean interpretation uses abstract
group/module equations and does not execute or prove adequacy of these
production pairing primitives.

### Pairing results

A catalog may additionally declare `F.PairingGT`, a group distinct from its two
source groups with `ScalarAction` and associated scalar field `F`.
`pairing.apply<F> : group:F.PairingG1 × group:F.PairingG2 → group:F.PairingGT`
returns the bilinear pairing value. Catalogs supporting only `pairing.check`
need not supply this target association; they cannot form `pairing.apply`.

The total mathematical operation `algebra.pairing` has the same ordered source
and target identities. Zero source points are valid. Its target is the
prime-order subgroup, after final exponentiation, not a Miller-loop value or an
arbitrary element of an extension field. Abstract additive group notation is
retained: target `group_add` multiplies target-field elements, `group_scale`
exponentiates, zero denotes the multiplicative identity, and negation inverts.

The installed targets are `bn254.gt`, with scalar field `bn254.fr`, and
`bls12-381.gt`, with scalar field `bls12-381.fr`. Each target's generator is the
pairing of its installed G1/G2 generators. The canonical representations are
`arkworks.bn254-gt/0` and `arkworks.bls12-381-gt/0`. The codec
`zkcv.group.bn254.gt/0` is ZKCV tag 50 followed by exactly 384 canonical
arkworks bytes; `zkcv.group.bls12-381.gt/0` is tag 53 followed by exactly 576
bytes, the twelve base-field coefficients. Decoding checks canonical encoding
and target subgroup membership; extension-field zero is invalid. Only
individual target-group values are installed, including recursive data
containers; dense target-group vectors are not installed.
The current scalar Lean import profile does not admit pairing target operations
or provide a native GT adequacy proof.

## Byte strings

`bytes` is an immutable byte string, exposed as `zkc::bytes::Bytes`. It has Copy,
Drop, participant-family admission and external construction authority. The
native representation is `native.bytes/0`; the canonical MLIR type is
`!data.bytes`. Its collection interface exposes
unsigned byte elements and one runtime extent. This grants neither numeric
interpretation nor finite-operation admission. Bytes do not imply an integer,
field or point encoding.

`zkc::bytes` exports `empty`, `repeat`, `append`, `concat`, `join`, `slice`, `at`,
`length` and `equal`. `append` checks that its index operand is in 0..255. `slice` takes a
start and length; the complete interval must be in bounds, including an empty
slice. No operation implicitly truncates, wraps or pads. Output allocation and byte limits
are checked before copying. Byte storage is charged by its byte length, not by
the numerical-element limit. Readable input/output uses JSON arrays of integers
in 0..255. [Native message framing](../formats/messages.md) remains separate
from the byte payload.

`repeat(byte, count)` checks the byte even when count is zero, then returns
exactly count copies. `join(parts: Sequence<Bytes>)` concatenates fragments in
order; an empty sequence produces empty bytes. It checks fragments in order,
checked total length, wire and output allowances before allocating. Neither
operation adds framing or transcript observations. Native allocation and work
charges follow the [capacity contract](../runtime/capacity.md#byte-construction).
These authored operations have their own charge boundaries;
replacing a scalar loop does not promise identical exhaustion behavior.

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

For messages, the [interaction](../../../lean/docs/spec/semantics.md#mathematical-and-participant-layers)
specifies the entire permitted reply domain, including hostile values of the
declared shape. An honest arithmetic predicate is a separate condition.
The [codec contract](../realization/codecs.md#codec-domains) specifies the
accepted external language, decoding and malformed-input behavior. The public
dimension syntax is one selected profile; a different shape language
specifies its own evaluation and admission rules.

## Domain adequacy

A source-adequacy claim identifies the actual admitted inputs and proves that
their denotation is the stated mathematical object or computation. Type
correctness, source-name equality, successful compilation and finite tests do
not by themselves establish that connection.

An operation can retain a logical computation for later
[interpretation](../../../lean/docs/spec/semantics.md#mathematical-and-participant-layers). Its
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
The physical spelling is `resource_unit:D@logical.resource_unit/0`. Its empty
payload is distinct from runtime bookkeeping for ownership and identity. MLIR
uses `!local.capability<"resource_unit:D">` and the existing physical data wrapper.
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
source/MLIR and Rust physical admission check these rules;
the compiler output alone is not admission evidence. Native execution maintains
an authenticated occurrence, generation and owner, rejects cloned handles at a
multi-port boundary and stale generations after a pass, and transfers newly
created units through explicit results. The current scalar Lean profile does not import affine logical resource units.

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
