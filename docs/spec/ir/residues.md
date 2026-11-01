# Canonical represented arithmetic

Residue owns exact integer arithmetic modulo a selected modulus at the boundary
between nominal mathematics and machine words. Algebra retains nominal fields
and groups; Poly retains polynomial domains, quotient rings and bases. This
chapter specifies the arithmetic boundary. It does not grant protocol-stage
admission, an executable binding or native wire representation to a Residue type.
Implementation coverage is recorded in [status](../../status.md).

## Values and widths

`!residue.value<q : uiW>` denotes the canonical integers `0 <= a < q`, with
`2 <= q < 2^W`. The unsigned attribute fixes the modulus and storage width.
Current compiler formation bounds `W` by 4096; this is an implementation capacity,
not an algebraic condition. No spare high bit or primality premise is required.
Two different moduli or widths are different types. Scalars and ordinary ranked
tensors of these values are admitted; encoded tensors, unranked tensors and
vectors of opaque residue elements are excluded. Standard Vector operations use
builtin integer elements after word lowering.

A canonical residue is not a nominal field. An extension-field characteristic
alone supplies neither the full value representation nor a multiplication law.
A conversion must retain the exact nominal domain, coordinate basis, ordering
and coefficient relation. Likewise, coefficient equality does not identify a
quotient-ring value with an arbitrary collection.

## Operations

All operations below are total on their mathematical inputs. Elementwise tensor
forms require equal actual shapes, including dynamic extents, and preserve every
dimension. Equal tensor types alone do not establish equal dynamic extents. They supply
no allocation, custody or execution-resource contract.

| Operation | Meaning |
|---|---|
| `residue.constant` | A typed literal whose unsigned word and modulus match exactly and whose value is below `q` |
| `residue.add`, `residue.subtract`, `residue.multiply` | Canonical representative of the corresponding operation modulo `q`; inputs and result have one exact type |
| `residue.project` | Interpret a signless integer as an unsigned bit pattern and reduce modulo `q`; this is not canonical decoding |
| `residue.lift` | Return the canonical nonnegative integer in a signless word of at least the declared storage width |
| `residue.centered_lift` | Return the two's-complement encoding of the representative in `[-floor(q/2), ceil(q/2))`, in a word of at least the storage width |

The even-modulus centered tie is negative. Lifting does not reinterpret a large
canonical residue as a signed negative integer before applying this rule.
Projection can change a noncanonical value; a strict codec instead refuses it.
This difference must survive optimization and external-message admission.

## Word lowering obligations

Arith supplies fixed-width bit operations, whose wrap and poison rules remain
unchanged. For width `W`, a direct exact realization may compute addition and
`a + q - b` in `W+1` bits and multiplication in `2W` bits, reduce by unsigned
remainder, then truncate to `W`. The canonical input ranges establish that the
wide arithmetic cannot overflow. The selected widths must be checked from the
actual types, not supplied as an unchecked origin annotation. Unproved no-wrap
flags are prohibited. Centered subtraction intentionally uses two's-complement
wrapping in its declared output width.

An arithmetic converter is a producer, not a correspondence checker. It retains
the unchanged source while creating a private candidate. Any enabled subsequent
optimization needs an independent reader of actual operations, constants, SSA
uses, shapes and ranges. Unknown operations, a changed modulus, inadequate
width, an unresolved cast or stale source/candidate association cannot acquire
permission from successful conversion alone.

## Codec and physical boundaries

Exact field/coordinate/limb/byte relations belong to the
[codec contracts](../realization/codecs.md). They fix modulus, limb width and
count, top-bit constraints, order, basis, complete consumption and refusal
behavior. Montgomery and RNS forms require their own parameters and relations;
reduction is never an implicit decoding step. Existing native wire languages
retain their own identities and readers.

Tensor and Vector shape transformations do not establish writable ownership.
Private MemRef storage requires independently checked extent, alias, lifetime,
allocation/refusal, release and publication contracts under a reached numerical
call. Poison transfer padding may be ignored only when actual bounds establish
that it cannot contribute a lane. An `in_bounds` assertion is not that proof.
Native publication occurs only after the selected complete-result and resource
obligations have been checked; failed execution withholds successful outputs.

## Admitted scalar correspondence profile

The native reader accepts one closed, single-block function with at most 256
arguments/results and 4096 instructions. All residue occurrences have one exact
modulus and storage width. Source words are signless and at most 4096 bits;
intermediate candidate words are bounded by 8192 bits. Unused instructions are
checked. External functions, captures, calls, regions, unknown attributes and
operations outside the following profile refuse with `represented-arithmetic`.

The reader interprets source residue constants and arithmetic, integer constants,
unsigned projection and lifts. Its Arith profile contains integer constants,
zero extension, truncation, addition, subtraction, multiplication and unsigned
remainder by the exact modulus. Comparison/select additionally implement the
centered-lift boundary. Unsigned intervals establish nonwrapping intermediates,
nonzero divisors and lossless narrowing. Centered subtraction has a distinct
bit-pattern interpretation and can only flow through its checked select.
Returned ordinary integers must be canonical; arbitrary word-program equivalence
is outside this profile. Extension `nneg` and all arithmetic/truncation overflow
flags are refused, including on otherwise unused operations.

Modular expressions use constants, identities, commutativity and double negation.
The reader does not expand polynomials or decide every valid arithmetic identity.
Standard CSE and different sharing are admitted. There is no blanket approval for
arbitrary Arith canonicalization. A successful read compares complete signatures
and actual returned expressions with canonical-range or exact centered meaning.
It adds no persistent approval bit and must be repeated after mutation.

The numerical consumer profile additionally requires residue inputs and one
residue result. It reconstructs a closed residue expression from the actual word
interpretation, rather than copying the original formula. A target still owes
its nominal representation relation, installed kernel admission, shaped/buffer
correspondence and resource contract before executing that expression.

## Private pointwise tiles

A private candidate may use standard Linalg vectorization and One-Shot
Bufferization. The independently admitted result is one closed function with
one returned buffer, at most 256 input ports and 4096 instructions, and a static
rank-one tile of 1 through 256 lanes. Inputs are read-only tiles or scalar
broadcasts. They share the exact residue word type. Word operations may widen
internally under the scalar correspondence profile. No cross-lane operation,
mask, call, control region, capture or unresolved conversion is admitted.

MemRefs have a static full-tile extent, identity layout and default memory space.
An allocation creates a fresh private owner; identity casts retain that owner.
Full-tile reads require an initialized live object. Stores and copies can change
only private live objects. Copies preserve the complete element type and extent.
Deallocation consumes a private owner; it cannot release a borrow or a previously
released alias. The result transfers one initialized, live private allocation.
Every other private allocation must have been released. Returning a borrow,
reading uninitialized storage, leaking an owner or using a released alias refuses.
Allocation alignment is absent or a power of two no greater than 64 in this
profile; it does not establish the alignment of a later resident provider value.

A Vector transfer must have a zero index, identity permutation, no mask and an
exact vector/buffer shape match. These actual facts prove bounds independently
of `in_bounds`. Fully poisoned scalar padding is permitted only when no lane can
select it; it cannot feed arithmetic or publication. Nonuniform vector constants
and shuffles are outside the pointwise profile. Scalarization reconstructs the
actual lane expression, then the independent arithmetic reader establishes its
canonical value relation to the source. This also establishes prefix closure for
a final short tile; it does not authorize unchecked dynamic accesses.

The result of reading is an owned scalar interpretation, lane count and peak
requested canonical-word storage. Re-read after mutation. A successful read is
not a runtime allocation grant. MemRef allocation is a storage proposal; reached
native execution still owns fallible charged allocation, stop cleanup and
complete-result publication. Resident provider sizes, alignment and Montgomery
forms may differ and need their own representation and resource relations.
The standard IR's storage count is not a resident-memory or equal-refusal claim.
