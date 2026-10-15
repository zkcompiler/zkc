# Structured source export

`zkc-compile protocol-structured FILE --symbol=NAME` verifies the supplied
protocol-profile MLIR and exports a selected function with its retained
declarations. It performs no preparation, participant projection, finite
selection or realization. `original` names this export boundary; it does not
prove how an externally supplied module was produced.

The selected `protocol.func` has exactly one participant. Every input and output
scope is that participant. The complete unit is checked: supported unused
definitions are retained, and unsupported definitions are refused. Symbol names
are nonempty and unique across functions and domains. Helper references form an acyclic
graph; helpers cannot call the selected root. The independent
[formal admission contract](../../../lean/docs/spec/structured-source.md)
defines the Lean interpretation.

## Envelope and types

The current format is an exact tagged array, `zkc.structured-source/0`:

```text
[format, "original", source-sha256, entry-name, participant, domains, definitions]
```

`source-sha256` is `sha256:` followed by 64 lowercase hexadecimal digits, hashing
the exact supplied MLIR bytes. It identifies those bytes; it is not a proof of
their semantics or of export correctness. Every record below has the exact
displayed arity. Unknown tags, extra fields and unrepresented native attributes
are refused.

| Type | Native interpretation |
|---|---|
| `["bool"]` | `i1` |
| `["index"]` | unsigned 64-bit index |
| `["field", domain]` | nominal scalar field |
| `["vector", domain]` | immutable vector over that field |

The initial domain is `bls12-381.fr`. Groups, services, communication, affine
resources, variants, matrices, general arrays, arbitrary kernels and other
unlisted operations require a separately specified extension.

## Declarations

```text
["domain", name, input-types, ["elements", container-argument]]
["domain", name, input-types, ["indices", container-argument, 0]]

["function", name, kind, visibility, input-types, output-types,
 preconditions, origin, body]

["finite", name, visibility, input-types, output-types,
 domain-name, step-name, predicate-name]
```

A domain body consists of exactly one supported constructor and its matching
yield. Additional constructors are refused, including unused ones. The selected
input is a vector; other inputs remain part of the domain and callback ABI.
Elements yield one field value; indices yield one index. Only axis zero is
supported.

Function `kind` is `protocol`, `math` or `local`; visibility is `public` or
`private`. Math preconditions are exact arrays
`["index_bound", index-argument, container-argument, 0]`. Other relation
annotations are refused. Protocol and Math origin is `[]`; Local origin is
`[origin-name, [[key, value], ...]]`, preserving the ordered `logical_origin`
bindings without flattening them or substituting the helper symbol.
Bindings have unique nonempty keys and nonempty values, with at most 128 pairs.
The native verifier validates binding values against installed and canonical
static identities. Lean retains these values as opaque metadata and checks their
shape and uniqueness; it does not independently reproduce that identity registry.
Math helpers are private.

A finite declaration represents `local.finite_fold`. The empty predicate name
means no predicate. There is no implicit Unit leaf for an empty state or result.
The [finite ABI](../ir/finite.md) is retained: operands are `A ++ S ++ C`, the
step receives `S ++ I ++ A ++ C`, and the predicate receives `I ++ A ++ C`.
Callbacks are private and have the required Math or Local kind.

## Blocks, binding and control

```text
["block", instructions, terminator]
[descriptor, operand-indices, result-types, regions, site]
[input-types, output-types, body]                     # region

["return", indices]
["yield", indices]
["condition", indices]                              # Boolean first
["stop", reason, site]
```

A block starts with its inputs in original order. Each instruction prepends
its full ordered result list to the current context. Older references shift by
that list's length. Zero-result instructions leave the context unchanged but
still execute. Return and yield references preserve order, repetition and
identity even when their types coincide.

Regions are closed: their arguments are the actual explicit captures and loop
state, with no implicit access to the surrounding context. An `if` has two
regions from captures to result types. A `for` body takes
`index :: (state ++ captures)` and yields `state ++ captures`; a conditional
body yields a leading Boolean followed by state and captures. Continuing
captures must be the identical input values, accounting for the prefix of body
results. Type equality alone does not establish forwarding.
An unconditional stop in a loop body uses `for`; `for_condition` requires a
condition terminator. Nested branches in either form may still stop.

Pure mathematical instructions have empty sites. Local call/control instructions retain
their actual required sites. Nonempty sites are unique within a definition,
including nested regions. Stop reasons are `reject`, `abort`, `exhausted`,
`incomplete` and `refused`.

## Descriptors

| Descriptor | Meaning and interface |
|---|---|
| `["field.constant", domain, decimal-string]` | canonical scalar constant |
| `["field.add" / "field.subtract" / "field.multiply", domain]` | two fields to one field |
| `["field.equal", domain]` | two fields to Boolean |
| `["bool.constant", value]` | Boolean constant |
| `["bool.and" / "bool.or" / "bool.xor" / "bool.equal" / "bool.not_equal"]` | two Booleans to Boolean |
| `["select", type]` | Boolean and two equal-typed values to that type |
| `["bounded_at", domain]` | vector and index to field, with exact bound obligation |
| `["call", name]` | ordinary Math helper call |
| `["apply", name]` | Local helper or finite declaration call |
| `["local_call", name, participant]` | Protocol call to a Local helper with exact owner |
| `["fold", domain, step, predicate]` | total Algebra fold |
| `["if"]` | Local conditional over closed captures |
| `["for"]` / `["for_condition"]` | Local counted control |
| `["guard", participant]` | Protocol guard with exact owner; false rejects |

Every operand, result and region interface is checked against the selected
descriptor and referenced declaration. A same-typed result permutation can be
a valid different program. It is preserved rather than classified as a type
error. A bound for a different same-typed vector does not authorize a read.

Ownership is checked independently of operand types:

| Body kind | Admitted instructions |
|---|---|
| Protocol | Pure field/Boolean operations, select, Math call, Algebra fold, Local call, Protocol guard |
| Math | Pure field/Boolean operations, select, bounded read, Math call, Algebra fold |
| Local | Boolean constant, Local apply, conditional and counted control |

The descriptor can represent selection of any admitted value type. The current
native mathematical verifier admits Boolean and scalar-field selection in this
profile; vector and index selection are not yet native export paths.

Only Local bodies may end in an explicit stop. A guard retains the owner of
the original `protocol.guard`; projected `local.guard` is outside this source
stage. Local mathematical computation through realization/bindings is not yet
part of this import profile.

## Limits and evidence

The writer bounds source bytes to 16 MiB, the complete exported file (including
its final newline) to 1 MiB, strings
to 512 UTF-8 bytes, domains and definitions to 128 each, signatures to 512
positions and total instructions to 4096. The instruction count includes nested
bodies and one fold per finite declaration; it excludes terminators and domain
constructors. Lexical JSON and region nesting are bounded by 64. Helper reference
depth is bounded by 64. References are derived from stored instructions, with
at most two helper references per instruction; shared calls are not expanded for admission.
See the formal contract. All failures
produce diagnostics rather than a partial successful snapshot.

Export and independent import check a deliberately limited logical profile.
They do not establish frontend translation, participant projection, finite
algorithm selection, native provider arithmetic, runtime resource policies or
protocol security. A later compiler correctness result must relate the exact
source and target subjects under explicit observations and capacity premises.
