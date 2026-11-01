# Physical numerical plans

This chapter defines the represented-execution replacement for executable
pointwise parameters. [Status](../../status.md) records integration coverage.
The logical `numerical.map`, `numerical.sum` and `numerical.product` operations
retain their mathematical Ring parameter and nominal field. Their physical
calls use the one plan language below. Logical and physical admission are
different stages; an implementation name alone does not determine the stage.
The native binding's represented ports determine it.

## Carrier and domain

A physical invocation has one canonical JSON parameter, encoded as:

```text
["zkc.numerical-plan/0", expression, lanes, slots, locations]
```

`expression` is the nested canonical `zkc.ring/0` array, not an escaped JSON
string. It has one output and the exact input count of the binding's operand
mask. Every input and node has the binding's nominal field; embeddings are
excluded. The canonical inner expression occupies at most 4096 UTF-8 bytes.
The complete canonical plan occupies at most 16384 UTF-8 bytes.

`lanes` is an integer from 1 through 256. `slots` is a positive integer at most
the expression's node count. `locations` has one integer per expression node;
each is in `[0, slots)`, and every slot must occur. Array lengths and types are
exact. Extra entries, noncanonical encoding and the former bare executable Ring
parameter refuse. The development format remains version zero. Logical Ring
subjects remain unchanged; this is not a compatibility-reader alternative.

The plan is a storage proposal, not evidence that it computes the source.
Compiler admission separately compares the actual selected expression with the
retained mathematical subject. Native admission and the reached provider read
the actual expression and schedule independently of compiler decisions.

## Schedule meaning and independent validation

The binding mask determines row dependence. A constant is invariant; an input
is varying exactly when its mask bit is one. Arithmetic nodes are varying when
any operand is varying. This classification is recomputed from the actual DAG.
Invariant nodes run in topological order at the first reached row. Varying nodes
run in topological order for each chunk. An empty domain evaluates neither set.
Captured values never enter immutable preparation.

For every evaluated node, all operand values are read before writing its result
to `locations[node]`. Reusing a last-used operand's slot is permitted. An
independent reader simulates symbolic slot contents: a read must find exactly
the referenced node, and a write replaces that slot's owner. It checks all nodes,
including unused nodes. It does not rerun the producer's allocation algorithm.

An invariant node directly used by a varying node, or selected as the output,
is persistent across chunks. Its slot cannot be overwritten after definition.
Other invariant temporaries may be reused after their last read. Every varying
dependency precedes its consumer in each chunk, so a previous chunk's value
cannot satisfy a missing current evaluation. After evaluation the root's slot
must still hold the root. These conditions establish the actual schedule; an
unvalidated slot map or lifetime annotation grants no authority.

## Representation and execution

CPU selection may derive a nominal prime-field expression through the canonical
Residue, Arith and [private-tile](../ir/residues.md#private-pointwise-tiles)
readers. The installed prime-field fact and exact modulus are required; a field's
characteristic alone does not justify this representation. Extension and binary
fields retain their complete domain and can use an explicitly selected opaque
provider. Unsupported arithmetic or storage candidates refuse; they do not
silently revert to the original expression.

An installed resident kernel may realize the checked expression under its value
relation. This does not identify Montgomery or extension storage with canonical
word buffers. The actual expression, lane bound and slot assignment in the
physical plan must be used by the reached CPU consumer. A compiler-only MLIR
artifact that is discarded before independently selecting the old call does not
implement this contract. A later AOT target can choose a direct word realization.

A native chunk has at most `lanes` rows. Final short chunks and smaller chunks
under resource pressure preserve pointwise semantics. Actual column lengths are
checked even for unused inputs. The aggregate mode remains the binding's map,
sum or product contract, including its empty-domain result.

## Resources, preparation and outcomes

The runtime numerical Call owns allocation, refusal, release and publication.
The candidate's MemRef allocation is not permission to allocate outside that
owner. Managed resident scratch uses `slots * chunk_rows * sizeof(S)` for the
selected provider element `S`, plus typed operand views, map staging and result
charges. Minimum row workspace uses one element per slot. All arithmetic and
size products are checked. Scratch and staging are fallible and remain charged;
failed execution publishes no successful output and releases private storage.

The word candidate's peak requested storage and the resident provider's bound
are different quantities. Their relation establishes successful values under
sufficient declared capacity; it does not assert identical refusal at every cap,
identical allocator overhead, alignment or process RSS.

Preparation is bounded by the plan carrier, input count and 1 MiB metadata
ceiling. It includes the actual Ring DAG, constants, mask, slot assignment,
dependency classes and copied preparation key. Equal complete bindings,
physical signatures and plan bytes may share a reached call's immutable
preparation; no live values or process-global cache are introduced.

The conservative evaluation-admission score remains
`W = 8B + 2I + 2N + 1 + R(3N + 3)`, with `B` now the complete plan byte length,
`I` the operand count, `N` the node count and `R` the row count. It applies to
cold, cached and empty-domain calls. Bounded preparation still precedes this
per-evaluation admission, as in the numerical contract; the work allowance does
not retroactively gate that preparation.

## Ownership and invalidation

The common mathematical layer owns logical expressions. The CPU target owns
plan proposals and installed realization selection. Independent compiler readers
check the actual word/tile and slot schedule; the checked physical plan retains
an immutable owned payload. Materialization compares actual physical parameters
against that payload and the logical source relation. Mutation requires a fresh
read. The Rust program reader and reached CPU consumer validate the current
physical carrier. No producer hash or persisted approval flag substitutes for
these checks. Lean remains an independent consumer and is not a native gate.

## Bounded compiler work

Physical selection owns a cumulative represented-construction allowance across
all retry attempts. Each lookup costs one unit. A new proposal additionally
costs `(1 + inputs + nodes) * (1 + lanes) * (1 + modulus_bytes)` units; the
modulus term is zero when the complete domain has no integer modulus. The
default is 64 Mi units. These are deterministic size units, not timing claims.
A transaction-local cache uses the exact nominal field, Ring attribute, row
mask and lane bound. Only immutable attributes survive discarded candidates;
no operation pointer or previously successful validation grants admission.
Exhaustion is a terminal `represented-construction-limit` refusal.

Each independent physical-plan validation owns a 16 Mi unit checking allowance
across its occurrences. Each lookup costs one unit. A validation-local cache
reuses only exact immutable field/source/mask/candidate tuples accepted by that
reader; it never consults producer state. Reading a new pair charges the same size
formula with `lanes = 1` for each expression. Exhaustion refuses with
`represented-checking-limit`. Each expression and candidate also retains its
own bounded grammar and word/tile reader limits. Compiler budgets are separate
from reached runtime work, scratch and output-publication accounting.
