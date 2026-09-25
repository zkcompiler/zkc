# Authenticated finite tables

A vector commitment authenticates coordinates of an ordered finite table. It
does not assert polynomial degree, relation satisfaction, an extraction theorem
or hiding. A protocol can use this domain without using AIR, FRI or polynomials.

## Contract

`VectorCommitment(C)` associates a nominal scheme `C` with `C.ValueField`.
The table is a flat, row-major field vector with positive width and height.
This capability is separate from `MultilinearOpening`.

| Operation | Meaning |
|---|---|
| `oracle.commit<C>(values,width)` | Commit one rectangular table; return public root and private immutable opening state |
| `oracle.open<C>(state,index)` | Return the complete selected row and ordered authentication path |
| `oracle.check<C>(root,width,height,index,row,path)` | Check exactly the caller's expected shape and coordinate; return Boolean |
| `commitments.empty/append/at/length<C>` | Persistent public root sequence, with checked lookup |
| `opening_states.empty/append/at/length<C>` | Persistent private state sequence, with checked lookup |

Indices are checked unsigned naturals, not field elements. The verifier supplies
the expected shape; a received path cannot choose it. The Boolean is not an
implicit acceptance: the authored verifier must consume it in a guard or expose
it through an explicitly selected caller acceptance result. A public
root cannot manufacture private opening state. Opening states and their
collections have no public wire decoder or transcript codec.

Publication occurrence and interaction order belong to source execution. A
received root or row is a distinct adversarial value, even when source analysis
identifies its authored sender. Repeated coordinates remain repeated logical
queries; an encoding optimization must preserve rejection of inconsistent
responses before it can share authentication work.

## Installed binary Merkle schemes

The installed schemes are `rows.merkle-keccak256.koala-bear/1` and
`rows.merkle-keccak256.koala-bear.ext8-binomial3/1`. Both use Plonky3 0.5.1's
binary single-root tree with Keccak-256, one rectangular matrix and cap height
zero. Leaf hashing binds a versioned leaf tag, field/basis codec, width, height
and canonical coordinates. Node hashing uses a distinct tag and two 32-byte
digests. Missing bottom-layer leaves use upstream zero-digest padding.

Non-power-of-two heights are allowed. Checking requires exact row width,
`index < height` and path length `ceil(log2(height))` before upstream hashing.
Shape, byte and element limits apply before allocation. Authentication failure
returns false; malformed shapes and resource exhaustion refuse execution.
These schemes are nonhiding and do not require an external setup key. Setup
policy is selected by nominal scheme, never by the words `commitment` or `proof`
alone. The [wire format](../../compiler/artifact-format.md) fixes public codecs.

## Source analysis and construction

`oracle-inspect SOURCE ENTRY` recovers roots, shape operands, coordinates,
received rows/paths, authentication guards and authored opening/publication
provenance. It uses the same finite source expansion as claim analysis. Ordinals
are execution order, not lexicographic path order. Checked constant evaluation
and exact index-expression congruence can link coordinates through loops and
index collections. Authored coordinate correspondence may cross messages, but
local sampled-value dependencies and constant facts stop at every receive.
Constant-index lookup resolves only locally constructed root/state collections;
a relayed root list cannot inherit the sender's element identities or the earlier
roots' reception times. Individual received roots retain their actual reception.
The `zkc.oracle-access/2` report separates may-dependence from exact identity:

- `coordinate_receptions` records direct received inputs, including a sampled
  index's bound. `coordinate_draws` records contributing sample occurrences.
- `coordinate_provider_history` retains received inputs that pass through a
  provider, rather than treating them as directly selected coordinates.
- `coordinate_unknowns` retains unclassified operation dependencies.
- `coordinate_sample`, when present, identifies an exact sample result;
  `sample_bound_matches_height` requires a bounded-index sample whose bound and
  the check's height are the same local value, allowing only resolved local
  collection aliases. Separate equal constants or receptions do not establish
  this identity. May-dependence alone grants neither fact.
- `publication_bound_draws` lists derived draws whose actual provider chain
  observes the exact checked root value at the checking role. This fact is
  recorded even for a local root; the publication policy separately requires a
  received root and an authored publication. Observing a derived statistic,
  observing a list containing the root, observing the root after the draw, or
  observing it on another provider chain does not establish this fact. Separate
  receptions remain separate even when the authored sender supplies one root.

None of these links equates an adversarial message with its authored sender's
value or establishes a sampler distribution, entropy or injective encoding.

`oracle-check SOURCE ENTRY` accepts three independent, optional policies:

| Option | Required evidence |
|---|---|
| `--publication-before-queries` | An authored publication and a root reception; every draw contributing to a checked coordinate follows that reception. Each contributing transcript draw additionally absorbs the exact checked root before sampling. Direct received coordinate inputs are refused. |
| `--queries-before-responses` | Every bounded-index draw precedes every recognized opening response across the selected execution, retaining duplicates. |
| `--sampled-queries` | Each checked coordinate is the exact output of a bounded-index sampler, and its bound is the same local value as the check's height. |

The publication policy checks contributing draws, not whether the coordinate
itself is sampled. It permits locally derived coordinates, including reduction
modulo 1, and constants (which have no contributing draw), when its other
requirements hold. It therefore does not silently impose the stronger exact
sample policy. A draw with bound 1 and an unrelated height also passes ordering;
`--sampled-queries` refuses it with `oracle-query-bound-unresolved`. If that same
bound 1 is the check's height, the exact sample policy passes. A coordinate
derived from a sample, a constant or a reception instead produces
`oracle-query-not-exact-sample`. These are structural facts, not a claim of
uniformity, entropy, independence or cryptographic query quality. The sample
policy alone does not require publication or response ordering.

An early private draw disclosed later is not thereby an insecure interactive
protocol. For transcript draws, source ordering alone cannot establish exact
root absorption. Directly received coordinate inputs produce
`oracle-query-coordinate-received` under the publication policy; received inputs
absorbed into provider history are retained separately. A received bound remains
a direct input even when it is also the exact height operand.

Valid admitted sources can lack evidence under these policies. In particular,
refusal of whole-list absorption or separate equal constants means the installed
analysis cannot establish the required fact; it is not a claim that the source
is malformed or that the values differ. Unsupported provider transfer is also
unknown coverage: RNG and transcript transfers use installed contracts; the
current `curve.commit`, `curve.response`, `group.commit` and `group.response`
nonce consumers have no sampling transfer contract. Each selected policy
reports `oracle-unsupported-provenance` for these occurrences. No nonce sampling
law is inferred from their signatures.

`--accept-result=N` is an explicit caller contract: the selected entry Boolean
must be true for acceptance. **N is zero-based across all entry result ports,
including other roles.** For outputs `(P bool, V bool)`, 0 selects P and 1 selects
V. In contrast, a construction descriptor's `accept N` counts only validator
ports, so `accept 0` selects V in that example. The report's `acceptance_result`
records the requested index and `acceptance_role` records the selected value's
owner when available. An absent or non-Boolean result produces
`oracle-acceptance-result`. The two selectors retain their separate meanings.

Only that result and its same-role conjuncts count as acceptance sinks.
Ordinary Boolean returns do not. A successful `require`
also entails its conjuncts; disjunction, negation and strict selection do not
unconditionally entail their operands. This reasoning concerns completing or
caller-accepted runs, not use-before-check or every intermediate execution state.
A Boolean received by V from P has reported owner V but supplies no entailment
of V's earlier authentication check.

These optional policies cover the selected execution, including its child calls.
Consequently, `--queries-before-responses` refuses a sequence of two separately
queried oracle arguments if the second draws after the first answers. Applying
that global policy is a choice; rejection does not establish that sequential
composition is insecure. A component-local phase contract needs an explicit
scope and composition premises. The installed checker does not invent them.

The allocated findings are `oracle-check-unguarded`,
`oracle-opening-coordinate-unresolved`, `oracle-query-before-publication`,
`oracle-publication-unresolved`, `oracle-query-after-response`,
`oracle-query-coordinate-received`, `oracle-response-unauthenticated` and
`oracle-analysis-limit`, together with `oracle-query-publication-unabsorbed`,
`oracle-unsupported-provenance`, `oracle-sampler-signature`,
`oracle-observation-signature`, `oracle-check-signature`,
`oracle-acceptance-result`, `oracle-query-not-exact-sample`,
`oracle-query-bound-unresolved` and `oracle-execution-invalid`.
The public execution-view API checks order coverage, ordinals, uniqueness of
produced SSA names, forward/cyclic producer references and the port arities it
consumes. Malformed
synthetic executions produce findings rather than indexing absent ports or
operations; these defensive checks do not replace source admission.
One work budget covers structural checks, both analysis passes, provenance
copies and history traversal. Observations share immutable parent links instead
of copying history prefixes. Exhaustion stops analysis immediately and emits
`oracle-analysis-limit`; any returned access list is then partial and cannot be
used as complete policy evidence. C++ callers can supply a smaller `workLimit`
to `analyzeOracleAccess`; the CLI uses the default of 1,000,000 work units.
`oracle-inspect` prints findings with a successful exit status, while
`oracle-check` exits unsuccessfully if any finding is present.

An empty finding list establishes only these installed dataflow checks.
Recognized received opening rows/paths must be operands of a
locally guarded authentication check; a response with no such consumer is
reported even when the source contains no `oracle.check` operation. Recognition
currently follows direct authored `oracle.open` results and message provenance.
It does not recover a row transformed by an arbitrary local operation, and a
relayed opening result remains a recognized response. Extending that coverage
requires an explicit operation contract, not recognition by protocol name.
The view records shape operands, not a proof that a publication's table shape
equals a check's expected shape. Field-challenge ordering (for example beta or
a FRI fold challenge) still requires an explicit protocol-specific audit; these
index-query policies do not establish it. It does not prove parameter
independence, state-restoration soundness, Merkle extraction, FRI proximity or
Fiat–Shamir security.

Analysis of actual constructed output retains these boundaries. The admitted
normal, early-query and late-query controls construct and compile, but their
producer and validator transcript draws are distinct occurrences. All retain
`oracle-opening-coordinate-unresolved`; independent transcript states are not
equated to remove that finding. The early-query output additionally lacks exact
root absorption and precedes publication under the publication policy. The
late-query output additionally fails the response-order policy. Construction
success does not discharge these separate oracle policies.

Source-authored commitment/authentication plus a selected transcript construction
is the implemented route. Automatic elaboration from an arbitrary ideal-oracle
IOP and a BCS security theorem remain separate work.
