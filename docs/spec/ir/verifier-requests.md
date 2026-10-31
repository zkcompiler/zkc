# Deterministic verifier requests

This is the native construction contract for removing deterministic
verifier-to-prover transport after checked oracle realization. Implementation
coverage is tracked in [status](../../status.md). This contract does not supply
Fiat–Shamir soundness, commitment binding, FRI proximity, or a formal
realization theorem.

## One construction boundary

The compilation chain is original protocol, admitted preparation, checked oracle
realization, ordinary participant projection, and selected transcript
construction. Preparation retains the original subject and construction
application markers. Realization consumes the explicit oracle policy and checks
its actual common body. Projection retains ordinary sends and receives.
Construction removes selected challenge deliveries and admitted deterministic
requests. There is no proof-specific oracle realizer or alternative FRI source.

The checked compilation owner retains the realization edge. Source-relative
reconstruction facts are private facts about the actual modules. An inspection
clone, serialized record or digest cannot manufacture this checked owner.
Logical claims remain relative to their original subject; executable
correspondence alone cannot publish a stronger logical-oracle claim.

## Value relation and causal order

At a removed request, the validator observes its original computed value and
the producer observes the exact value replacing its receive. The two values
must have the same nominal logical meaning and canonical message encoding on
corresponding continuing prefixes. Equality of types, lengths, roots, role
availability or generated names is insufficient.

The native checker admits a finite relation over actual SSA values:

- Equal constants and exact mathematical operations on related inputs.
- Original data ports present at both roles and checked by the Host against
  the same canonical public binding. A verifier-only public port is not a
  producer operand.
- The exact producer send operand corresponding to a validator receive at the
  same occurrence and iteration. Publishing a function of a secret does not
  publish that secret.
- The already constructed sample of the matched selected challenge, with the
  same invocation, observations, coordinates and transition parameters.
- Calls to the same admitted deterministic Local closure on related data.
- Explicit loop invariants for carried values, captures and induction
  coordinates, including zero iterations and exact initial/yield positions.

Dependencies must be available at the corresponding event frontier. A later
response cannot justify the request that causes it. Deduplication identifies
the same source occurrence and lexical frame, never equal-looking values from
different applications or iterations. Request grouping retains constructor and
instance identity, first-use order and every logical occurrence.

Receiver stores are reproduced from their actual initializer and append
operations. Holder records, which may contain private table and opening data,
are not substitutes for receiver records. Replica state remains private
implementation data, outside original ports, results and proof frames.

## Deterministic calls and outcomes

An installed deterministic-data interpretation states that equal complete
logical inputs produce equal normal results or the same logical stop. It does
not grant totality, speculative execution, equal resource exhaustion, sampling
uniformity, or cryptographic security. Unknown or unclassified implementations
do not receive this interpretation.

The checker inspects the entire transitive Local execution closure, including
scoped control, branches, loops, captures and all outcome paths. It refuses
opaque/external behavior, private services, unselected randomness, hidden
transcript state and mutable or affine data. Each replica uses its own caller's
administrative scope; scope tokens and outcomes are not copied as ordinary
data. Partial deterministic operations retain their refusal behavior.

Reconstruction reproduces complete needed calls. Checked oracle realization
separates demand-only request collection from the verifier's zero-result
availability check. The collector takes only demand state and stores; the
distinct check takes its actual request result, original evaluator state and
the same stores. Before grouping or exchange, an empty prefix runs the original
ordered finishes and impossible-empty refusal; a nonempty prefix has no effect.
Both helper bodies and the actual common call order and operands are checked
under the [query-batch contract](../formats/oracle-realization.md#checked-query-batches).
The verifier retains the complete check. It supplies no producer request data,
so it introduces no evaluator dependency solely for request reconstruction.
This refinement changes generated Local boundaries; it does not prune stopping
instructions from an existing partial deterministic call.

The original validator's calls, guards, authentication, replay and acceptance
stay in order. Extra producer work is charged and may stop or exhaust earlier.
The judgment preserves validator behavior and relates continuing prefixes; it
is not raw trace or budget equivalence. Honest producer coverage additionally
requires admitted deterministic implementations, matching transport and
sufficient execution budgets. An always-stopping candidate does not satisfy
that coverage obligation.

## Loop-count correspondence

Every loop shared by both proof roles requires agreement of actual counts as
well as maxima, including a loop with no message or query. This retains the
original joint count-admission condition before any body entry. A loop owned
by only one participant does not introduce a cross-participant count premise.
The condition also applies to an identity construction: preserving both
participant bodies does not preserve a count check formerly owned by the
joint driver. Selection, construction and the independent actual-body reader
each enforce the same count premise.
Ordinary structural congruence uses the value relation above. Oracle request
loops additionally use the checked structural recurrence:

```text
leaves(base instance) = 1
leaves(virtual instance) = sum(leaves(child) for each declared query occurrence)
rounds(block) = ceil(sum(leaves(root) for each logical root occurrence) / capacity)
```

Repeated edges remain repeated summands; a virtual with no queries contributes
zero. The realization reader checks actual allocation order, source edges,
lookup operands, stored counts, overflow bounds and ceiling division. Shapes
and capture values are not inputs to this count recurrence. Their separate
request and domain obligations remain mandatory.

Construction may use the reproduced receiver count for the producer loop only
after checking its equality to the original holder count. It retains the
original count calculation and possible stop. Private holder records do not
become public merely to satisfy dependency analysis. Equal maxima or a new
runtime equality guard cannot replace this source-relative count check.

## Observations and executable admission

Each reconstructed request retains its original message observation on both
roles, including messages after the final challenge. It produces no proof
frame and no new challenge transition. Selected challenge deliveries remain a
different event class with exact query/delivery pairing. Construction-owned
gate witnesses retain their own transport and are not message observations.

The descriptor event vocabulary adds `['reconstructed-message', origin_hex]`,
using the existing native message-origin grammar. Ordinary message rows still
retain the exact logical payload and codec. The descriptor also retains one
canonical normalized oracle-selection JSON string after the witness inventory;
its roots are an exact source-ordered inventory. This gives nine descriptor
fields. The deployment remains nine fields and the program carrier is
unchanged. All tags remain version 0. Producers, readers and fixtures migrate
together; the former descriptor arity is not an alternate accepted form.

Generated realization events use the existing message-origin grammar with a
reserved protocol name `zkc.oracle.<digest>`, where `<digest>` is 64 lowercase
hexadecimal SHA-256 digits. Authored protocol names cannot use this namespace
in native proof construction. The compiler derives the digest from compact
canonical JSON with this array shape:

```text
["zkc.oracle-native-occurrence/0", entry, purpose, role,
 normalized_selection_json, source_association,
 ordered_query_associations, packet_capacity_or_null]
```

A source association is `[entry, path, operation, lineage]`. The path contains
canonical decimal strings indexing operations through the prepared source's
single-block repeats. Lineage is `[authored_steps, authored_event]`, including
original application and repeat frames; an oracle event is internally named
`["oracle", authored_protocol, authored_site]`. A generated message requires its
actual source oracle send or query and the corresponding authored lineage.
Administrative local-only operations without an authored site may have null
lineage. A query block includes every ordered query association, including
repeated occurrences, and its actual packet capacity. Other events use an empty
query list and null capacity. These are digest-preimage rules, not an additional
published certificate format.

The origin's event site is the actual, already expanded common site. Its path
retains full authored application/repeat prefixes and any generated repeat
frames so generated and authored events identify the same enclosing loop.
Readers therefore do not apply application-site prefixes a second time for
this reserved namespace. Ordinary authored origins retain the existing site
expansion rule. Generated helpers do not establish provenance: the immutable
realization owner and its actual-body checker establish each association.
The compiler checks complete event coverage and rejects duplicate origins.
This namespace does not assert that an authored declaration has that name.

The initial native proof profile keeps original deployment ports free of logical
oracle handles and sequences, including handles nested in records. Oracle
construction inside the entry and its applications is supported through the
checked realization. Importing external oracle graphs requires a separate Host
contract; an executable representation is not silently substituted for a
logical public input or result.

Runtime admission checks the executable endpoint it actually receives: the
complete event/state chain, helper arguments, payload association, coordinates,
ordinary dependency restrictions and exact surviving transport. It does not
prove equality with an absent participant or correspondence to absent source.
The authenticated native compilation and its independent source/candidate
checker own those judgments. No persisted SSA replay-certificate language is
introduced.

The actual-body checker maintains distinct ordinary and replica value maps,
checks every inserted call and loop slot, and rejects unused or unexplained
work. It does not call the emitter. Whole-candidate regeneration comparison is
an additional control, not a substitute for this reader. Tests must exercise
the reader directly with mutated actual operands, calls, counts, yields,
observations and scope/outcome edges.
