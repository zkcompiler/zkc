# F0-V2B2C1B5B2 Exact Terminal Owner Projections

> **State:**
> `Affirmative/F0V2B2C1B5B2-A-EXACT-TERMINAL-OWNER-PROJECTIONS` at bounded
> constructor-isolation resolution
> **Authority:** None. This record and its synthetic profile do not modify the
> target PIR specification or any current artifact identity.
> **Executable evidence:**
> [`evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2`](../../../../evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/README.md)

## 1. Question and result

B5B1 selected a candidate Terminal contract, but deliberately stopped before
claiming that it could inhabit the exact Core body and normalized owner views.
B5B2 asks the stronger construction question:

> Can the selected first-active Terminal contract be made identity-bearing,
> admitted from exact bytes, and projected uniquely into all six owner views,
> while keeping required Check, Reduction, Claim, and public-output
> dependencies explicit?

For the bounded Boolean and Claim/Reduction slice, the answer is affirmative.
The typed owner and an independent byte-derived exhaustive path agree on the
same six exact bodies. Seventeen semantic mutations and six schema-valid but
owner-wrong view substitutions fail to impersonate that result.

This completes the 21/21 B2C constructor-isolation matrix at bounded research
resolution. It does not complete B2D integration or authorize target
publication.

## 2. Ownership decision retained from B5B1

The design keeps the existing owner split:

- Foundation owns portable-term identity, typing, canonical encoding, and
  denotation.
- PIR owns whether an authenticated Foundation term is admissible as the Guard
  establishing a required Terminal Check.
- The Core owns Check, Reduction, Claim, Terminal, and occurrence coordinates.
- The PIR owner-view projector derives graph edges, Claim uses, dispositions,
  and runtime schemas from the admitted Core and paired Protocol.
- Analysis may later qualify a broader implication theorem, but an absent
  theorem cannot become an implicit admission success.

The B5B1 must-fact procedure is a small abstract interpretation: it computes
only facts guaranteed on a Boolean term's true outcomes and joins branches by
intersection. That design follows the sound-abstraction discipline of
[Cousot and Cousot's framework](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml),
but this package supplies differential finite evidence rather than a
mechanized soundness proof.

## 3. Exact candidate body

```text
TerminalDeclCandidate = {
  verdict: TerminalVerdict,
  public_outputs: CanonicalSeq<ValueRef>,
  required_true_checks: CanonicalSortedUniqueSeq<CheckRef>,
  required_applied_reductions:
    CanonicalSortedUniqueSeq<ReductionRef>,
  terminal_claims: CanonicalSortedUniqueSeq<ClaimRef>
}
```

`public_outputs` is ordered because it is an ABI. The other collections denote
sets, so duplicate or noncanonical spellings are rejected.

The old authored sequence of `(ClaimRef, ClaimDisposition)` pairs is removed.
For every Claim in `terminal_claims`, the projection derives:

```text
Accept       -> Consume
Reject|Abort -> Discharge
```

This avoids two identity-bearing spellings for a distinction that has no
defined runtime behavior. A future mixed-disposition need would require a new
semantic role and consumer, not resurrection of an unconstrained tag.

## 4. Profile and schema construction

The test cannot reinterpret the revision-1 Interaction profile. It therefore
constructs a genuine synthetic revision-2 profile using the existing F0-V1
publication topology and adds three reachable definitions:

1. an expanded Terminal body compiler;
2. a Terminal admission law; and
3. a static-view grammar binding.

The schema/profile dependency is made acyclic in two stages:

```text
normalized owner-free grammar
  -> SHA-256 grammar identity
  -> synthetic Interaction revision 2 names that digest
  -> final schema source names the resulting profile ID and body digest
```

The resulting coordinates are:

| Coordinate | Value |
|---|---|
| repaired F0-V1 Interaction digest | `ab74407099935edb863832b357973071b5c5193d16123d811f8289bbbc9be559` |
| candidate Interaction digest | `76cf68774060fbe667ce5f1a7d0b67de525449d8fad92b262c7fd4adfd9b6b79` |
| candidate Interaction body SHA-256 | `4272f9bb8285a84481da961c29cdc058aa7e4ce2411c7f73582a0149933d554d` |
| owner-free grammar SHA-256 | `725ecb1fa099aa7490bc9c1012d4370c0a6a1b183aff6c11d8129f11e464be9a` |
| attached schema-source SHA-256 | `376cefb165ff92f0152856996a96ae02f7e04b9e6c679d01f85e10471c10ca41` |

Both publication compilers agree on all 18 profile bodies and references.
Interaction and 15 transitive dependents rotate; `analysis-kernel` and
`oir-endpoint-graph` remain stable. The schema has 88 definitions, 459 source
nodes, and maximum expanded source depth 17.

These values describe the candidate experiment only. Target migration must
recompute rather than copy them if the authoritative source differs.

## 5. View changes

The schema delta has three operations:

- remove `ClaimDispositionEntry`;
- replace `TerminalEntry` with verdict, ordered outputs, sorted-unique Checks,
  sorted-unique Reductions, sorted-unique Claims, and its occurrence backlink;
- extend `ClaimReductionViewBody` with ordered
  `TerminalReductionRequirementEntry` rows.

The six projections then behave as follows:

| View | Terminal-related owner derivation |
|---|---|
| `PublicBindingView` | unchanged binding and scope meaning |
| `StrategyDecisionView` | unchanged; this slice has no prover decisions |
| `PublicCoinView` | graph edges from required Check outputs, Reduction states, Claims, and public outputs into Terminal effects |
| `EffectView` | exact Check rows and expanded Terminal rows |
| `ClaimReductionView` | Claim uses, verdict-derived dispositions, and explicit Terminal-to-Reduction requirements |
| `ExecutionView` | unchanged static occurrence-output and Terminal result schemas |

No view field becomes a second semantic owner. Each row is a deterministic
projection from an admitted Core or its paired Fresh Protocol.

## 6. Branch-complete exact witness

The witness uses three public Boolean inputs `(q,g,h)`:

```text
0 Check(identity(q)) -> checked_q
1 Reduction0 guarded by checked_q AND g
2 Accept guarded by checked_q AND g
3 Reduction1 always, reached only after Accept was inactive
4 Abort guarded by h
5 Reject always
```

The initial Statement Claim is linear. Reduction 0 and Reduction 1 both consume
it, but first-active guard regions make those uses disjoint. Each reduction
creates one reusable output Claim. The terminals declare exactly the live
output Claim and required Reduction on their paths; Accept additionally
requires Check 0.

The independent execution table is:

| Verdict | Assignments |
|---|---:|
| `Accept` | 2 |
| `Abort` | 3 |
| `Reject` | 3 |

The typed non-enumerating analysis derives one Check entailment, three
Terminal/Reduction requirements, live Claim sets `(1)`, `(2)`, `(2)`, and the
three corresponding derived dispositions. The cold evaluator reaches the same
partition by executing all eight assignments.

## 7. Independent-check design

The cold path is not a second call into the typed owner. It uses separate
Foundation, schema, codec, parser, and graph module instances and never imports
the B5B1 analyzer. Starting from serialized inputs, it:

1. authenticates Core and Protocol body/reference pairs under the candidate
   profile;
2. checks Fresh Protocol-to-Core pairing;
3. decodes all selected Core tables into plain records;
4. authenticates the exact portable-algorithm preimage closure;
5. interprets only the admitted Boolean `Literal`, `Variable`, `Let`, and
   `Conditional` fragment;
6. simulates availability, Check output, Reduction application, linear Claim
   consumption, Claim creation, exact terminal closure, and first-active stop;
7. derives the six owner views independently; and
8. encodes them under its independently compiled candidate schema.

The six paths match byte-for-byte for 32,796 bytes. The graph has 28 nodes and
49 edges. All required Terminal inputs are explicit, while Abort and Reject
have no hidden dependency on the accepting Check.

## 8. Falsification record

The frozen result has 62 findings:

| Outcome | Count |
|---|---:|
| `Affirmative` | 31 |
| `Refused` | 21 |
| `Malformed` | 3 |
| `KindMismatch` | 1 |
| `CannotAnswer` | 6 |

Seventeen freshly authenticated semantic mutations cover invalid Check and
Reduction references, duplicates and ordering, incomplete or wrong terminal
Claim closure, a guarded final fallback, a Guard that does not establish Check
truth, a conditionally unavailable Check, a late Reduction, overlapping
linear consumers, Check ABI drift, Claim-output aliasing, and Terminal backlink
loss or duplication. Both paths reject every mutation.

Six owner-view substitutions remain values of the structural schema but differ
from the owner's exact body. They remove or alter a required Check, Reduction,
Claim, disposition, requirement row, or graph edge. This is the intended
distinction between grammar validity and owner-derived truth.

Additional controls reject an old authored-disposition row, mismatched Core
body/reference, cross-Core Protocol, truncated Core bytes, missing or
substituted algorithm preimages, and foreign process-local authority.

## 9. Design consequence

B5B2 supports carrying the B5B1 selection into the main semantic design. The
minimum coherent target change is not a new subsystem. It is one coordinated
owner migration:

1. revise the Interaction-owned Terminal body and admission law;
2. revise the Interaction-owned normalized view grammar;
3. rotate the exact transitive profile cone;
4. migrate Core producers and consumers directionally; and
5. re-establish live implementation correspondence after publication.

Before that migration, B2D should combine all constructor families into an
integrated Core and attack cross-family graph, ordering, authority, and
mutation interactions. B2D can still reopen this selection if integration
reveals an omitted owner coordinate.

## 10. Nonclaims and next gate

This package establishes finite construction and falsification evidence. It
does not establish a refinement theorem, abstract-interpreter proof, reduction
theorem, protocol soundness theorem, Fiat--Shamir theorem, hash/sponge
assumption, QROM result, compiler preservation proof, backend correctness, or
deployed verifier validity.

It also does not establish target publication, live implementation
correspondence, or F1 Q1. Those outcomes remain `CannotAnswer`, not inferred
successes.

The next research gate is F0-V2B2D integrated graph and mutation closure.
F0-V2C target migration remains downstream of that gate.
