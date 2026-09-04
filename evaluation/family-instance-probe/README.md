# Family and instance probe

## Exact question

For two finite protocol-family shapes already representable by the retained
indexed authoring instrument, does changing a family parameter produce regular,
separately admitted concrete Core instances and distinct Core identities, and
does that evidence support keeping family parameterization outside the PIR Core
while Analysis binds one family theorem to each member through an exact
pointwise correspondence?

The frozen aggregate answer is
`Affirmative/FAMILYINSTANCE-A-INSTANCES-OUTSIDE-CORE`. This is a bounded design
recommendation. It is not target adoption.

Run the gate from the repository root:

```bash
python3 -B evaluation/family-instance-probe/run.py --check
```

Use `--json` to retain each run's measured admission medians as well as the
frozen findings.

## Reused authority and method

The probe imports
[`indexed-core-elaboration/reference_model.py`](../indexed-core-elaboration/reference_model.py).
That instrument owns one finite `Static`/`Repeat` authoring grammar, unfolds a
selected index, delegates the result to the unchanged finite Core admission
routine in
the [finite Protocol reference model](../k2-protocol-fiat-shamir/reference_model.py),
and authenticates the resulting Core identity. This package adds no Core
constructor, profile, or admission path.

The selected fibers are:

- FRI-like folding with one query and fold counts `2`, `3`, and `4`;
- sumcheck-like interaction with variable/round counts `1`, `2`, and `4`.

For each fiber the runner:

1. runs the retained schema/index checker and obtains its admitted concrete
   Core;
2. records canonical Core body bytes and the compact
   `subject-kind@content-digest` coordinate of the typed Core identity;
3. times 21 warm calls to the unchanged bare Core admission routine and records
   the median;
4. constructs every node and edge representable by the simplified fixture's
   input, scope, occurrence, claim, reduction, and terminal coordinates;
5. compares declarations by semantic name and canonical declaration value;
6. checks which top-level Core body fields changed; and
7. fits exact integral affine laws to body bytes, fixture-graph nodes and
   edges, and declaration count over the three measured members.

The exact body, identity, graph, declaration, source-digest, and affine-law
observations are frozen in `expected-findings.json`. Wall time is inherently
host-dependent: every run reports each median, while the frozen finding for
each member is the explicit `<= 250,000,000 ns` class. Exceeding that ceiling
fails the gate.

The source digest now pins the protocol model after its owner-profile compiler
dispatch repair. Source-authority IDs in that model changed because their
preimages now use tagged owner equations. This probe derives only Core IDs;
those bodies contain no source-authority envelope, so all six frozen Core
identities and affine observations remain unchanged.

## Frozen observations

The following medians are one authoring run, not immutable values. The frozen
performance coordinate is the ceiling class described above.

| Family shape | Parameter | Body bytes | Core identity digest | Admission median | Fixture graph nodes | Fixture graph edges | Declarations | Changed from prior |
|---|---:|---:|---|---:|---:|---:|---:|---:|
| FRI-like folding | folds `2` | 7,625 | `8c158862bb8e...38d0c` | 133,673 ns | 42 | 58 | 19 | 0 |
| FRI-like folding | folds `3` | 8,815 | `298ea61f2db1...9be61` | 148,674 ns | 48 | 67 | 21 | 5 |
| FRI-like folding | folds `4` | 10,005 | `332a7b9cb17f...3f269` | 168,355 ns | 54 | 76 | 23 | 5 |
| Sumcheck-like rounds | variables `1` | 4,190 | `aef62014b432...3cfef` | 76,062 ns | 24 | 31 | 12 | 0 |
| Sumcheck-like rounds | variables `2` | 7,003 | `7820272d0c8d...0c9c7` | 122,913 ns | 35 | 51 | 17 | 6 |
| Sumcheck-like rounds | variables `4` | 12,629 | `79ed21123a33...ffffd` | 208,206 ns | 57 | 91 | 27 | 11 |

All six compact identity coordinates have the subject kind
`pir.interactive-core`; the complete fixed profile, regime, identity-profile,
and hash-suite preimages remain authenticated by the imported Core identity
routine and are pinned through the imported source digest.

For fold count `r`, the measured laws are:

```text
Core body bytes          = 5,245 + 1,190 r
fixture graph nodes      =    30 +     6 r
fixture graph edges      =    40 +     9 r
declarations             =    15 +     2 r
```

Between adjacent measured fold counts, only `schedule` and `reductions` vary.
One extra fold adds a challenge and an Oracle publication; it also changes the
reduction's challenge/publication lists and the query/answer declarations'
selected layer. Those five declaration additions or changes explain the
consecutive difference count.

For variable count `v`, the measured laws are:

```text
Core body bytes          = 1,377 + 2,813 v
fixture graph nodes      =    13 +    11 v
fixture graph edges      =    11 +    20 v
declarations             =     7 +     5 v
```

Only `schedule`, `reductions`, and `claim_uses` vary. Each added variable adds
one prover message, one challenge, one check, one reduction, and one reduction
claim use. The terminal claim use also changes, so the declaration difference
between members with gap `delta` is `5 * delta + 1`.

These are exact regularities only over the named finite, one-digit parameter
domain. They do not establish the same formulas after identifier-width or
canonical-natural-width boundaries, and they are not an all-index induction.

## Graph boundary

The graph counts are affirmative only for the graph fully representable by the
reused finite fixture. The adapter uses the Section 11 node categories for public
or private inputs, scope openings, binding observations, occurrence activity,
effects and outputs, claims, reductions, and terminal decisions. It uses the
fixture's declared dependency, Oracle, claim-use, and reduction coordinates.

The reused fixture README states that its public-coin check is not the durable
complete `PCNode`/module graph, that its reductions are schedule-anchored rather
than first-class effects, and that initial claim identifiers carry no theorem
meaning. Therefore exact target `PCGraph` equivalence and exact target node and
edge counts are
`CannotAnswer/FAMILYINSTANCE-C-TARGET-PCGRAPH`. The missing evidence is six
instances admitted by the target Appendix-A carrier followed by the target
Section 11 graph constructor, or a checked correspondence from this fixture
projection to those target graphs. The probe never turns that absence into an
affirmative.

## Theorem-binding model

The runner freezes the coordinate categories for the family theorem

```text
for every variable count v, degree bound d, and finite field F,
soundness error <= d * v / |F|
```

without asserting that theorem. The single family applicability record binds
the theorem schema, family definition, family read manifests and experiment
profiles, source/target roles, parameter substitution, side conditions, typed
bound transform, hypothesis context, support, and validation basis. Each
concrete member then needs its family definition, logical `v` literal, exact
Core and Protocol identities, relation instance and binding identities,
statement/witness/challenge coordinates, equalities fixing round count, degree
bound and field cardinality, and one family/member correspondence judgment.

All three compared designs can reuse the same theorem source because Analysis
already separates theorem-source validation, family applicability, pointwise
correspondence, and member specialization. The instances-only design requires
only the latter pointwise evidence at each Core. An internal template adds
template admission, total bounded unfolding, and per-member unfolding equality.
A family semantic profile adds profile publication, a parameter-fixing import,
and per-member unfolding equality. Neither added route removes concrete Core
admission or pointwise correspondence.

## What a pass establishes

A pass establishes, for exactly the six selected fibers and frozen imported
sources:

- successful unchanged finite Core admission and authentication;
- distinct Core identities after every selected parameter change;
- exact frozen body, identity, declaration, and fixture-graph observations;
- a reported median bare-admission time in the frozen ceiling class for every
  member;
- integral affine variation of four measured size coordinates on each selected
  finite domain;
- refusal of an adjacent member's identity as the current member's identity;
  and
- a structurally complete coordinate ledger in which one theorem source is
  reused and each concrete member supplies separate correspondence evidence.

## What a pass does not establish

A pass does not prove the sumcheck theorem, FRI soundness, any soundness or
security property, family-wide correctness of the generator, target Core or
target `PCGraph` correspondence, implementation conformance, admission
complexity, endpoint correctness, or asymptotic behavior. It does not admit an
internal template or family profile, publish a profile, change an owner page,
adopt a design, or authorize downstream use. The measured FRI-like and
sumcheck-like Cores are shape witnesses, not paper-algorithm correspondences.
