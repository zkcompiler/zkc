# Binary FRI

The [library](lib.zkc) has one logical `Commit` and one private query checker.
`Query`, `QueryAssociated`, `ScalarLowDegree` and `BlockLowDegree` use that checker. FRI has no commitment
parameter, Merkle state, roots, paths, pair layout or automatic realization
selection. A deployment must select and check its oracle realization.

The compiler realizes these handles before participant projection. NativeProof
then reconstructs deterministic verifier requests from the checked public
inputs, transcript draws and already published values. Both participants absorb
those requests at their original occurrences; only their transport is omitted.
The verifier still authenticates each response before using its answers. See
[verifier request reconstruction](../../../../docs/spec/ir/verifier-requests.md).

## Public API

Every protocol below has roles `(P,V)`. Commitment static arguments are
`<C, LogSize, TerminalLog, Rounds>`; query state adds `Queries`. Samplers use
`<F, LogSize, Queries>` and have no commitment configuration.

| Export | Contract |
|---|---|
| `Configuration` | `Value: Field`, `Challenge: Field`, ordinary `challenge(draw) -> Value effects(stop)`; no commitment members |
| `Direct<F>` | Value and challenge field `F`, identity conversion |
| `FieldTable<F>`, `Oracle<K>` | Explicit installed logical table and handle aliases |
| `CommitmentState<C,...>`, `QueryState<C,...>` | Distinct types with private fields and library construction; direct custody `@P->V` |
| `Commit` | Takes the word at P, a shift component at each role, shared runtime round count and `Random<C::Challenge>` at V; returns commitment state after checking terminal coefficients |
| `ScalarQueries` | Samples an ordered sequence of scalar index requests, delivering each result unchanged |
| `BlockQueries` | Samples one product block and delivers it unchanged; requires `IndexBlockRandomness` |
| `BindQueries` | Checks a supplied role-paired sequence's exact count and every position's bound at both roles, then returns query state with the original handles and geometry |
| `Positions` | Returns the state's exact positions with components at P and V |
| `Initial` | Returns the state's exact initial handle with its retained row bound |
| `Query` | Returns acceptance and authenticated first-layer values in position order |
| `QueryAssociated` | Takes expected first values at V; queries the same state's initial handle at its positions and checks equality before each fold chain |
| `ScalarLowDegree`, `BlockLowDegree` | Select the named sampler between `Commit` and `BindQueries`, then call the same `Query`; return `(accepted, positionsP, positionsV, valuesV)` |
| `power_word`, `fold_value` | Total mathematical helpers; neither authenticates data nor establishes domain membership |

Commitment state owns bounded sequences of actual layer handles and virtual
fold handles, the initial handle, exact coset geometry, terminal coefficients
and the round count. Query state adds the checked positions and query count. Converted challenges live in
their exact fold captures; a second unused challenge vector is not retained. Every
logical field retains a per-element `rows` bound and the same oriented family.
There is no nested logical record. Ordinary metadata has components throughout
that family. Role assembly preserves those components; it does not assert that
they are equal. Private construction prevents accidental mixing of independently
obtained components; privacy is not a security proof or an ingress theorem.

## Domain, degree and schedule

The supported profile is `1 <= Rounds`, `1 <= Queries`,
`TerminalLog + Rounds + 1 <= LogSize`, and `LogSize <= 63`. Runtime counts must
equal their static parameters at both roles. All zero-round profiles refuse;
bounded traversal does not implement an arbitrary variable-round API.

The initial word has exactly `2^LogSize` values. The degree target is strictly
below `2^(TerminalLog+Rounds)`, with terminal degree strictly below
`2^TerminalLog`. Values are in natural coset order `shift * g_n^i`. Checked
coset setup retains the installed two-adic bound and nonzero shift. Each round
checks the installed generator against the previous generator squared. The
virtual predicate retains a positive binary source size, exact source and
result sizes, generator order, and inverse equations for the shift, generator
and two. `CharacteristicNotTwo` is an explicit field requirement. The prover
continues to use the existing checked `coset::fold` implementation.

For each actual source, Commit sends its oracle before drawing and exchanging
its challenge. It constructs a virtual fold from that actual handle and those
challenge components, then folds the prover word. The final polynomial follows
the last round. `Commit` performs no index sampling. The selected sampler runs
after `Commit` and before `BindQueries`; every query draw precedes every opening. Query acceptance is
returned only after all chain equalities and terminal evaluations succeed.

The terminal encoding is exactly `2^TerminalLog` coefficients, zero padded
only after checking that interpolation produced at most that many coefficients.
The verifier checks exact length before sampling queries.
An oversized honest interpolation stops at the prover's padding guard
before a terminal message is sent. This is also relevant to adversarial tests
that distinguish producer refusal from verifier rejection.

The two samplers are explicit laws, with no capability fallback. Scalar sampling
uses a bounded loop of scalar requests; block sampling uses one ordered product
request. The selected native transcript must support that method. Duplicates and
position order are preserved. `BindQueries` checks shape and bounds, not sampling
uniformity: a caller-supplied sequence needs its own distribution justification.

Joint challenge/query distribution (including conversion pushforward laws),
the selected gap/proximity relation, authentication security and Fiat-Shamir
security remain mathematical premises or separate obligations. Execution and
interface membership do not establish them.

## Virtual fold

The private `Fold` definition captures the source handle, beta, `source_rows`,
result rows, shift, generator and prepared inverses. Commit reads `source_rows`
from `oracle.rows(source)` before construction. Its admissibility clauses bind
that capture back to the same actual anchor and bind result rows to half of it.
The result-shape capture never becomes independent size authority.

For every unsigned 64-bit query word, it computes
`low = i & wrapping_sub(source_rows >> 1, 1)` and
`high = wrapping_add(low, source_rows >> 1)`, queries low then high, and uses
`inverse_shift * power_word(inverse_generator, low)` in `fold_value`. These
maps are total even for inadmissible captures; actual domain checks remain
ordered query obligations. `power_word` uses `finite_math::fold` over the exponent's significant bits
(at most 64), carrying `(result, factor, remaining)`. Six total word steps
compute that bit width; exponent zero returns one from an empty fold. Low-bit
and logical-shift operations are total. The query suite contains no source data/shape reads, checked
Local calls or materialized virtual table.

The checker first queries the initial handle at the selected position. In
association mode it immediately compares that authenticated answer with the
supplied DEEP value. Each later actual layer answer is compared with the
preceding virtual-fold answer; the last fold is compared with the terminal
polynomial. Round zero's fold is explicit, followed by a uniform loop over the
remaining rounds. Optional association is a verifier-local predicate, so it does
not create a conditional communication schedule. Both source siblings remain
logical queries. Physical sharing or
sibling omission needs its own checked reconstruction and authentication.
Existing pruned multi-openings and dynamic query packets have different costs;
this migration claims no preserved proof size or throughput.

## Migrated callers and exact examples

| Source | Shared API and preserved outer schedule |
|---|---|
| `examples/projects/fri/main.zkc` | `ScalarLowDegree<Direct<E>,5,0,3,8>`; the source no longer selects a row commitment |
| `libraries/arguments/stark/single_table/lib.zkc` | `Commit<FriConfiguration<K>,LogFinal+Rounds+LogBlowup,LogFinal,Rounds>`, explicit scalar or block queries and binding, then trace/quotient openings and degree-adjusted DEEP values, then `QueryAssociated` |
| `libraries/arguments/stark/single_table/low_degree.zkc` | Only `FriConfiguration<K>`: `Value = K::Extension`, `Challenge = K::Challenge`, `challenge = K::challenge`; no specialized Commit/Open remains |
| `libraries/arguments/stark/single_table/koala_bear_octic/lib.zkc` | `ScalarLowDegree<Direct<Extension>,LogSize,0,LogHeight,Queries>` before trace/quotient openings and the existing DEEP equality |
| `libraries/arguments/stark/whole_bundle/lib.zkc` | `ScalarLowDegree<Direct<Extension>,LogSize,0,MaxLogHeight,Queries>` before base/auxiliary/quotient openings and the existing DEEP equality |

The outer application signatures remain:
`examples/projects/fibonacci/main.zkc` keeps `TableArgument<0,B,3,5,8,8>`;
`examples/projects/femtocairo/main.zkc` keeps
`ThreeTableArgument<Execution,LogUp<Extension>,5,7,8,8>`;
`examples/projects/stark/main.zkc` keeps
`ScalarTableArgument<Poseidon2,0,B,LogFinal=0,Rounds=3,LogBlowup=2,Queries=8>`.
The quartic configuration's octic challenge conversion is preserved explicitly.
FRI retains no direct physical commitment dependency. All maintained callers
select their query policy explicitly; no `LowDegree` compatibility alias remains.
