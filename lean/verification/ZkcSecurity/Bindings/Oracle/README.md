# Positional permutation adapter

`Permutation.lean` realizes a virtual table through the existing
`Commitment.CommittedOp.read` descriptor. For a permutation `π`, its logical
word is `word ∘ π`; reading index `i` makes exactly one positional read at the
original handle and position `π i`. Executable access takes no reference word.

The reusable mathematics in `Families/Proximity/Permutation.lean` applies to
every finite index type, alphabet with decidable equality, code and fixed
nonnegative rational threshold. It proves preservation of Hamming counts,
normalized Hamming distance, exact membership and farness against the image
code `{word ∘ π | word ∈ code}`. With a positive threshold, farness excludes
membership. Invalidity alone does not imply farness. The selected clients use
nonempty positional domains.

## Execution laws

- `lookup_agrees` requires the actual table at the selected handle to be
  `positionalTable word`. This is the partial readback square; absent entries
  do not silently become a value.
- `withTables_read` uses the existing ideal reading. `ideal_frame` preserves
  every base-handler state coordinate and emits no events, for Yes, No and gap
  inputs. `withTables_read_missing` retains rejection on unavailable access.
- `read_within_one` and `read_not_within_zero` count the actual descriptor
  independently of values, authentication success or provider cache hits.
  `run_read` retains the underlying handler's complete outcome, state and trace,
  including stopped executions.
- `AuthenticatedPermutation.lean` uses the existing `Commitment.run` and
  `Extractable.authenticate`. `authenticated_read_bind` preserves the history,
  roots and messages passed to an arbitrary continuing process and consumes
  exactly one opening on success. It introduces no commitment or base operation.
- `authenticated_query_bound` separately transports the selected
  authenticator's hash-query bound. One positional read can require several
  cryptographic queries. No value-agreement premise supplies this bound.
- `authenticated_no_transcript_queries` restricts every query to the hash
  namespace. `authenticated_cache_extends` retains all previous joint-cache
  answers. `authenticated_transcript_frame` preserves every transcript cell,
  present or absent, on both accepted and rejected authentication. Hash cells
  may be added; there is no cache reset or claim that the entire cache is equal.

## Reuse and controls

`TestsSecurity/OraclePermutation.lean` contains two parametric reuse clients:
reversal of a singleton reference code, and a coordinate swap on a repetition
code. The latter also proves the image code equals the original repetition
code. Both instantiate the same access and farness theorems. Concrete controls
establish:

- A noninjective coordinate map can erase the only error and change distance.
- A word at distance `1/4` is invalid but outside No at threshold `1/2`, before
  and after permutation. The same Yes set with different gaps has different No.
- Permuting the word without its corresponding code breaks membership.
- Two reads can return the same value as the adapter while failing its bound.
- An unavailable handle rejects.
- A cached uniform-bit oracle returns a point mass rather than a fresh uniform
  bit; this is checked against the existing lazy random-oracle implementation.

## Integration boundary

The implementation baseline is `1956aff09a35e1c31fab200e93df240631727c28`.
Inspected owners are `Commitment/Verifier.lean`, `Commitment/Charges.lean`, the
FRI positional reads and `tableOf` in the optional integration's
`ZkcArkLibExamples/CommittedFri.lean`, and `Far` in
`ZkcArkLib/Fri/Soundness.lean`. The inspected ArkLib checkout is
`1e0241333c18d8b22cb68f9522da5f9fb88f9a06`. Its executable context lens requires
statement-independent output lifting; this adapter does not claim a general
replacement for that lens.

The normalization matches the formula of ArkLib's `Code.relHammingDist`:
Hamming count divided by index cardinality in `ℚ≥0`. A future FRI integration
must check that equality in its own package, cast the selected rational gap to
the real-valued FRI predicate, and connect the exact domain and code. The
security package acquires no ArkLib dependency. The coordinate-count proof's
upstream source is credited in the mathematical module.

The parent can instantiate its claim relation with exact code membership and
`Far code threshold`, using `far_excludes_member` for disjointness,
`mem_permutedCode_iff` for the forward witness/membership law, and
`far_reindex_iff` for No transport. Runtime agreement and resource obligations
remain the separate realization laws above. This change defines no competing
claim/component/connection contract and changes no global imports or semantics.

The body is bound to an exact existing typed `PIR.Process` access. A frontend/IR
descriptor export, checked source occurrence and routing, registration in the
parent's contract assembly, and any canonical receipt remain integration work.
They are not established by a finite control or by this library theorem.

This boundary does not prove application-invalid-to-FRI-far, FRI folding
proximity, a full FRI/STARK theorem, AIR adequacy, DEEP/grinding assumptions,
hash/leaf-layout correspondence, or source/native/program-byte correspondence.
The parent retains those separately owned paper and implementation obligations.

## Focused validation

With the pinned dependencies and seeded project caches, run from
`lean/security`:

```sh
for module in \
  ZkcSecurity/Families/Proximity/Permutation \
  ZkcSecurity/Bindings/Oracle/Permutation \
  ZkcSecurity/Bindings/Oracle/AuthenticatedPermutation
do
  mkdir -p ".lake/build/lib/lean/$(dirname "$module")"
  LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
    -o ".lake/build/lib/lean/$module.olean" "$module.lean" || exit
done
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  TestsSecurity/OraclePermutation.lean
```

These commands compile only the new modules, write only the isolated project's
objects and reuse existing dependency objects. They do not build all packages.
The test module prints the axiom closures of the principal laws and controls;
only `propext`, `Classical.choice` and `Quot.sound` occur. Full native and
protocol suites are outside this validation scope.
