# Source-bound positional permutation client

`SourceBoundPermutation.lean` installs one reusable, request-restricted opaque
family over four Boolean coordinates. A request selects a fixed-reference or
repetition code, reversal or a coordinate swap, and a positive rational gap
(`1/4` or `1/2`). The exact static argument list includes the Boolean alphabet,
dimension, code, ordering, gap numerator and denominator, and source/output code
direction. The ordered runtime ABI has four Boolean statement ports.

The installed predicate is exact membership in the selected source code or its
permuted output code. `OpaqueRegistry.Binding`, `RegisteredRelations` and the
shared `Source.Structured.RelationMeaning` determine that predicate before proof
evidence. A Boolean relation does not specify a distance gap: the separate
`Families.Proximity.relation` contract fixes `No := Far code gap`. The typed gap
also participates in registry selection, so coincident Yes predicates cannot
reuse a differently configured request's binding or No adapter.

`TestsSecurity/SourceBoundOraclePermutation.lean` admits two authored Snapshots
through `structured_views`, including exact raw/typed helper association and a
continuation contract's input and output relation applications. The clients are
reversal of a nonconstant fixed reference at gap `1/2`, and swapping two
coordinates of the repetition code at gap `1/4`. Both consume the shared
`RelationMeaning.RealizesClaim` gate and the same installed family. Encoding is
total and has a proved inverse on every mathematical word; membership is neither
universally true nor universally false.

The source helper only reorders the four coordinates. Its actual admitted closed
invocation returns the encoding of the mathematical permutation. Separately,
`body` is definitionally the existing `Permutation.read` typed Process at the
unchanged handle and the permuted position. `checked_reversal` and `checked_swap`
join installed relation association, output-code direction, gap-sensitive No
transport and actual one-read simulation. The shared parametric permutation
theorems prove the distance and transport laws; finite controls only test
specific boundaries.

The actual commitment interpreter supplies authentication and arbitrary-suffix
history/root/message preservation. A positional-read bound remains distinct
from the independently assumed authenticator query budget. Supported shared
cache runs retain previous answers and all transcript cells, including absent
cells and failed authentication. None of these laws resets or materializes an
oracle, or turns cached authentication into fresh randomness.

Refusal controls reach the actual source checker, registry resolution/admission,
or shared relation-association obligation. They cover wrong static code,
ordering, gap, dimension, direction, argument type, ABI and purposes; a missing
registry; source/math membership mismatch; an unpermuted output code; an empty
encoding domain; a missing readback; and reusing a No adapter after changing the
gap while retaining Yes. The existing `OraclePermutation` controls additionally
cover noninjective coordinates and correct-value implementations with excessive
reads.

These are independently checked authored Snapshots, not native compiler exports.
There is no source-oracle descriptor or compiled-source/read correspondence.
The source association and existing typed Process access law are the established
boundary. Application-to-farness, FRI, native execution and hash/leaf-layout
correspondence remain separate obligations.

After integrating the shared relation-meaning seam and building its dependencies,
run from `lean/security`:

```sh
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true \
  -o .lake/build/lib/lean/ZkcSecurity/Bindings/Oracle/SourceBoundPermutation.olean \
  ZkcSecurity/Bindings/Oracle/SourceBoundPermutation.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true \
  TestsSecurity/SourceBoundOraclePermutation.lean
```

The test executes the structural/registry controls and prints the axiom closures
of the association, access, authentication, query and capture laws.
