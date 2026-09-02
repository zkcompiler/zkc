# F0-V2B2B constructor-complete view-schema inhabitance

This package defines and tests one candidate structural schema source for all
six normalized PIR owner views. It closes the schema-and-inhabitance stage
selected by F0-V2B2A; it does not admit an extended `InteractiveCore` or derive
an owner view from one.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-view-schema-f0v2b2b/run.py --check
```

The frozen result is
`Affirmative/F0V2B2B-A-CONSTRUCTOR-COMPLETE-SCHEMA-INHABITANCE`. Its 65
findings contain ten scoped affirmatives, seven explicit `CannotAnswer`
boundaries, and 48 mutation refusals.

The checked source contains 88 named definitions and 453 source nodes. A
recursive dependency expander and a separately implemented iterative
topological expander produce identical schemas for:

- `PublicBindingView`;
- `StrategyDecisionView`;
- `PublicCoinView`;
- `EffectView`;
- `ClaimReductionView`; and
- Fresh `ExecutionView`.

The source repairs all twenty variant cases and eight maximum-zero references
reported by B2A. It covers all fourteen repair groups, including the complete
eight-case Core effect union, fourteen `PCNode` cases, three prover move cases,
ten guaranteed-read coordinates, Oracle lifecycle and receipt branches,
claims, reductions, terminal dispositions, and the opaque module-effect
boundary.

## Method

The source language has four closed constructors: atom, nonempty record,
nonempty variant, and bounded sequence. B2B strengthens the earlier candidate
sequence node with an exact lower bound and an ordering discipline:

```text
Sequence {
  minimum_length,
  maximum_length,
  discipline: Ordered | SortedUnique,
  element_schema
}
```

Without those fields, the schema could not distinguish
`CanonicalSeq<T>`, `NonEmptyCanonicalSeq<T>`, and
`CanonicalSortedUniqueSeq<T>`. That would leave empty scope paths and
reductions, duplicate graph nodes, and reordered graph sets structurally
well-typed.

The recursive implementation generates an additive inhabitance suite rather
than a Cartesian product. For each reachable node it exercises every variant
arm, every atom boundary, each legal sequence lower boundary, and a nonempty
sequence whenever one can form. The resulting 302 values cover all 914
reachable requirements. Both recursive and iterative validators accept every
value.

Thirty source mutations test profile and predecessor pins, source identity,
cycles, unused definitions, tags, fields, bounds, disciplines, body compilers,
laws, owners, and the module boundary. Eighteen value mutations test exact
record fields and order, variants, lower and upper sequence bounds,
sorted-unique behavior, typed atoms, laws, and module boundaries. Every value
mutation is rejected by both validators. Twenty-five malformed source
mutations additionally fail both grammar compilers; the remaining five are
well-formed alternative grammars rejected by the frozen source identity.

## Claim boundary

The generated values are synthetic structural inhabitants. In particular,
the value used at an `AdmittedModuleEffect` atom has the closed boundary shape
but is not an admitted module effect. B2C must start with authenticated,
immutable Core and Protocol carriers, apply the exact owner admission laws,
and derive all six values independently. It must also check canonical owner
ordering using the target body encodings rather than treating this package's
JSON diagnostic ordering as semantic authority.

B2D remains responsible for integrated PCGraph edge/transfer/sink behavior,
logical-access influence, and complete Fresh runtime Oracle receipt behavior.
F0-V2C remains responsible for profile publication, revision and identity
migration, and old-profile controls.

Accordingly, this result is not owner admission, owner-view derivation,
PCGraph correctness, runtime/replay correctness, implementation
correspondence, profile publication, a formal proof, relation satisfaction,
Fiat--Shamir soundness, or Q1.
