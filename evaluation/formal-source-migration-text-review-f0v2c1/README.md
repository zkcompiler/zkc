# Migrated owner-text freeze review

## Exact question

Does the current migrated PIR owner text close all sixteen verification
questions: the ten previously frozen owner-text questions, plus exact Interface
completion derivability, source-authority preimage equations, heterogeneous
challenge-transition representability, required-influence exactness, the
Analysis owner-read join, and public-setup view totality?

Run from the repository root:

```sh
python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check
```

## Frozen answer

No. The current result is
`CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED`. The ten earlier questions
remain affirmative, and three of the six new questions close. Three are
blocked:

- `CannotAnswer/F0V2C1-C-INTERFACE-COMPLETION-DERIVATION`: the Interface
  presents the construction, challenge, prefix receipt count, and prefix state,
  but the owner transition evaluates acceptance with public-condition values
  and prior joint-member challenge values at
  `docs-next/pir/fiat-shamir.md:863-866`. Those inputs are not among the
  completion coordinates and are not recoverable from a potentially
  noninjective transcript state.
- `CannotAnswer/F0V2C1-C-CANONICAL-BINDING-PREIMAGE`: the PIR text has one
  tagged compiler route for every audited source-authority constructor, but the
  Analysis executable requests its Fiat--Shamir execution view at
  `evaluation/k3-analysis-closure/reference_model.py:16521` through a common
  helper that forms and hashes an untagged six-field payload record at
  `evaluation/k2-protocol-fiat-shamir/reference_model.py:2262-2283`. It never
  invokes the canonical-framed source compiler.
- `CannotAnswer/F0V2C1-C-PUBLIC-SETUP-VIEW-TOTALITY`: the owner correctly places
  the review countermodel's occurrence-derived binding in `run_established`,
  but the claim at `docs-next/pir/interactive-core.md:3062-3063` that every
  Protocol has exactly one view ignores invocation-valued entries. The current
  Schnorr fixed-setup formation at
  `docs-next/analysis/cryptographic-properties.md:523-525,561-566` neither
  requires `run_established` to be empty nor permits it as the complement of
  the entry sequence.

The completion coordinate types themselves fit the Foundation bounds. The
fixed worst tuples are `(11,1,0,0)` for the challenge natural,
`(12,1,0,0)` for the receipt-count natural, and `(64,3,2,1)` for the domain
payload record. Both state coordinates inherit the construction's stricter
tagged-completion preflight. The six coordinate constructors and the six body
arms agree exactly.

## Closed repaired questions

The heterogeneous two-rule countermodel now has one exact
`challenge_rules` sequence. Rule zero retains Boolean decoding and bounds
`(1,1)` at position zero; rule one retains `RootNat(2)` decoding and bounds
`(2,3)` at position one. No rule is selected, dropped, or changed.

The influence view also closes. For a first challenge after a root opening with
two public bindings, its required entries are the exact Core, construction, and
application-domain headers, the root scope atom, and distinct binding atoms
zero and one. For a second challenge, the static sequence additionally carries
one required `EveryActualDrawOf(0)` entry, expanded at runtime to the exact
tag-13 draw atoms in order. `InfluenceAtom` has one definition, its body has
tags zero through thirteen, and the view explicitly includes the requirements
from items 9 and 10 of the owner law.

The Analysis read catalog contains ten literal view selections and 66 selected
top-level fields. Every name resolves to a field of the selected owner body.
The owner law says these names are ordinal subtree paths and expands them to
every atomic leaf, so no current selection is ambiguous between a leaf and a
subtree. The developer control covers all ten current literal calls and is
sufficient for this field-existence join; it does not by itself prove the
recursive semantic meaning of the expanded leaves.

The source-authority text audit scans all top-level PIR Markdown pages, fourteen
identity constructors, and twenty-four profile compiler definitions. All ten
direct constructors apply a same-page compiler to an enumerated family tag;
all four generic static-view constructors dispatch through the owner profile.
Both Fiat--Shamir family pages enumerate `StaticView` and
`CheckedConstruction` arms for all four family-valued source subject kinds.
The frozen failure is confined to the executable preimage route described
above, not the current owner prose.

## Earlier questions and publication reconstruction

The earlier decision-fidelity, Terminal, public-coin graph, owner-name,
manifest, publication-compiler, family-body, PIR-reference, static-view-law,
and declaration-body findings remain affirmative. The current family-view
census contains 91 exact fields across the eight construction/result bodies.
The existing bounded schedule, terminal, region, claim-status, reference-leaf,
law-selection, declaration-body, and manifest checks are rerun unchanged apart
from current source and revision pins.

The reference and independent publication compilers agree on all eighteen
profiles at the current tree, the round-seven tree, and the migration base.
Relative to round seven, sixteen profiles rotate. `oir-endpoint-graph` and
`analysis-kernel` are stable, Foundation is unchanged, and no publication table
is written. Relative to the migration base, the previously frozen
seventeen-profile cone remains, with only `analysis-kernel` stable.

## What a passing check establishes

A passing `--check` establishes that the exact pinned sources reproduce all
sixteen finding outcomes, including the three explicit `CannotAnswer`
boundaries, the three closed repair countermodels, the ten retained findings,
and agreement of the two publication compilers. It does not turn a missing
premise into an affirmative result and does not edit an owner source.

It does not publish or bless an identity, prove any owner law for arbitrary
values, validate a live compiler, runtime, provider, backend, or endpoint,
establish relation satisfaction or theorem truth, or prove Fiat--Shamir,
random-oracle, concrete-sponge, QROM, protocol-security, deployment, or
production-readiness claims.
