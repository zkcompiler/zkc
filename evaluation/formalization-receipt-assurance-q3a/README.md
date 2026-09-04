# Q3-A formalization-receipt assurance audit

This package asks one question at cutoff
`faea36ef6da3f82e29ff5fddc6750a4824bfbc2a`:

> Can the current pinned ArkLib `FormalizationReceipt` path form an
> independently authenticated Q3 theorem-environment result for its six live
> declarations, with exact identity, failure partition, and residual trust?

The frozen answer is
`CannotAnswer/Q3A-C-OBSERVATION-NOT-AUTHENTICATED-RESULT`.
The current path is a useful source-drift reader and a bounded Q3 input. It is
not yet a durable Q3 result constructor.

Run the offline, standard-library-only gate from the repository root:

```sh
python3 -B evaluation/formalization-receipt-assurance-q3a/run.py --check
```

The result is 29 findings: nine affirmative observations, five fail-closed
refusals, and fifteen `CannotAnswer` boundaries. The ordinary gate does not
need Lean, ArkLib, the network, or a cached external build. It validates one
dated live observation and then runs fourteen black-box cases, including the
baseline and thirteen mutations, against the production receipt driver.

## What was observed

On 2026-09-03 the production driver was run against a clean checkout of the
official ArkLib repository at its exact registry pin
`fad5cbf808774838924dc8273715724c6a6caa1f`. The checkout used Lean 4.31.0
(`68218e876d2a38b1985b8590fff244a83c321783`) and the committed ArkLib
toolchain and Lake manifest. All six checkable declarations resolved; every
normalized printed statement and every transitive axiom set equalled its
receipt. Four receipts outside ArkLib were reported but not checked.

The observation is frozen in [`live-observation.json`](live-observation.json)
with the zkc driver, signature, upstream registry, workflow, ArkLib tree,
toolchain, and dependency-file digests. This file is a research record created
after the command returned zero. It is not a workflow-issued result artifact
and is not retroactively treated as the missing Q3 result.

One declaration,
`RandomQuery.oracleReduction_completeness`, reproduced with `propext`,
`Classical.choice`, and `Quot.sound`, and without `sorryAx`. Five reproduced
with `sorryAx`. This says exactly what the environment reported about those
declarations. It does not establish intended meaning, PIR correspondence,
theorem applicability, or a zkc property.

The public `Lean reading` workflow was active but had zero recorded public
runs when inspected on 2026-09-03. The successful local exact-pin run above is
therefore the observation used here; an absent public run is not classified as
a failed reading.

## Two independent paths

[`model.py`](model.py) directly inventories the registry and validates the
frozen source and environment identities. It does not import or execute the
production driver's logic. [`independent.py`](independent.py) treats that
driver as a black box, writes a temporary mutated signature for each case, and
observes only its exit status and reported checkable count. [`run.py`](run.py)
joins the paths and compares their exact findings with
[`expected-findings.json`](expected-findings.json).

The paths have different jobs. The direct model prevents a successful driver
run from silently expanding into a stronger claim. The mutation path measures
which receipt fields the driver actually authenticates in offline mode.

## Field boundary

| Receipt or environment field | Current path | Exact limit |
|---|---|---|
| repository and revision | checked for ArkLib | the driver checks `HEAD`, not a clean tree or remote identity |
| declaration | must be nonempty; resolves in external mode | module discovery is a source-search heuristic, and no imported-module closure is emitted as a result |
| printed statement | compared in external mode | arbitrary substitution passes the ordinary offline driver |
| axiom set | compared as a set in external mode | offline mode checks only whether `sorryAx` agrees with `mechanized` versus non-mechanized |
| `mechanized` | distinguished from any state carrying `sorryAx` | exact `proof_incomplete` versus `subject_incomplete` cause is not derivable from `#print axioms` |
| `covers` | must be nonempty | its semantic relationship to the declaration is authored, not checked |
| `does_not_cover` | recorded | deletion is accepted by the driver |
| external non-ArkLib receipts | listed | declaration, statement, environment, and axiom closure are not read |
| toolchain, lock, modules, checker mode | operationally used in the external run | the current driver emits no typed result binding the complete basis |
| run result | human-readable stdout and exit code | no canonical result identity, durable artifact, qualified outcome, or consumer capability is formed |

The production driver is not the whole signature validation stack. In
particular, the `unknown-incomplete-state` mutation demonstrates only that this
driver does not own the state enum; other registry/schema checks may reject
the same mutation. The package keeps that boundary explicit.

## Mutation results

The driver refuses an empty declaration, wrong ArkLib pin, empty `covers`, a
`mechanized` receipt with `sorryAx`, and a non-mechanized receipt without
`sorryAx`.

It accepts both directions of `proof_incomplete`/`subject_incomplete`
relabeling, unrelated but nonempty coverage text, removal of
`does_not_cover`, statement and non-`sorryAx` axiom substitutions in offline
mode, an unknown non-mechanized state, and deletion of an ArkLib statement.
The last case silently changes the report from six to five checkable receipts;
it is visible in stdout but is not a failing outcome.

These accepted mutations are not all defects. Some fields intentionally
belong to another validator or to human correspondence review. They show why
the current command cannot itself be interpreted as an authenticated result
for those fields.

## Smallest coherent next boundary

This audit does not select a redesign. It identifies three separable choices
for the main design lane:

1. **Retain a drift reader.** Keep the present mechanism and narrow its public
   claim to exact-pin statement/axiom reproduction. Treat incompleteness cause,
   coverage, and exclusion scope as reviewed annotations.
2. **Add a Q3 environment result.** Define a typed proposition and qualified
   result binding repository and revision, clean tree and source tree,
   dependency lock, toolchain, imported modules, declaration, normalized
   statement, complete axiom profile, checker identity and mode, source
   identities, and a canonical result ID. Preserve `Mismatch`,
   `MissingDependency`, `Unsupported`, and `CannotAnswer` separately rather
   than collapsing them into pass/fail.
3. **Raise hostile-provider assurance.** In a profile that treats compiled
   proof artifacts as untrusted, add fresh kernel replay and optionally a
   comparator or independent checker. Lean's official
   [proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
   distinguishes `#print axioms` from replay and describes
   `lean4checker --fresh` and stronger cross-checking options.

Choice 2 is the smallest candidate that answers the stated Q3 identity
question. Choice 3 is a policy-dependent strengthening, not a prerequisite
for every receipt. Neither choice can derive `proof_incomplete` versus
`subject_incomplete`: that split needs a separate provenance analysis of where
the `sorryAx` enters. Likewise, neither can validate `covers`; that requires a
Q2 correspondence or Q5 applicability proposition over exact formal and zkc
subjects.

## Non-claims

This package does not:

- establish Q1 source reification, Q2 provider correspondence, Q4 theorem
  truth policy, Q5 applicability, or Q6 property truth;
- verify ArkLib, Lean, Lake, the production receipt driver, or the GitHub
  workflow;
- classify all of ArkLib, the four external receipts, or any theorem not named
  in the six live receipts;
- show that a `sorryAx`-free declaration means what zkc needs;
- make formalization annotations part of Soundness Kernel derivation; or
- change PIR semantics, Analysis authority, compiler behavior, a target
  profile, or a user-owned decision gate.
