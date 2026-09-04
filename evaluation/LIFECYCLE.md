# Evaluation lifecycle

`evaluation/` is the project's research workbench. It is allowed to contain
models and falsifiers that are faster to change than the durable Python
reference or product implementations. That freedom does not make the
directory an untracked scratch dump: every executable package has a stable
check ID, an explicit evidence scope, and a declared disposition in
[`lifecycle.json`](lifecycle.json).

The lifecycle catalog is operational metadata, not semantic authority. A
`retain` decision says only that the package still answers a distinct live
question. A `promote-then-retire` decision says that useful laws should move to
their durable owner; it does not make the research implementation normative.
An `active-sequence` keeps predecessor falsifiers available until the selected
source and its downstream correspondence are closed.

## Promotion path

```text
research instrument
        |
        +-- stable semantic law ----------> reference/ owner
        +-- shipped behavior/refusal -----> native or Rust suite
        +-- external correspondence ------> pinned evidence harness
        `-- rationale/reversal trigger ---> durable design document
                         |
                         v
               predecessor replay passes
                         |
                         v
                  research package retires
```

Promotion requires all of the following:

1. the exact exercised claim and its non-claims have stabilized;
2. a durable owner is named instead of adding a second authority;
3. the minimal positive, negative, and disagreement fixtures are carried over;
4. any claimed independence remains real after code is moved;
5. the successor reproduces the predecessor's accepted evidence record;
6. durable consumers and documentation no longer depend on the package; and
7. the manifest and lifecycle catalog move in the same change.

Retirement then removes the package from the checkout. Git history preserves
the research implementation; the live tree preserves only the selected laws,
fixtures, and rationale. A package is not deleted merely because it is large,
nor retained merely because it once took substantial effort to produce.

## Current policy

The current catalog deliberately makes no bulk deletion. The target-model
prototypes are promotion candidates, but extracting them safely is semantic
work, especially for the expensive property-analysis surface. The migrated
owner text has been re-pinned and its exact owner-source law selection has
reclosed through the active source-definition sequence. Identity publication
and downstream correspondence remain separately gated. Cross-cutting probes
are temporary by design.
Distinct protocol witnesses, bounded falsifiers, pinned upstream adapters, and
benchmark records remain retained until their exact exit rules are met.

Run the inventory audit from the repository root:

```sh
python3 -B -m checks.evaluation_lifecycle --check \
  --output target/checks/evaluation-lifecycle.json
```

The generated report measures tracked size and maps every package to exactly
one check or declared non-check asset. Those measurements support review and
sequencing; they are not promotion verdicts.
