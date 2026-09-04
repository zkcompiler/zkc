# Semantic migration candidate

## Exact question

Do two independent publication compilers reconstruct the same current
eighteen-profile identity table from the pinned migrated owner sources, while
also preserving the migration head's rotation result and performing no
publication?

Run the frozen gate from the repository root:

```sh
python3 -B evaluation/semantic-migration-candidate/run.py --check
```

Use `--json` to inspect the complete identity tables, source inventory,
prerequisite-gate evidence, and refusal controls.

## Frozen answer

Yes, as a bounded non-publishing rehearsal. The reference and cold compilers
agree on all eighteen current identities. Relative to the pre-migration
identity pin, the migration head rotates seventeen profiles and leaves only
`analysis-kernel` stable. The current Analysis head rotates all eighteen.

The difference between the migration and Analysis heads is exactly these six
profiles:

- `analysis-kernel`;
- `analysis-cryptographic-property`;
- `analysis-afk-transport`;
- `analysis-afk-theorem-source-validation`;
- `analysis-incremental-composition`; and
- `analysis-incremental-composition-source-validation`.

This additional cone is expected because this branch re-authors the Analysis
owner pages. It does not weaken or rewrite the migration-head control.

The contract pins six owner pages and eight profile manifests. The rehearsal
also reruns the target-basis, target-carrier, owner-view, and terminal-contract
prerequisites, refuses every legacy published identity in scope, and verifies
that the checked-in publication table is byte-identical before and after the
run.

## Evidence boundary

A pass establishes exact source-pin agreement, dual-compiler agreement for the
measured current and migration-head tables, the stated finite rotation cones,
the frozen prerequisite observations, and absence of a publication-table
write.

It does not publish or finalize an identity, make the current candidate
normative, prove a protocol or security theorem, establish provider or
implementation correspondence, validate a backend, or establish production
readiness. The legacy publication hold remains separate and intentionally
unresolved.
