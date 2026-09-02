# F1-R1C owner-view source-determinacy audit

This gate asks whether the published target source determines enough exact
structure to implement the six PIR owner views and their least required-read
closure without inventing a second schema. Its aggregate result is
`CannotAnswer/F1R1C-C-SOURCE-DETERMINACY`.

This is a source-contract audit, not a static-view implementation, target
semantic authority, Q1 result, or claim that the admitted Core is defective.

Run it from the repository root:

```sh
python3 -B evaluation/formal-source-owner-views-f1r1c/run.py --check
```

Use `--json` for the complete evidence inventory.

## What remains affirmative

The audit first establishes five positive controls:

- the two independent profile compilers reconstruct the same Interaction
  profile;
- that profile matches the frozen v0 publication row;
- its exact static-view source fragment is authenticated;
- the fragment names all five Core views and the Protocol `ExecutionView`; and
- the retained F1-R1B Core and Fresh Protocol still admit through exact
  process-local owner handles.

The finding is therefore not that the view prose is unhashed, that the Core
lacks a field, or that target admission failed.

## Why the aggregate is CannotAnswer

The authenticated source promises a closed `PIRViewSchemaCatalog` in an
inline profile-owned declaration catalog. The published Interaction profile,
however, contains only the six common catalog kinds and no extension catalog.
None of the six view bodies has a declaration entry or selector.

The same source displays readable record shapes, but it does not provide the
exact grammars needed by the claimed field resolver and source envelope:

- no canonical body compiler for any of the six complete view bodies;
- no exact body grammar for owner coordinates, path steps, atomic boundaries,
  field coordinates, or manifests;
- no explicit map from five law-valued fields to exact
  `pir.semantic-law` declaration references; and
- no closed static-view body grammar for the binding payload, capability
  requirement, no-policy declaration, or policy closure. All six generic
  `pir.source-*` subject kinds currently route through one compiler selector,
  while the static fragment defines only the law-reference and
  consumer/purpose role bodies.

Those are absent semantic premises, not negative statements about a formed
view. A research evaluator could choose plausible records and law references,
but then its choices—not the exact owner contract—would determine the source
projection. The gate therefore refuses to fabricate a manifest.

The retained K2 view witness cannot fill the gap. It has a witness-local
profile and top-level enum fields; the target requires owner-qualified atomic
paths and boundaries. The gate classifies that substitution as
`Refused/F1R1C-R-FIXTURE-VIEW`.

## Evidence diversity and limits

[`audit_model.py`](audit_model.py) compiles the profile through both existing
independent publication implementations, inspects their structured artifacts,
and re-admits the R1-B subject. [`independent.py`](independent.py) separately
parses the raw manifest with duplicate-key rejection, extracts the marked
source ranges itself, and reproduces the catalog, selector, body-function, and
compiler-routing inventory. The 13 expected observations are frozen in
[`expected-findings.json`](expected-findings.json).

Agreement is bounded evidence, not a proof that the proposed repair is
complete. The audit does not execute a view, issue a binding or capability,
establish read adequacy, or show current implementation conformance.

## Exact repair gate before R1C resumes

F0 must reopen at the owner-view publication boundary. A repair should provide:

1. an explicit six-entry profile-owned static-view schema catalog;
2. closed view, coordinate, path, boundary, and manifest grammars;
3. an exact field-to-law-reference table and declaration dependencies;
4. closed per-subject or explicitly tagged authority-envelope body compilers;
5. independent profile reconstruction and the resulting identity migration;
   and
6. mutation controls for missing schema entries, wrong law refs, ambiguous
   paths, and cross-kind envelope substitution.

Only then should R1C implement full owner-derived views, atomic field
resolution, the least read fixed point, exact requested/realized equality,
and process-local issuance. R1D and F1-I remain downstream.
