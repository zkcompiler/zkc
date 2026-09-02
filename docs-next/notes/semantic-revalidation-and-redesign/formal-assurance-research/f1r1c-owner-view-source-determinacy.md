# F1-R1C Owner-View Source Determinacy and F0 Reopening

> **Kind:** Temporary F1 source-contract falsification and F0 reopen record
> **State:** F1-R1C0 determinacy audit complete with `CannotAnswer`; F0-V1 has
> since established publication-topology feasibility, and F0-V2A has selected
> and validated a bounded generic schema algebra. Exact target grammar and
> migration remain required before the evaluator may proceed
> **Authority:** None. This result changes no current or target semantic law,
> profile identity, admission judgment, Analysis result, or roadmap priority.
> **Evidence:** The focused audit under
> [`evaluation/formal-source-owner-views-f1r1c/`](../../../../evaluation/formal-source-owner-views-f1r1c/README.md)
> matches 13/13 expected observations and returns
> `CannotAnswer/F1R1C-C-SOURCE-DETERMINACY`.

## 1. Question and disposition

F1-R1C began with an exact admitted Core and Fresh Protocol from F1-R1B. Its
next obligation was to derive the complete target `PublicBindingView`,
`StrategyDecisionView`, `PublicCoinView`, `EffectView`,
`ClaimReductionView`, and Protocol `ExecutionView`, then compute atomic field
coordinates and the least required-read fixed point without trusting a caller.

The source-side precondition does not yet hold. The aggregate result is
`CannotAnswer`, not Negative, Refused, or an implementation failure:

```text
exact target profile and source fragment                 Affirmative
exact admitted Core and Fresh Protocol handles           Affirmative
six readable owner-view surfaces                         Affirmative
published six-entry schema catalog                       absent
exact view/coordinate/manifest body grammar              absent
exact law-field declaration bindings                     absent
exact static-view authority-envelope body grammar        absent
therefore exact target read manifest                     CannotAnswer
```

Issuing a view under locally invented encodings would turn the evaluator into
a second schema owner. Continuing to R1D would then package a coherent but
non-target projection, reproducing the exact failure mode that F1-R1A and
F1-R1B were introduced to prevent.

## 2. Exact observations

### 2.1 What the target already authenticates

The two independent semantic-profile compilers reproduce the same frozen
Interaction profile. Its `interaction-static-views` fragment includes the
common coordinate vocabulary, all six displayed view records, closure prose,
issuance operation, and source-role bodies. Changes to those fragment bytes
rotate the profile. The R1-B finite Schnorr Core and Fresh Protocol continue to
admit under that exact profile.

This rules out three overstatements:

- the view contract is not ambient or wholly outside profile identity;
- the Core carrier does not need another field merely to make views possible;
  and
- F1-R1B admission did not accidentally grant view authority.

### 2.2 The promised schema catalog is not published

Section 13.1 says the standalone PIR profile fixes a closed
`PIRViewSchemaCatalog` in an inline profile-owned declaration catalog, with one
entry per view kind containing the owner subject, body schema, derivation law,
field resolver, closure law, source-binding schema, and capability contract.

The compiled Interaction profile has only the common publication catalogs:

```text
pir.body-compiler
pir.evaluator-signature
pir.failure-schema
pir.semantic-law
pir.source-fragment
pir.subject-language
```

There is no owner-local schema extension catalog. No manifest definition has
a selector for any of the six `*ViewBody` declarations. The complete fragment
is authenticated indirectly through other declarations, but an exact schema
entry cannot be resolved or substituted as the issuance law requires.

### 2.3 Readable shapes are not yet complete machine boundaries

The six displayed records state useful semantic intent, but the target also
claims that paths terminate at exact atomic leaves with no prose or
implementation-defined remainder. The source currently supplies no canonical
body grammar for the six view records or for:

```text
PIRStaticViewOwnerCoordinate
PIRStaticViewCoordinate
PIRViewPathStep
PIRViewAtomicBoundary
PIRStaticViewFieldCoordinate
PIRStaticViewReadManifest
```

Several displayed fields use semantic descriptions such as complete producer
coordinates, exact producer edges, resolver coordinates, and a run-record
schema. Those descriptions are sufficient design guidance but do not select
one independently reconstructible atomic tree and encoding.

### 2.4 Law references are typed but not bound field by field

The profile correctly publishes exact `pir.semantic-law` declarations. The
view records contain five law-valued positions:

```text
prover_view_formation
visible_history_law
generated_execution_law
replay_qualification_law
relation_run_view_issuance_law
```

The source says proposition-valued `_law` or `_requirement` fields carry exact
profile declaration references, but it provides neither an explicit mapping
table nor schema-entry dependencies that bind each position. In particular,
`prover_view_formation` is law-valued without following the naming rule. A
human can infer plausible declarations; an independent exact checker should
not have to infer a canonical field value from prose.

### 2.5 Static-view issuance cannot form its inert envelope exactly

The issuance section requires a profiled owner-binding payload committing to
the producer coordinate and complete manifest, an exact no-policy declaration,
a typed consumer/purpose requirement, and a policy-closure ID. The Interaction
manifest routes all six generic `pir.source-*` kinds through
`source-authority-envelope-body-v0`, whose selector is
`PIRSourceConsumerRoleBody(x) = R`.

Within the static-view fragment the only explicit body functions are:

```text
PIRProfileLawReferenceBody
PIRSourceConsumerRoleBody
PIRSourcePurposeRoleBody
```

The four static-view payload, requirement, no-policy, and closure grammars are
not present. Confidential-Oracle bodies elsewhere do not define the static
view family and cannot be reused by label.

## 3. Why K2 is not a repair

The behavioral K2 witness remains useful for deriving candidate facts and
mutations. Its static-view manifest is a tuple of top-level enum fields, with
only a small challenge-leaf coordinate exception, under a witness-local
Interaction profile. The target requires one owner/profile-qualified nonempty
path to every atomic boundary. Reusing K2 would therefore repeat profile and
schema substitution rather than implement the target.

This is exactly `Refused/F1R1C-R-FIXTURE-VIEW`, not evidence that the K2
behavioral tests are wrong.

## 4. F0 impact

F0 reopens narrowly at the owner-view publication and issuance contract. The
larger A/S/C architecture survives:

```text
admitted PIR owner
  -> exact owner-derived static view and read closure
  -> neutral question-relative source package
  -> independently checked Analysis correspondence
```

The finding does not justify a `FormalKernel`, theorem-prover authority, a new
Core field, moving challenge semantics into Analysis, or collapsing Core and
Protocol. It does invalidate the earlier positive non-change statement that
the existing target view contract was already exact enough for F1.

The repair belongs to PIR and semantic-profile publication because PIR owns
the facts, schemas, closure, binding, and capability. Analysis should consume
the repaired view; it must not define it.

## 5. Ideal repair program

### R1C-P0 — publish the schema contract

1. Add an explicit owner-local catalog kind such as
   `pir.static-view-schema`, with exactly six entries and exact source
   selectors.
2. Give each entry the owner subject kind, complete body grammar, derivation
   law, atomic resolver, least-closure law, authority-envelope compiler, and
   capability contract through exact declaration dependencies.
3. Define closed canonical grammars for every nested record/sum used by the
   six views and for coordinate, path, boundary, and manifest values.
4. Publish an explicit field-to-`pir.semantic-law` reference table; rename or
   explicitly type `prover_view_formation` so the rule is total.
5. Replace the ambiguous shared source-envelope compiler with either one
   exact compiler per `pir.source-*` subject kind or one explicitly tagged,
   closed dispatch whose every family arm has a canonical body.

The profile publication mechanism already supports owner-local `pir.*`
catalogs, so this is a repair inside the existing owner/profile architecture.
No new Foundation mechanism is presently indicated.

F0-V1 has now tested this conclusion executablely. The selected in-place
candidate and its five directly affected dependent profiles compile through
both publication implementations, produce the predicted sixteen-profile
rotation cone, and refuse the bounded topology mutations. See the
[`F0-V design and result`](f0v-owner-view-publication-repair-design.md) and
[`executable gate`](../../../../evaluation/formal-source-owner-view-repair-f0v/README.md).
That result closes mechanism feasibility only. F0-V2A has since selected one
finite PIR-owned schema universe and independently validated its generic
enumeration/resolution method over representative six-view structures; see
the [`F0-V2 design and result`](f0v2-canonical-view-schema-design.md) and
[`executable gate`](../../../../evaluation/formal-source-view-schema-f0v2a/README.md).
It also replaces the separate field-to-law table with fixed law atoms and
treats a complete admitted module effect as an opaque semantic leaf. Exact
six-body grammar and migration remain F0-V2B/C work.

### R1C-P1 — migrate and independently reconstruct

The repair changes Interaction source bytes and catalog structure, so it
rotates the Interaction profile and every dependent profile identity. The
publication program must decide the explicit revision/compatibility treatment,
regenerate the frozen identity table through both compilers, and update the
F1-R1A/R1B profile-bound controls. Unchanged Core domain bytes will still gain
new profiled IDs; old bytes must not be reinterpreted.

The mutation suite should refuse at least a missing/extra schema entry, wrong
owner subject, wrong schema selector, wrong law declaration, incomplete law
dependency, coordinate-tag alias, interior-record boundary, cross-view path,
and cross-kind authority body.

### R1C-P2 — implement and test owner derivation

Only after P0/P1 should the bounded evaluator:

- derive all six full views from the identical R1-B admitted handles;
- enumerate every atomic leaf and resolve each path independently;
- compute the constructor-specific least closure from selected leaves;
- require requested, derived, and realized read sets to agree exactly;
- form the exact inert payload/requirement/no-policy/closure identities; and
- issue noncopyable, nonserializable, consumer/purpose-bound live authority.

The R1-B mutations remain controls. R1C adds omission, phantom leaf,
equal-value coordinate alias, wrong boundary, law substitution, Core/Protocol
substitution, reconstructed-handle, and capability consumer/purpose cases.

## 6. Assurance position and sequencing

| Level | Result after this audit |
|---|---|
| Q0 current source admission | open; R1-B remains offline bounded admission |
| Q1 exact admitted-source reification | `CannotAnswer`; target view source is not yet determinate enough |
| Q2 provider correspondence | not started |
| Q3--Q6 theorem and property | not started |
| Q7--Q10 transition through realization | not started |

The corrected sequence is:

```text
F1-R1B   exact target carrier/admission                 [complete, bounded]
  -> F1-R1C0 owner-view source determinacy              [complete, CannotAnswer]
  -> F0-V1   publication-topology feasibility           [complete, bounded]
  -> F0-V2A  generic schema-algebra feasibility          [complete, bounded]
  -> F0-V2B  exact six-body grammar                      [open]
  -> F0-V2C  target publication and migration            [open]
  -> F1-R1C  owner view, read closure, issuance         [waiting on F0-V2C]
  -> F1-R1D  integrated Relations/source package        [waiting]
  -> F1-I    live implementation authority              [waiting]
```

This is the intended value of F1 pressure testing: stop at the first absent
owner premise, test the repair mechanism, complete the actual owner contract,
and then resume without weakening the proposition.
