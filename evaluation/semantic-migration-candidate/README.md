# Semantic migration candidate

This package answers one pre-publication question: what the current semantic
design looks like when the selected Terminal repair, normalized PIR owner-view
publication, OIR Terminal obligations, and PublicCoin wording corrections are
composed in one successor candidate.

The answer is executable but deliberately not authoritative. The package
constructs owner-page and profile-manifest overrides in memory. It does not
edit the durable owner pages, write `published-identities.json`, finalize an
identity, or select any of the open provider-observable ownership choices.

The pinned source baseline is commit
`4ff8358108b6acf4355fa178b9b70529c6fb3778`.

The candidate contract is re-pinned to the current migrated owner pages and
canonical-framed manifest, including the total-schedule position rule and the
profile-local source-compiler equations. This package reconstructs profile
identities from owner text; it does not consume the finite protocol model's
source-authority IDs.

Run the bounded gate from the repository root:

```sh
python3 -B evaluation/semantic-migration-candidate/run.py --check
```

Inspect the complete structured report, including all candidate identities:

```sh
python3 -B evaluation/semantic-migration-candidate/run.py --json
```

Print the exact owner-page and manifest unified diffs without applying them:

```sh
python3 -B evaluation/semantic-migration-candidate/run.py --print-patches
```

## Common candidate

The common overlay composes four changes:

1. retain first-active Terminal selection, require positive structural use of
   every required Check, add sorted-unique required Reduction references, and
   replace authored Claim dispositions with verdict-derived dispositions;
2. publish six normalized owner-view schema entries and split the shared
   source-authority body route into exact common and profile-local compilers;
3. carry required Reduction spine references and terminal Claim references
   through the endpoint source view and OIR projection, deriving disposition
   from the Terminal verdict; and
4. state exactly which PublicCoin node owns each transfer and make class
   priority independent of source, edge, and traversal order.

The candidate touches six owner pages and seven source manifests. The complete
before/after bytes, hashes, inserted candidate clauses, and unified diffs are
part of the report rather than copied into this README.

## Identity result

Both existing publication compilers independently reconstruct the same 18-row
candidate table. Under the currently published Foundation law source, exactly
16 profiles rotate:

```text
interaction
  -> canonical-framed-fiat-shamir
  -> duplex-sponge-fiat-shamir
  -> public-setup
  -> commitment-opening
  -> oracle-commitment
  -> verifier-derived-query-plan
  -> interface-plan
  -> endpoint-source-view
  -> oir-projection-relation
  -> relations
  -> five dependent Analysis profiles
```

`oir-endpoint-graph` and `analysis-kernel` remain stable because neither
imports the Interaction root. The candidate Interaction digest is
`62464076d1ed690fa1acf93998cae4cdc3600649b5af028d4390d3046a3bb7a7`.
This value is a branch-candidate observation, not a published identity.

The gate treats every old row in the rotated cone as an explicit refusal
control and the two independent roots as stability controls. It also verifies
that the checked-in publication table is not a candidate output.

## Endpoint Terminal fixture

One finite projection fixture carries two required Reductions and two terminal
Claims across the PIR-to-OIR boundary. A separately structured audit retains
the complete sets, derives `Consume` from `Accept`, and refuses the old
authored-disposition shape, a missing Reduction, noncanonical Reduction order,
and an attempted disposition input. This is the migration fixture that the
earlier delta record lacked; it is not a general endpoint projection proof.

## Effect on the three F1 prerequisite gates

The existing gates are pinned to the current publication, so they should not
be edited in place before a migration. The candidate evaluates their migrated
forms instead:

| Gate | Candidate result | Required change |
|---|---|---|
| R1A target basis | `Affirmative` | replace equality to the frozen old row with explicit old-row refusal; both compilers agree on the successor basis |
| R1B target carrier | `Affirmative` for the bounded Schnorr slice | encode the five-field Terminal body, rotate Core and Protocol IDs, and retain the direct required-Check use control |
| R1C0 source determinacy | `Affirmative` | the six schema entries, 88-definition grammar, and six split source routes now exist; the old missing-source findings become positive controls |

This does not complete the later provider correspondence. R1C0 still records
downstream holds for the Fresh run schema, the provider-observable ownership
decision, and the integrated provider audit.

## Alternatives intentionally not selected

The three provider-observable questions remain open. The package compiles each
PIR-owned choice as a separate alternative and proves that each creates its
own 16-profile identity table. The counterpart choices add no further PIR
rotation:

| Question | PIR-owned alternative | Other-owner alternative |
|---|---|---|
| exact algorithm reading | add an authenticated preimage observable to the owner view | carry and authenticate K1 preimages in the formal-source package |
| public-coin law | publish a PIR denotational kernel | bind the structural references to a distribution in Analysis |
| outcome map | publish a provider-neutral owner map | require a total map in each Analysis provider binding |

No option is preferred by this package. The distinct candidate identities
demonstrate that selecting a PIR-owned option after publication would require
another rotation.

## Foundation boundary and integration slots

The active Foundation lane owns the exact-natural byte-bound decision. If it
aligns the Python evaluator to the already published law source, the common
16-profile cone above is complete. If it changes the Foundation law source,
the semantic regime and all 18 profile identities rotate. This package records
both consequences and selects neither.

The candidate also reserves explicit input slots for the Fresh run schema,
family-local Fiat--Shamir views, integrated provider audit, Foundation edge
result, and current gate-reclosure lane. Missing lane results preserve `Hold`;
they are not replaced with guessed positive or negative findings.

## Evidence boundary

The frozen result contains 23 findings: 20 bounded positive/refusal controls,
two `CannotAnswer` decisions, and one publication `Hold`. It establishes
profile-source compilability, finite identity-rotation topology, one translated
Schnorr carrier, one endpoint Terminal fixture, and exact open-choice effects.

It does not establish target publication, a normative identity, complete
admission, a refinement theorem, implementation correspondence, protocol
soundness, Fiat--Shamir security, provider theorem applicability, backend
correctness, or deployed-verifier validity.
