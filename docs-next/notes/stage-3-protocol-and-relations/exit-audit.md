# Stage 3 exit audit

> **Document kind:** Temporary Stage 3 documentation exit-gate record
> **Document state:** CLEAN and CLOSED on the exact snapshots recorded below
> **Provisional owner:** `project`
> **Authority:** None. This record audits documentation closure. It cannot make
> the selected target normative, admit a subject, mint authority, establish an
> implementation or property result, authorize migration or cutover, or
> activate Stage 4A or Stage 4B.
> **Audited:** 2026-08-22
> **Scope:** The promoted Stage 3 durable pages, the complete temporary Stage 3
> package, its two downstream entry contracts, and their durable routes.
> **Disposition:** Retain with this temporary package until the downstream
> handoffs and still-needed rationale have durable owners; delete it under the
> package-level gate before `docs-next/` authority cutover.

## 1. Exit verdict

**CLEAN and CLOSED.** The Stage 3 semantic selection, seven promoted durable
bodies, complete temporary package, two downstream handoffs, four downstream
indexes, durable routes, documentation manifest, and mechanical documentation
checks have no remaining exit blocker on the exact snapshots audited here.

The four items held open during the provisional audit closed as follows:

| Provisional blocker | Final closure |
|---|---|
| Validation-matrix refreeze | Independently re-audited and recorded at SHA-256 `947d963c0d5c926e6901415cc78701404ae9e8d42db3052b285daad29a695b7a` |
| Stage 4A/4B cross-handoff closure | Both repaired contracts passed an independent semantic and mechanical audit at the hashes in Section 2 |
| Downstream index reconciliation | Analysis, Compiler, OIR, and Realization indexes passed an exact-snapshot audit against the final handoffs |
| Final convergence reconciliation | The convergence record now declares the whole bounded Stage 3 package CLEAN and CLOSED at the exact hash in Section 2 |

This result exits only the bounded Stage 3 design-research program. It neither
starts a later stage nor widens any semantic or operational claim.

## 2. Snapshot and frozen-integrity accounting

The frozen Stage 3.4 artifacts were recomputed from the files on disk rather
than inferred from filenames or earlier notices.

| Artifact | Recorded closure SHA-256 | Observed SHA-256 | Result |
|---|---|---|---|
| [Integrated target](target-semantic-model.md) | `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b` | `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b` | Exact match |
| [Candidate portfolio](candidate-models.md) | `ce4f71e88741f71d126c81ce8afeb2cb29da83f856bb13fdf032a702756b9923` | `ce4f71e88741f71d126c81ce8afeb2cb29da83f856bb13fdf032a702756b9923` | Exact match |
| [Scenario results](scenario-results.md) | `ba630d5d860c7f590eb375fe88b23ab30270d7385686e02b86da2adee268819a` | `ba630d5d860c7f590eb375fe88b23ab30270d7385686e02b86da2adee268819a` | Exact match |
| [Validation matrices](validation-matrices.md) | `947d963c0d5c926e6901415cc78701404ae9e8d42db3052b285daad29a695b7a` | `947d963c0d5c926e6901415cc78701404ae9e8d42db3052b285daad29a695b7a` | Exact match after final re-audit |

The handoff, downstream-route, and convergence closure was audited on these
exact non-authoritative documentation snapshots:

| Closure record | Observed SHA-256 | Result |
|---|---|---|
| [Stage 4A entry contract](stage-4a-entry-contract.md) | `f92a5ffc8d583d603b1e15aac6f73b1d147636c3fc1a13bf6fbdfb840942b7d8` | CLEAN |
| [Stage 4B entry contract](stage-4b-entry-contract.md) | `062efbd41caa9d6dfaa933816204027b2803ea3896abe886a1fb48285fc2fd12` | CLEAN |
| [Analysis index](../../analysis/README.md) | `6b720daf004497b7b780f08325219d12e6f8907232a961d1b90b674997be6a4c` | CLEAN |
| [Compiler index](../../compiler/README.md) | `386ec771564964dabbb71618e9c728141aeecf569c881e6ee71db9cf15081ac1` | CLEAN |
| [OIR index](../../oir/README.md) | `92fa3bf238baf85eee122cbbb947c326ffdbf364e53bd9741e88a79cb7363bdf` | CLEAN |
| [Realization index](../../realization/README.md) | `16f26325689e65ab5b2aca52185f7a1af55e8806e263fa270067fb7dfdaf0d70` | CLEAN |
| [Convergence record](convergence.md) | `1ae0bbae0dce83b6159b5b4e888b8b6ff349caab385fbd61e294d3492f44c584` | CLEAN and CLOSED |

The target file is intentionally immutable at the recorded hash. Its header is
therefore a narrow historical-snapshot exception: it still describes selection
as pending and its local disposition does not contain the final package
deletion trigger. Editing that header would invalidate the audited semantic
basis. Current selection state is instead owned by the
[convergence record](convergence.md) and durable pages; deletion is owned by the
[package index](README.md), [absorption record](absorption-record.md), and this
exit record. This exception grants the frozen target no durable authority and
creates no durable dependency on it.

The handoff pages and downstream indexes are not semantic authority and were
not part of the Stage 3.4 frozen set. Their hashes above identify the exact
documentation snapshots checked for boundary consistency; they do not turn
those pages into admitted subjects or live authority.

## 3. Package and deliverable accounting

Including this page, the package contains exactly 21 Markdown pages: 16 in the
package root and five in `cases/`. The [package index](README.md) inventories
every root work product by role; the [case index](cases/README.md) inventories
all four nested dossiers. Together those two indexes cover every package page
without making an incubation page durable.

The [absorption record](absorption-record.md) accounts for all 15 substantive
research inputs, separately accounts for both downstream handoffs, names every
durable destination, and retains one package-level deletion gate. The 14
charter-required work products have the following complete trace:

| Charter work product | Closing work products and durable destination |
|---|---|
| 1. Current reconstruction and correspondence | [Current Protocol and PIR](current-protocol-pir.md), [current Relations and seams](current-relations-and-seams.md), and [joint synthesis](current-model-synthesis.md) |
| 2. Native forces, cases, and equal-resolution alternatives | [Design forces](design-forces-and-opportunities.md), the [four case dossiers](cases/README.md), and [five candidates](candidate-models.md) |
| 3. Complete Protocol semantics and closed canonical PIR | [Frozen target](target-semantic-model.md), [Protocol model](../../pir/protocol-model.md), and [Canonical PIR](../../pir/canonical-pir.md) |
| 4. Protocol-to-carrier correspondence and information-loss ledger | [Frozen target](target-semantic-model.md) and [Canonical PIR](../../pir/canonical-pir.md) |
| 5. Identity, dependency, authority, outcome, replay, checker, and trust matrices | [Validation matrices](validation-matrices.md) |
| 6. Complete Interface boundary | [Interface and Plan specification](../../pir/interfaces-and-plans.md) |
| 7. Bounded Plan and `PlanRealizes` contract | [Interface and Plan specification](../../pir/interfaces-and-plans.md) and [Stage 4B entry](stage-4b-entry-contract.md) |
| 8. Relations ontology, ingress, artifact interpretation, and correspondence | [Relation model](../../relations/relation-model.md) and [Protocol correspondence](../../relations/protocol-correspondence.md) |
| 9. Fresh-to-Fiat--Shamir construction and `FSCompile` handoff | [Fiat--Shamir and composition](../../pir/fiat-shamir-and-composition.md) and [Stage 4A entry](stage-4a-entry-contract.md) |
| 10. Semantic Protocol/Core composition | [Fiat--Shamir and composition](../../pir/fiat-shamir-and-composition.md) |
| 11. Relation, observation, effect, closure, refusal, and consumer matrices | [Validation matrices](validation-matrices.md) and [frozen target](target-semantic-model.md) |
| 12. Scenario, opportunity, and falsification results | [Scenario results](scenario-results.md), [design forces](design-forces-and-opportunities.md), and [candidate portfolio](candidate-models.md) |
| 13. Gap, convergence, promotion, and absorption | [Current-to-target gap](current-to-target-gap.md), [convergence](convergence.md), and [absorption record](absorption-record.md) |
| 14. Separate Stage 4A and Stage 4B entries | [Stage 4A entry](stage-4a-entry-contract.md) and [Stage 4B entry](stage-4b-entry-contract.md) |

No temporary file is promoted merely by appearing in this trace. Durable
meaning resides only in the owning pages named below.

## 4. Durable ownership, routes, and manifest closure

The selected result is split across seven non-overlapping durable owners:

| Durable page | Owner | Stage 3 responsibility |
|---|---|---|
| [Protocol and Relations Architecture](../../project/protocol-and-relations-architecture.md) | `project` | Integrated topology, selection rationale, costs, capabilities, alternatives, reversal triggers, nonclaims, and later-stage split |
| [Protocol Semantic Model](../../pir/protocol-model.md) | `pir` | Core, Protocol, execution, failures, terminals, obligations, admission, and views |
| [Canonical PIR](../../pir/canonical-pir.md) | `pir` | Closed MLIR carrier, semantic bijection, authentication, admission, information-loss boundary, persistence, and replay |
| [Protocol Interfaces and Prover Plans](../../pir/interfaces-and-plans.md) | `pir` | Independent Interface and Plan subjects, codecs, admission, `PlanRealizes`, exports, and placement constraints |
| [Fiat--Shamir and Core Composition](../../pir/fiat-shamir-and-composition.md) | `pir` | Transcript construction, Fresh-to-FS checking, semantic Core composition, maps, outcomes, and replay |
| [Relation Model](../../relations/relation-model.md) | `relations` | Relation subjects, dependencies, ingress, binding, artifact interpretation, grounding, and satisfaction boundary |
| [Protocol Correspondence](../../relations/protocol-correspondence.md) | `relations` | Structural and instance correspondence questions, checked results, capabilities, views, and replay |

The architecture page routes directly to all six exact semantic owners. The
PIR and Relations indexes route their local pages, and the project/root maps
preserve the Stage 1--3 dependency chain and current-authority warning. The
[documentation manifest](../../project/documentation-manifest.md) contains 29
entries, exactly matching the 29 durable Markdown pages in `docs-next/`, with
no duplicate, missing, or extra path and with kind and owner metadata matching
the page headers.

No durable page depends on an individual Stage 3 work product. The one allowed
navigation edge is from the durable temporary-workspace index
[`notes/README.md`](../README.md) to this package index; it exposes package
status and deletion routing, not semantic authority.

## 5. Stage 4 handoff status

The two handoffs preserve one shared Stage 3 boundary while assigning distinct
later authority:

- [Stage 4A](stage-4a-entry-contract.md) routes Analysis before Compiler. It
  requires admitted purpose-specific views, exact question/model/theorem/rule
  and assumption bases, qualified judgments, exact Relations, Fiat--Shamir,
  and composition seams, independently admitted Compiler candidates, and a
  declared finite selection domain.
- [Stage 4B](stage-4b-entry-contract.md) routes OIR before Realization. It
  requires the exact admitted Protocol, Interface, endpoint role, and tagged
  Plan basis; separates `LocalOirValid` from `ProjectionCorrect`; requires
  occurrence- and path-sensitive output exposure/availability; and separates
  portable supplier binding, live supplier authority, effectful production,
  semantic checking, deployment, invocation, and execution.

Both pages state exact prerequisites, outputs, authority boundaries, and
nonclaims. They share Protocol/Interface/Plan identity, observation, occurrence,
failure, terminal, Plan-read, projection/property, and cross-branch
reconciliation rules. Neither page is an activation decision. Their independent
cross-audit is CLEAN at the exact hashes in Section 2, and the four downstream
indexes preserve the same separation without activating either branch.

## 6. Documentation validation

The following checks pass on the final set of 29 durable pages and 21 Stage 3
package pages.

| Check | Final result |
|---|---|
| Relative local file links and Markdown heading or line fragments | PASS; every audited target resolves |
| Package inventory | PASS; 21 pages are covered through the package and case indexes |
| Durable manifest | PASS; 29 actual durable pages equal 29 unique manifest entries |
| Durable dependency on individual Stage 3 notes | PASS; none, apart from the explicitly allowed package-index route described in Section 4 |
| Heading structure | PASS; exactly one H1 per page and no heading-level jump |
| Fenced blocks | PASS; backtick and tilde fences are balanced |
| Markdown tables | PASS; every table has a delimiter row and constant cell arity after escaped-pipe handling |
| Whitespace | PASS; no trailing whitespace and every page has a final newline |
| Header/manifest metadata | PASS; manifest kind and provisional owner equal the corresponding page headers |
| Stage 4 non-activation | PASS; both handoffs and every durable route require a separate activation decision |

These are documentation checks. They are not parser, compiler, protocol,
cryptographic, implementation-conformance, or runtime tests.

## 7. Docs-only scope

The audited Stage 3 deliverable and edit set is confined to documentation under
`docs-next/`. This exit-audit task creates and edits only this page. An existing
unrelated worktree modification at `emit/Cargo.lock` was observed, explicitly
excluded from the audit, and not touched. The audit therefore does not claim
that the entire worktree is documentation-only.

No code, build configuration, dependency, generated artifact, test fixture, or
runtime state is included in the Stage 3 exit result. No build, test, benchmark,
proof, or deployment result is reported by this page.

## 8. Exact nonclaims and retained gates

This audit does not establish:

- normative authority or cutover for any `docs-next/` page;
- implementation support, implementation correspondence, feasibility,
  completeness, migration order, compatibility, or cost;
- relation truth, witness validity, soundness, knowledge, completeness, zero
  knowledge, Fiat--Shamir security, composition preservation, or any theorem or
  quantitative bound;
- Analysis or Compiler correctness, OIR validity, projection correctness,
  output availability, realization, endpoint support, supplier correctness,
  deployment, invocation, runtime availability, Evidence appraisal, or
  consumer reliance; or
- Stage 4A or Stage 4B activation.

The package is not deleted by a clean exit. Deletion still waits for both
handoffs to be absorbed or retired, every still-needed rationale and reversal
condition to have a durable owner, the individual-note dependency check to
remain empty, post-removal documentation validation, and acceptance of Git
history as the discarded-detail record.

## 9. Exit conclusion

The promoted Stage 3 semantic model, ownership split, package accounting,
routes, manifest, explicit nonclaims, downstream handoffs, and documentation
structure pass the final exit gate. The whole bounded Stage 3 design-research
program is therefore complete and CLOSED on the exact snapshots in Section 2.

This closure does not activate Stage 4A or Stage 4B and does not authorize
normative cutover, implementation, migration, compatibility, theorem, property,
endpoint, realization, Evidence, or reliance claims. Any later branch still
requires its own explicit activation decision and independently owned results.
