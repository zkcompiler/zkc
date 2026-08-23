# Documentation migration policy

> **Document kind:** Governance proposal
> **Document state:** Scaffold
> **Provisional owner:** `project`
> **Authority:** This policy describes the proposed migration process only.
> Existing documents retain their current authority until ratified cutover.

## 1. Objective

The migration should make semantic ownership, authority, dependencies, and
reader paths clearer without losing content or disguising semantic changes as
file moves. It is complete only when the new corpus is both structurally sound
and semantically reviewed.

This initial scaffold performs no content migration and no authority transfer.

## 2. Invariants

Throughout the migration:

1. current owners remain authoritative until one explicit cutover;
2. every existing normative section remains traceable to a new owner, an
   explicit removal rationale, or an unresolved item;
3. structural relocation and semantic modification are reviewed separately;
4. no implementation, test, or experiment silently decides intended semantics;
5. no normative statement becomes a current support claim through migration;
6. current, target, provisional, reserved, deferred, and observed content stay
   visibly distinct;
7. public reader links continue to resolve or receive deliberate redirects;
8. private research and planning records are not promoted merely because they
   informed a public document; temporary public-ready design notes have no
   authority and must be absorbed and deleted under their workspace contract;
   and
9. unrelated user changes in the worktree are preserved.

## 3. Migration stages

### Stage A: authority and content inventory

Build one section-level ledger containing:

```text
current source and heading
current authority class
semantic subject
candidate new owner
dependencies and consumers
disposition: move, split, summarize, supersede, or unresolved
known duplication or conflict
```

The section-level migration ledger belongs in the private development
repository because it contains raw research and review history. Only reviewed,
durable ownership and provenance results are promoted into the public
scaffold. A bounded redesign candidate or falsification question may instead be
preserved temporarily under [`notes/`](../notes/README.md) when it is written
for public review, declares no authority, and has an explicit deletion
contract. That exception does not permit raw review logs or task queues.

The inventory must cover normative specifications, architecture, status,
roadmap, formalization, evaluation indexes, guides, and relevant repository
policy. It should inspect implementation only to understand real boundaries and
terminology, never to confer normative authority.

### Stage B: boundary research

Reconstruct and openly explore the proposed domains against specifications,
public interfaces, artifact lifecycles, identities, change boundaries, and
consumers. For each material boundary, compare preservation, completion or
alignment, structural redesign, and capability-expanding alternatives. Record
what each candidate enables or forecloses as well as split, merge, promotion,
and rename proposals. A boundary may change because a better abstraction or
valuable capability is discovered even when no current scenario fails.

Ratify the domain map before bulk movement. Target design drafts may develop
during research, but they are not a lossless structural migration. Raw working
research records remain private. Public-ready redesign candidates,
opportunities, alternatives, and deliberately open architectural questions may
remain in the temporary notes workspace until their owner-level review is
complete. Durable public pages carry only reviewed conclusions and
intentionally retained open architecture.

### Stage C: lossless structural draft

Move or copy content into the proposed owners with minimal semantic editing.
Preserve source provenance and mark unresolved conflicts. Split mixed documents
along authority boundaries, but do not close design gaps inside the same change.

The result is a shadow corpus. The current corpus still governs.

### Stage D: semantic review and closure

Review each owning specification as a coherent contract. Resolve omissions,
contradictions, duplicated definitions, ambiguous identities, and missing
non-claims through explicit semantic changes. Review architecture and decisions
separately from normative clauses.

After a specification area is coherent, compare the implementation and tests
against it. Classify each surface as conforming, bounded, partial, extension,
divergent, absent, or unverified. Do not edit the specification merely to make
the classification look better.

### Stage E: shadow validation

Validate:

- exactly one normative owner per definition;
- complete old-to-new provenance;
- domain README ownership and dependency consistency;
- manifest, link, and reachability integrity;
- explicit authority and document-state metadata;
- global status claims against bounded evidence;
- roadmap references against decisions and domain boundaries; and
- absence of private development material, the temporary `notes/` workspace,
  or empty placeholder structure.

### Stage F: ratified cutover

Cutover is one deliberate authority transition, not a gradual inference from
file freshness. The cutover change must:

1. declare the new root reading map authoritative;
2. assign each normative surface its final owner;
3. update repository and contribution routing;
4. update or redirect all stable public links;
5. retire the shadow/provisional banners;
6. preserve an accessible migration map for historical links; and
7. state exactly which old pages are replaced, retained, or removed.

Only after this change may `docs-next/` replace `docs/` or be renamed.

## 4. Semantic-change discipline

A semantic change includes any change to an artifact's meaning, schema,
identity preimage, admission condition, refusal, judgment, assumption,
conclusion, bound, boundary contract, or normative lifecycle.

Such a change requires:

- a named owning domain and page;
- explicit before and after meaning;
- affected dependencies and consumers;
- rationale and alternatives where the choice is architectural;
- implementation and evidence impact classified separately; and
- focused review independent of file movement.

Editorial normalization, link repair, and relocation should remain mechanical
where possible so reviewers can see the semantic delta.

## 5. Content provenance

The eventual migration ledger is the audit trail for completeness. One source
section may map to several new owners, and several duplicate sources may map to
one owner. Every row records why.

For normative content, provenance ends only when the new owner is reviewed and
the source is explicitly superseded. A missing row is a migration defect. A
copied paragraph with two live owners is also a defect.

The ledger is a migration artifact, not permanent semantic authority. Its
durable public residue should be the final manifest and any redirects needed
for readers.

## 6. Verification policy

During the scaffold phase, verification checks only documentation mechanics:

- every directory has a README and no directory is empty;
- every page is reachable from the root or manifest;
- relative file and heading links resolve;
- every temporary note appears exactly once in `notes/README.md`, while no
  individual working note appears in the durable manifest;
- no durable page links directly to an individual temporary note;
- no trailing whitespace or missing final newline exists;
- the public-tree boundary check passes; and
- the workspace diff contains only intended new documentation files.

Passing these checks says nothing about semantic completeness. Semantic
coverage becomes a separate gate after the section-level inventory exists.

The current path guard was written for `docs/` and cannot be assumed to cover a
parallel root. Before cutover, it must be extended or generalized so that
private research, planning, review, and archive paths cannot bypass the same
public-tree policy under the final documentation root.
