# Documentation governance

> **Document kind:** Governance proposal
> **Document state:** Scaffold
> **Provisional owner:** `project`
> **Authority:** This document governs only the design of `docs-next/` during
> research. It does not override the current
> [documentation rules](../../docs/README.md#documentation-rules).

## 1. Governing idea

Documentation is part of the system's authority structure. A page must make it
possible to tell whether it defines intended semantics, reports current
support, records evidence, explains architecture, preserves a decision,
orders future work, or teaches a workflow. Detail and proximity do not grant
authority.

Authority is question-relative, not a total ordering of pages.

| Question | Owning document kind |
|---|---|
| What must an artifact, operation, judgment, or consumer mean? | Normative specification |
| What does this checkout currently support? | Global status |
| What was observed for an exact subject and procedure? | Evidence record |
| How should the system be understood structurally? | Architecture |
| Why was a durable choice made? | Decision record, reflected in any affected specification |
| What is intended next? | Global roadmap |
| How does a reader perform a task? | Guide |
| Where is the owner? | Index or manifest |

## 2. Required page contract

Every durable page begins with a visible Markdown block immediately after its
title. It declares:

```text
Document kind
Document state
Owning domain
Authority
```

While this tree is a scaffold, `Provisional owner` satisfies the owning-domain
field without implying ratification.

A substantive page must also make its scope, dependencies, and non-claims
clear. A domain README additionally declares purpose, owned subjects,
non-ownership, upstream dependencies, downstream consumers, bridge ownership
when applicable or an explicit statement that it owns none, candidate internal
boundaries, and open split or merge questions.

Use visible Markdown rather than YAML front matter until a real documentation
tool consumes structured metadata.

## 3. Document kinds

### Governance

Governance defines documentation authority, manifest structure, change rules,
and migration or cutover procedure. It governs how owners are recorded; it
does not acquire the technical semantics of those owners. A governance proposal
has no authority over the current corpus until explicitly ratified.

### Normative specification

A specification owns intended meaning. It defines the exact subject, inputs,
preconditions, outputs, postconditions, identities, refusals, dependencies,
and non-claims needed for independent implementation and review.

- Use `MUST`, `SHOULD`, and `MAY` only where normative force is intended.
- Do not weaken intended semantics to match an incomplete implementation.
- Do not claim implementation support; link to global status.
- Name every external assumption, theorem, authority, adapter, and opaque
  predicate at its actual boundary.
- Keep carrier representation distinct from semantic meaning even when both
  are specified in the same domain.

### Architecture

Architecture explains component roles, data and control flow, trust boundaries,
and target structure. It may describe unimplemented design, but must label it
as target or open architecture and cannot override a specification.

### Decision record

A decision record preserves durable alternatives, choice, rationale, and
consequences. It does not silently amend semantics. An accepted semantic
decision changes the owning specification in the same ratified transition.
Public decision names use descriptive slugs; internal task numbers and private
shorthand do not become shipped terminology.

### Status

There is one global public status authority. It reports implemented and
exercised facets, names the checkout or verification point, cites evidence,
and distinguishes complete, bounded, partial, unavailable, and unverified
support. Domain status pages, if ever generated, are views rather than
competing owners.

### Roadmap or public plan

The global roadmap owns public dependency order and intended direction. It
does not report current capability and cannot be the only home of a durable
architectural decision. Internal queues, session plans, and review worklists
remain private development material.

### Design-research execution plan

A design-research execution plan may order the temporary reconstruction,
alternative exploration, convergence, and consolidation needed to produce a
candidate semantic model. It is not the product roadmap, does not authorize
implementation, and does not make its preferred design normative. The
scaffold keeps at most one cross-domain design-research execution plan; bounded
package charters remain temporary notes and are absorbed or deleted.

### Evidence record

An evidence record is authoritative only for its attributable record of an
exact producer-owned observation. The producing domain retains authority over
what the raw observation means and its completeness frontier. The record states:

- subject and content identity or revision;
- producer, issuer, or recording authority;
- inputs, configuration, environment, and procedure;
- observed result and covered facets;
- exclusions and failed or unattempted facets; and
- residual trust and reproduction instructions.

A test, receipt, citation, demonstration, or matching implementation does not
become a semantic definition or a broader proof through detail or repetition.

### Guide

A guide is an audience- and task-oriented projection across owning documents.
It may contain commands and examples. It must link to the current owner of any
schema, capability claim, or architectural rule it summarizes.

### Index or manifest

An index routes readers; a manifest inventories pages and owners. Neither
redefines the content it lists. `docs-next/` keeps one manifest so that
secondary reading maps do not become manually synchronized authority lists.

### Temporary design note

A temporary design note preserves a candidate, unresolved question, caution,
alternative, or falsification plan while the durable owner is being
reconstructed. It has no semantic, status, evidence, decision, or planning
authority. It may repeat context and compare incompatible alternatives, so it
cannot be cited as the basis of a durable rule.

Temporary notes may exist only under [`notes/`](../notes/README.md). Each note
must state its intended destinations and deletion trigger. Accepted conclusions
are rewritten into the exact durable owners; rejected or deferred conclusions
receive a rationale or roadmap destination where needed. Absorption never means
that a specification links back to the note.

## 4. Three independent state axes

Never compress these axes into one word such as “supported” or “valid”:

1. **Document state:** scaffold, draft, active, superseded, or retired.
2. **Normative surface maturity:** admitted, provisional, reserved, deferred,
   or deprecated, where the owning specification defines the exact meaning.
3. **Implementation state:** implemented, bounded, partial, absent, or
   unverified, owned only by global status and its cited evidence.

An admitted semantic contract may be unimplemented. A passing implementation
may exercise a provisional surface. A reserved name may have code experiments
without defining an accepted contract.

The baseline meanings for surface maturity are:

- **admitted:** the owning specification provides a complete intended contract;
- **provisional:** the corpus states a reviewable contract, but explicitly
  permits incompatible refinement before admission;
- **reserved:** a name, role, or boundary is held without a complete contract,
  so conformance cannot yet be claimed;
- **deferred:** the surface is explicitly outside the current normative scope;
  and
- **deprecated:** the surface remains recognized for a bounded transition but
  is not the forward contract.

An owning specification may add stricter criteria but must not silently give
these labels a contradictory meaning.

## 5. Ownership and duplication

### One definition, one owner

Every normative concept has one owning page and domain. Other pages may give a
short reader-oriented summary followed by a link. They must not copy tables,
schemas, or rule text that can drift independently.

A shared glossary indexes terms and their owners; it does not centralize all
definitions. Vocabulary entries live with the domain that gives them meaning.
Only common admission and extension mechanics belong in `foundation/`.

### Producer definitions and bridge contracts

The producer owns its object definitions. The domain that defines the newly
minted output role owns the cross-domain bridge and cites every input owner.
Each bridge has exactly one physical home even when both sides must review it.

Examples in the current hypothesis include PIR-to-OIR projection under `oir/`,
admitted-PIR property projection under `analysis/`, and property-judgment use
in selection constraints under `compiler/`.

Evidence-policy vocabulary may be owned by `evidence/`, but the consumer that
relies on a record owns its concrete acceptance or release decision. Evidence
cannot authorize its own use.

### Temporary-workspace exception

The durable documentation manifest lists [`notes/README.md`](../notes/README.md)
as the boundary and inventory authority for the temporary workspace. Individual
working notes are deliberately excluded from the durable manifest and must
appear exactly once in that local inventory. This is the only permitted second
inventory because its subjects are explicitly disposable rather than durable
documentation pages.

No durable page may depend on an individual working note. A root or governance
page may route readers to the temporary workspace index only. The entire
directory must be absent at cutover; Git history, accepted decisions, and
absorbed owner content preserve the useful record.

### Conflict handling

- `docs-next/` versus current `docs/`: current owners govern until cutover.
- architecture or guide versus specification: the specification governs
  semantics and the explanatory page is corrected.
- decision versus specification: the decision is not effective semantically
  until the owning specification is updated.
- implementation or test versus specification: record a conformance gap or a
  specification defect; do not silently choose the code.
- producer observation versus evidence versus status: the producer owns the
  bounded observation's meaning, Evidence owns its attributable bounded record
  and any policy-qualified appraisal, while status owns the public capability
  claim and must narrow it if support is inadequate.
- specification versus specification: treat the conflict as a defect. Do not
  resolve it by recency, file order, or broader title.

## 6. Judgment and claim discipline

Structural admission, relation correspondence, post-admission soundness,
knowledge, completeness, compiler legality and selection, endpoint validity,
execution results, and conformance evidence are distinct conclusions. A page
must name which one it establishes and which it does not.

In particular:

- authentication or admission does not establish relation satisfaction or
  cryptographic security;
- a conditional property judgment does not establish its hypotheses;
- completeness does not borrow soundness, and soundness does not imply zero
  knowledge;
- endpoint execution is not backend conformance;
- reference parity is evidence within its compared surface, not universal
  implementation correctness; and
- one successful run does not establish a family-wide property.

## 7. Naming, links, and style

- Use lowercase kebab-case filenames. Reserve `README.md` for directory
  entrypoints.
- Use one H1 per page and relative repository links ending in `.md`.
- Use descriptive headings. Number clauses only when a normative document
  needs stable formal references.
- Prefer links to a named owner and heading over unexplained section numbers.
- Do not casually rename headings that are cross-document link targets.
- Use code formatting for identifiers and literal values.
- Distinguish current, target, provisional, reserved, deferred, and open
  content in the sentence that makes the claim.
- Keep prose self-contained; private decision IDs and review shorthand do not
  appear in public text.

## 8. Change rules

When a documentation change alters meaning or ownership:

1. update the owning page first;
2. update the manifest and all affected reader routes;
3. update dependent summaries without copying the new definition;
4. update global status only if current implementation claims changed;
5. attach or update evidence only for observations actually rerun; and
6. preserve migration provenance until cutover is complete.

Moving text is not evidence that its new boundary is correct. Changing text
while moving it must be reviewed as a semantic change, not hidden inside a
structural reorganization.
