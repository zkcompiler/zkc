# Information architecture

> **Document kind:** Architecture proposal
> **Document state:** Scaffold
> **Provisional owner:** `project`
> **Authority:** Non-normative. This page proposes boundaries to investigate;
> it does not move authority from the current specifications.

## 1. Partitioning method

The documentation should resemble the semantic architecture, not the source
tree. A durable domain normally has:

- a coherent subject and vocabulary;
- a clear authority boundary;
- inputs and outputs that can be stated independently;
- a lifecycle or change cadence distinct from neighboring subjects;
- a recognizable set of upstream dependencies and downstream consumers; and
- enough internal material to benefit from one navigation entrypoint.

Page length alone is not a reason to split. A short page with a different
authority may need separation; a long, cohesive formal contract may remain
one document.

## 2. Proposed domains

| Domain | Provisional subject | Primary boundary guardrail |
|---|---|---|
| `foundation/` | Shared identity, authority, admission, lifecycle, encoding, extension, and evolution rules | Accept only genuinely cross-domain mechanisms; never absorb whole PIR or OIR vocabularies |
| `relations/` | External relation identities and interfaces, statement and witness ports, adapters, and correspondence | Do not claim relation satisfaction, witness generation, or source compilation |
| `pir/` | Protocol object, Open and Sealed PIR, structure, closure, composition, carrier, and sealing | Do not mirror MLIR or absorb property analysis, compiler search, or endpoint behavior |
| `judgments/` | Post-seal calculi for properties of authenticated subjects | Do not collect every domain-local operation formulated as a judgment |
| `compiler/` | Checked protocol transformations, finite search, constraints, objectives, and selection | Do not own relation compilation or endpoint/backend realization |
| `endpoints/` | PIR projection, OIR, verifier/prover semantics, and abstract execution | Stop at the canonical behavior and interface a realization must preserve |
| `realization/` | Supplier binding, emission, generated artifacts, deployment, invocation, and concrete runtime | Do not change endpoint semantics under the name of implementation |
| `evidence/` | Evidence objects, provenance, conformance facets, reproduction, policy language, and claim scope | Evidence supports claims but cannot define semantics, current public status, or its own acceptance |

`project/` governs the whole map. `guides/` provides reader journeys. Neither is
a semantic domain.

### Names intentionally not promoted

- `boundaries/` would collect bridges with different output authorities. Keep
  one global bridge map, but place each exact contract with its owner.
- `carrier/` would separate a representation from the semantic artifact it
  carries. Keep PIR carrier rules under PIR, OIR carrier rules under endpoints,
  and only identical shared mechanisms under foundation.
- `vocabularies/` would reproduce the current cross-domain catch-all. Place
  concrete entries with the domain that gives them meaning and keep only common
  admission discipline under foundation.
- `composition/` is currently a system view over several owned transitions:
  PIR link, endpoint projection, relation descent, property composition, and
  realization. Keep a project-level map and domain-local contracts.
- `registry/` and `artifacts/` remain candidate foundation subdomains until
  they demonstrate independent subjects and lifecycles.

## 3. Candidate dependency model

`foundation/` supplies common mechanisms but not domain meaning. PIR and the
relation-base contract define upstream subjects independently; post-seal
relation correspondence then consumes Sealed PIR. Judgments analyze
authenticated subjects. The compiler consumes PIR and selected judgment
capabilities to produce checked protocol changes. Endpoints consume any
admissible Sealed PIR; they do not require the compiler. Realization consumes a
fixed endpoint and binds it to concrete suppliers and runtime artifacts.
Evidence binds observations to exact subjects from every domain.

These arrows describe primary semantic production and consumption, not a
code-package import graph. A bridge page may cite both endpoints. For example,
the relation-to-protocol correspondence contract is physically owned by
`relations/` while citing definitions from both relations and PIR.

The compiler-to-PIR edge is a semantic loop: a transform result is new Open PIR
and crosses the ordinary seal boundary again. It is not permission for the
compiler to mint sealed authority privately.

Evidence dependencies are one-way. A receipt, test, or execution record may
support a claim about an artifact, but adding or removing that record does not
change the artifact's semantic identity.

## 4. Bridge ownership

Cross-domain material should not be gathered into one generic `boundaries/`
directory. Each bridge belongs to the domain that defines the newly minted
output semantic role.

| Bridge | Provisional owner | Boundary constraint |
|---|---|---|
| Sealed PIR + RelationContract + optional relation bytes to a correspondence result | `relations/` | PIR remains unchanged; the contract is post-seal and evidence-only relative to it |
| Open PIR to Sealed PIR | `pir/` | Common authentication primitives remain under `foundation/` |
| Static protocol composition (`link`) | `pir/` | Each component retains its cited domain definitions |
| Admitted PIR to property-analysis subject and facts | `judgments/` | PIR owns the authenticated facts it exposes |
| Judgment results to compiler constraints and objectives | `compiler/` | `judgments/` owns result meaning and derivation semantics |
| Sealed PIR to verifier or prover OIR | `endpoints/` | PIR owns projection obligations; endpoints owns realized coverage and OIR |
| Verifier endpoint to outer relation material (`descend`) | `relations/` | Endpoint identity and verifier semantics remain under `endpoints/` |
| OIR + supplier binding to an emitted artifact | `realization/` | OIR remains owned by endpoint semantics |
| Emitted artifact + resources and policy to a deployment binding | `realization/` | Emitted and deployed identities remain distinct |
| Deployment + invocation inputs to an operational run and result | `realization/` | Invocation values cannot change endpoint semantics |
| Abstract endpoint result or realized operational record to an evidence record | `evidence/` | The producer owns the raw result; the relying consumer owns acceptance policy |

Owning a bridge does not authorize redefining either endpoint. A bridge page
must list both source authorities, its new invariant, its refusals, and its
non-claims.

The current CheckContract and HoleContract boundary is intentionally
three-part:

- PIR owns each identity-bearing citation, protocol-facing ABI, and
  route-or-attachment meaning;
- endpoints owns projected `check_call` or `hole_call` behavior and abstract
  supplier requirements; and
- realization owns concrete supplier selection, binding, and execution.

The section-level inventory must test individual fields against this rule, but
no domain may silently acquire the complete contract by convenience.

## 5. Physical layout rules

### Domain first, kind second

The primary path answers “which semantic owner?” A secondary directory may
answer “what kind of page?” when that distinction aids navigation. Possible
local kinds include `spec/`, `architecture/`, `decisions/`, and `guides/`.

Do not create all kinds under every domain. Create a kind directory only with
durable content and a real navigation need. A single page can remain directly
under its domain and declare its kind in the page contract.

### Promote semantic subdomains carefully

Create a nested semantic directory when the topic has an independent subject,
authority, lifecycle, and more than one durable page. The new directory must
include a README and at least one substantive page in the same change.

Likely endpoint subdomains are projection, OIR programs, and abstract
execution. Likely realization subdomains are emission, deployment, invocation,
and runtime. They are candidates, not directories to pre-create now.

### Keep public planning bounded

The public tree carries one project roadmap and durable reader-facing design.
Domain work queues, migration scratchpads, review notes, and session plans stay
private. A domain-specific public plan is justified only when it describes a
stable, externally meaningful sequence that cannot be represented in the
global roadmap.

## 6. Split and merge tests

Split a document or domain when one or more of these remain true after editing:

- different sections answer to different authority classes;
- sections change independently and serve different consumers;
- one title hides more than one semantic subject or identity lifecycle;
- a bridge and both endpoint definitions compete inside the same page; or
- current, target, and evidence claims cannot be made unambiguous locally.

Merge or avoid a boundary when:

- the proposed child only mirrors a code namespace;
- it has no independent definitions or consumers;
- it would contain only an index pointing back to its parent;
- separating it would duplicate one normative invariant; or
- its name describes a mechanism used everywhere rather than a bounded subject.

## 7. Current decomposition hypotheses

The large current specifications suggest, but do not yet ratify, these moves:

- split common encoding and admission mechanics from PIR- and OIR-specific
  carrier semantics;
- distribute vocabulary entries to their semantic owners instead of moving the
  current vocabulary document wholesale into `foundation/`;
- keep PIR structural judgments such as formation, closure, seal, and link in
  `pir/`;
- separate shared property calculus, soundness, knowledge, completeness,
  assumptions, derivations, and PIR-fact projection within `judgments/`;
- separate generic compiler semantics from provider-specific transform
  families;
- keep endpoint projection and program semantics separate from target
  realization, deployment, invocation, and concrete execution; and
- keep global status concise by linking detailed provenance and reproduction
  records under `evidence/`.

## 8. Promotion and rename candidates

Research into the current architecture justifies one addition to the initial
proposal: `realization/`. OIR explicitly fixes endpoint behavior without being
a backend recipe, while emission, supplier binding, deployment, and invocation
have a different authority and lifecycle. Keeping them separate now prevents
`endpoints/` from erasing that semantic firewall.

The next candidates to reevaluate are:

- `pir/` to `protocol/` with PIR as a nested current representation, if the
  protocol semantic object becomes demonstrably carrier-independent;
- an internal split of `realization/`, if emitted artifacts, deployments,
  invocations, suppliers, and sessions acquire several independent normative
  identities and lifecycles;
- `artifacts/` or `representation/`, if common carrier semantics outgrow the
  strict admission rule for `foundation/`; and
- `judgments/` to `analysis/` or `property-judgments/`, or `evidence/` to
  `assurance/`, if the current names repeatedly attract out-of-scope material.

Promotion should follow the content inventory and authority analysis, not
anticipate them.
