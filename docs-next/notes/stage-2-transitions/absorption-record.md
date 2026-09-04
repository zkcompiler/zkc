# Stage 2 absorption record

> **Document kind:** Temporary promotion and deletion ledger
> **Document state:** Complete for Stage 2 closure; retained until later
> package absorption
> **Authority:** None. This record shows where reviewed Stage 2 conclusions
> were promoted and which later owners must make their schemas exact. It does
> not make those targets normative, report implementation, authorize migration,
> or replace the owning durable pages.
> **Disposition:** Keep with the completed Stage 2 research package while its
> handoffs remain useful. Delete it with the package after all durable
> destinations no longer depend on temporary research routes.

## 1. Closure result

Stage 2 selected one cross-domain transition architecture and promoted it to
the durable [Transition and Bridge Architecture](../../project/transition-and-bridge-architecture.md).
The selected architecture is:

```text
domain-owned typed contracts
  + shared descriptive invariants
  + process-local capability lifecycle
  + direct recomputation for small closed predicates
  + selective producer/validator separation
  + purpose-specific durable results only for named consumers
```

It explicitly does not select a universal transition algebra, runtime object,
wire artifact, `TransitionId`, fact root, checker registry, capability type,
error type, or portable admission receipt.

The final research rationale is in [Stage 2 Convergence](convergence.md). The
complete selected edge inventory is in the
[Target Transition Catalog](target-transition-catalog.md), and the current
architectural delta is in the
[Current-to-Target Gap Map](current-to-target-gap.md). Those pages remain
temporary evidence and handoff material, not durable semantic owners.

## 2. Durable promotion ledger

| Reviewed conclusion | Durable destination | Promotion state | Remaining exact owner |
|---|---|---|---|
| Cross-domain hybrid, common contract discipline, mechanism selection, identity/capability/persistence rules, outcome model, composition classes, reversal conditions | [Transition and Bridge Architecture](../../project/transition-and-bridge-architecture.md) | Promoted as the selected non-normative Stage 2 architecture | Stages 3--7 instantiate domain schemas; Stage 8 reviews implementation conformance |
| Program position and dependency gate | [v0 Semantic Design Program](../../project/v0-design-program.md) | Stage 2 recorded complete; later updated through Stage 3 completion | Stage 4A and Stage 4B entry contracts are ready; neither branch is activated |
| Whole-system orientation and target backbone | [Candidate v0 Semantic Architecture](../../project/v0-semantic-architecture.md) | Updated to route to the selected Stage 1 and Stage 2 decisions | Later packages replace remaining candidate-level object details |
| Stage 1 subject decisions and their completed transition handoff | [Protocol IR Architecture](../../project/protocol-ir-architecture.md) | Historical Stage 2 entry retained; selected Stage 2 result linked | Stage 3 completes Protocol, Interface, Plan, and canonical PIR schemas |
| Shared-invariant extraction rule and serialization authority loss | [Foundation](../../foundation/README.md) | Boundary promoted; no universal runtime or domain predicate moved into Foundation | Later extraction requires two concrete domains with genuinely identical semantics |
| Protocol lifecycle, logical authentication/admission split, reopen, link, composition, Interface and Plan consumption | [PIR](../../pir/README.md) | Boundary promoted | Stage 3 defines exact grammar, identities, predicates, and capabilities |
| Relation-interface admission, optional artifact interpretation, and Protocol-at-Interface correspondence | [Relations](../../relations/README.md) | Boundary promoted | Stage 3 defines exact relation ontology, identities, views, and outcomes |
| Question evaluation, derivations, qualified judgments, successful negative results, `FSCompile`, and `PropertyTransport` | [Analysis](../../analysis/README.md) | Boundary promoted | Stage 4A defines exact questions, proof/checking systems, and judgment schemas |
| Successor proposal, PIR-owned target admission, exact checked edge, and bounded-domain selection | [Compiler](../../compiler/README.md) | Boundary promoted | Stage 4A defines transform families, validators, domains, objectives, and decisions |
| Interface- and tagged-Plan-closed projection; `LocalOirValid` versus `ProjectionCorrect` | [OIR](../../oir/README.md) | Boundary promoted | Stage 4B defines OIR grammar, projection relation, source maps, and outcome schemas |
| Exact supplier binding, live authority, production/check separation, deployment, invocation, occurrences, and partial effects | [Realization](../../realization/README.md) | Boundary promoted | Stage 4B defines concrete target, operation, effect, and capability contracts |
| Observation, Evidence record, policy appraisal, and consumer-owned reliance | [Evidence](../../evidence/README.md) | Boundary promoted | Stage 6 defines exact record, assessment, policy, trust, freshness, and reliance schemas |
| Cross-domain bridge ownership and dependency graph | [Information Architecture](../../project/information-architecture.md) | Promoted | Later owners update the map only through reviewed boundary changes |
| Navigation and durable inventory | [`docs-next/` index](../../README.md), [Project index](../../project/README.md), and [Documentation Manifest](../../project/documentation-manifest.md) | Promoted | Maintain as documents are added or retired |

“Promoted” here means the non-normative target architecture is recorded by its
durable design owner. It does not mean that a normative specification, public
API, wire format, checker, implementation, proof, or conformance result exists.

## 3. Research-input disposition

| Temporary input | What was retained | What was not promoted as authority |
|---|---|---|
| [Current Transition Catalog](current-transition-catalog.md) | Current lifecycle strengths, exact observed boundary tensions, code/spec/test correspondence, and architectural gaps | Current class names, fused operations, carrier labels, or retained broad environments as target semantics |
| [Lifecycle Spine](lifecycle-spine.md) | Five-state lifecycle, exact closure, authentication/admission split, capability loss at bytes, admitted-only official persistence, and distinct link/composition | One public API per logical state, one traversal per predicate, or a universal artifact lifecycle implementation |
| [Semantic Bridges](semantic-bridges.md) | Separate relation ingress, correspondence, property analysis, checked change, FS construction, `FSCompile`, and `PropertyTransport` | A universal relation, automatic property preservation, or compiler ownership of Analysis judgments |
| [Endpoint and Operational Bridges](endpoint-operational-bridges.md) | Explicit Interface/tagged Plan projection, local versus source-relative OIR authority, supplier/realization/operation splits, effect and reliance chain | Complete OIR, backend, deployment, invocation, or Evidence schemas |
| [Transition and Checking Models](cases/transition-and-checking-models.md) | Layered acceptance, validator economy, capability locality, byte-versus-semantic identity, and evidence/appraisal/reliance distinctions | Wholesale adoption of any external compiler, certificate, capability, artifact, or attestation model |
| [Candidate Frameworks](candidate-frameworks.md) | Equal-resolution alternatives, evaluation vocabulary, opportunity tests, and falsifiers | Candidate B as a v0 center and any claim that one candidate mechanism fits every edge |
| [Cross-Case Synthesis](cross-case-synthesis.md) | A + C + selective D hybrid, shared versus owned rules, persistence posture, and mechanism selection | A universal runtime algebra or portable heterogeneous transition artifact |
| [Scenario Results](scenario-results.md) | Twenty-six integrated scenarios, twelve laundering/failure probes, enabled opportunities, and remaining downstream falsifiers | Proof that exact later schemas or validators are feasible or implemented |
| [Target Transition Catalog](target-transition-catalog.md) | Complete architectural transition families, closure/regime/checker matrices, owner seams, and deliberate deferrals | Final public symbols, error enums, wire fields, hashes, certificate schemas, or code organization |
| [Current-to-Target Gap Map](current-to-target-gap.md) | Keep/reframe/new/retire architectural classification and later ownership | Migration order, compatibility constraint, implementation priority, or authorization to remove current surfaces |
| [Stage 3 Entry Contract](stage-3-entry-contract.md) | Exact unopened next-stage intake, deliverables, scenarios, seams, exit gate, and reopening procedure | Stage 3 activation or a preselected Stage 3 schema |

## 4. Candidate decisions

| Candidate | Stage 2 disposition | Reopening trigger |
|---|---|---|
| A: domain-owned typed contracts | Selected as the global ownership baseline, strengthened by a shared lintable descriptive catalog | Domain contracts cannot remain coherent without genuinely shared executable semantics |
| B-local: universal typed algebra | Not selected as the v0 semantic center; typed references and introspection were retained | Several important pure relations share semantics, laws, authority, and a real generic consumer |
| B-wire: universal transition artifact | Not selected | A named heterogeneous cross-process consumer, stable schemas, independent checkers, retention window, and clear advantage over domain results appear |
| C: capability-centric lifecycle | Selected for Protocol admission and other process-local authority gates | Capability lifetime or reconstruction cannot be made explicit across real language, thread, FFI, plugin, or process boundaries |
| D: proposal plus validation | Selected per edge only when validation is materially smaller, more stable, or independently implementable | A validator duplicates the producer, requires unavailable private state, cannot report incompleteness, or has no benefiting consumer |
| Direct recomputation | Selected first for small closed predicates | Rechecking becomes unavailable or uneconomic for a named consumer |
| Trusted producer boundary | Retained as an explicit honest fallback | A smaller sound checker or verified producer becomes available |

The candidates are mechanism and ownership choices, not public type names.
Their reversal triggers remain durable in the owning architecture decision.

## 5. Deliberate downstream deferrals

The following were assigned, not forgotten:

- Stage 3 owns exact Protocol/Core/PIR, Interface, Plan, relation,
  authentication/admission, FS construction/bridge, and composition schemas.
- Stage 4A owns complete Analysis and Compiler questions, derivations,
  judgments, transform relations, validator placement, selection, and
  property-transport schemas.
- Stage 4B owns complete OIR, projection, supplier, realization, deployment,
  invocation, effect, and raw-observation schemas.
- Stage 5 tests joined cross-system capability and composition needs and is the
  principal reopening point for a stronger portable package or new named
  independent consumer.
- Stage 6 owns Evidence records, appraisal, trust/freshness policies, and
  consumer reliance.
- Stage 7 performs normative ownership consolidation and authority cutover.
- Stage 8 maps the selected normative model to implementation architecture and
  conformance work.

No deferral permits an ambient read, generic validity result, serialized local
authority, source coverage inferred from source-free targets, automatic
property transport, pure modeling of unexplained effects, or policy backflow.

## 6. Stage 2 exit-gate accounting

| Exit requirement | Closing artifact |
|---|---|
| Every current and selected target edge is cataloged | [Current Catalog](current-transition-catalog.md) and [Target Catalog](target-transition-catalog.md) |
| Inputs, authority, identity effect, outcome, capability, replay, and residual trust are explicit | Target catalog plus the three domain dossiers |
| Functional closure and semantic-regime rules are complete | [Lifecycle Spine](lifecycle-spine.md), [Cross-Case Synthesis](cross-case-synthesis.md), and durable architecture |
| Interface and ProverPlan seams are bounded | Target catalog, endpoint dossier, durable architecture, and [Stage 3 Entry](stage-3-entry-contract.md) |
| Checker and witness placement was compared per edge | External cases, candidate frameworks, synthesis, and target checker matrix |
| Scenario and opportunity evaluation covers the selected candidate | [Scenario Results](scenario-results.md) |
| Current-to-target delta and later owners are explicit | [Gap Map](current-to-target-gap.md) |
| Reviewed conclusions have durable destinations | This ledger and the destinations in Section 2 |
| A clean-room next-stage gate exists | [Stage 3 Entry Contract](stage-3-entry-contract.md) |
| Normative, implementation, migration, and proof non-claims remain explicit | Every closing artifact and durable architecture |

Stage 2 therefore satisfies its architectural exit condition. Stage 3 was
later explicitly activated through its own charter and has since completed;
this sentence preserves the Stage 2 gate rather than reopening it.

## 7. Retention and deletion gate

The package is complete but intentionally retained because later packages have
not yet absorbed all exact seam and research rationale. Before deletion:

1. Stage 3 must absorb its fixed intake, exact Protocol/Relations decisions,
   and any remaining reversal triggers into durable owners.
2. Later stages must own every still-relevant deferred schema or explicitly
   retire it.
3. Durable pages must no longer require links into this package.
4. The temporary inventory in [`notes/README.md`](../README.md) must be updated.
5. Route, heading, local-link, code-fence, manifest, and whitespace validation
   must pass after removal.

Git history retains the research record. The final documentation corpus should
retain the selected model, rationale, non-claims, deferrals, and reopening
conditions rather than this incubation layout.
