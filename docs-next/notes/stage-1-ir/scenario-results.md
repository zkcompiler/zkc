# Stage 1 candidate scenario results

> **Document kind:** Temporary comparative research result
> **Document state:** Evaluation complete; convergence input
> **Authority:** None. This document selects a research recommendation for
> promotion, but does not itself define normative Protocol semantics, amend an
> identity grammar, or authorize implementation.
> **Disposition:** Promote the accepted architecture and exact decisions into
> their durable owners, retain rejected alternatives and reversal triggers in a
> durable decision record, then delete this temporary result at the documented
> Stage 1 cutover.

## 1. Question and result

This evaluation answers the scenario gate required by the
[first-wave synthesis](cross-case-synthesis.md#10-required-next-evaluation).
It compares four complete bundles rather than scoring isolated mechanisms:

- strengthened lifecycle quotient (`A*`);
- a distinct closed canonical MLIR PIR level (`B*`);
- a carrier-neutral complete semantic package (`D*`); and
- `B*` with authenticated purpose-specific projections (`B*+P`).

The preferred v0 architecture is **`B*`**. Purpose-specific projections are an
optional consumer boundary over `B*`, not another complete representation and
not a new semantic root. The selected bundle is:

```text
language-independent normative Protocol semantics
        +
MLIR authoring, import, analysis, and transformation workbench
        +
one distinct, small, closed canonical MLIR PIR level
        +
zkc-defined canonical semantic form and regime-qualified identity
        +
independent admission into an immutable AdmittedProtocol capability
        +
dependent ProtocolInterfaceId and separate ProverPlanId
        +
purpose-specific authenticated projections where a concrete consumer needs one
```

There is no complete portable Protocol package, compatibility dialect, or
second runtime object model in v0. This is a latest-responsible-point decision,
not a claim that such a boundary can never become useful. The
[portable IR dossier](cases/portable-ir-contracts.md#6-stage-1-hypotheses-produced-by-this-dossier)
finds that compatibility is a product promise with permanent costs, while the
current native audit identifies no independent full-Protocol consumer that
already requires that promise
([current correspondence](cases/current-zkc-correspondence.md#7-candidate-accidental-constraints)).

## 2. Decision vocabulary

The evaluation uses hard classifications, not weighted scores:

- **Pass:** the architecture gives the scenario one unambiguous semantic owner,
  identified inputs, and a fail-closed authority path. This says the design can
  express and check the required distinction; it is not evidence that a future
  implementation or theorem is complete.
- **Conditional:** the architecture is coherent only while a named global
  invariant, bridge, or consumer discipline remains true. Violating that
  condition is a candidate falsifier, not a minor implementation defect.
- **Refusal:** the requested artifact or conclusion is not derivable from the
  supplied information. Refusal is the required correct behavior when the
  scenario is intentionally underdetermined.
- **Fail:** the bundle identifies semantically different subjects as one,
  permits an unidentified input to affect a normative result, silently ignores
  unknown meaning, or cannot express a required valid case. A failure cannot be
  compensated by ergonomics or migration cost.

The strengthened candidates are intentionally the best coherent versions of
their families. Consequently, a candidate can pass the twelve examples yet
still lose the architectural decision because its conditions create a larger
permanent obligation or duplicate semantic authority.

## 3. Common semantic subject used in the comparison

The scenarios expose a common factorization that is independent of carrier:

```text
SemanticRegime R

InteractiveCore I
  = typed roles and semantic ports
  + typed event occurrences
  + mandatory causal dependencies
  + one identity-bearing total observable schedule
  + claim/reduction flow, checks, and terminal behavior

TranscriptConstruction K[I]
  = suite and initialization
  + event-to-transcript-atom interpretation
  + injective framing and codecs
  + I/O pattern, composition domain, and sampling rules

Protocol P
  = FreshPublicCoins(I)
    | FiatShamir(I, K[I])

ProtocolInterface PI[P]
  = external ABI names, encodings, and dispatch mapped to P's semantic ports

ProverPlan PP[P]
  = witness routes, private construction actions, local randomness,
    algorithms, and suppliers mapped to P's abstract prover obligations
```

The total schedule belongs to `InteractiveCore`, not first to the
Fiat--Shamir result. An interactive protocol is already an ordered
conversation; a transcript construction interprets that history rather than
creating its order. A causal or partial-order authoring form is therefore a
template from which closure selects a total schedule, not an admitted Core.
The theory dossier establishes why round structure, typed effects, and explicit
independence are semantic
([protocol semantics](cases/protocol-semantics-theory.md#2-interactive-protocols-and-fiat--shamir),
[ordered effects](cases/protocol-semantics-theory.md#4-ordered-effects-and-independence)).

Identity follows the subject dependency graph:

```text
CoreId              = H(core-domain, R, canonical(I))
ConstructionId      = H(construction-domain, R, CoreId, canonical(K))
ProtocolId          = H(protocol-domain, R, CoreId, FreshPublicCoins)
                    | H(protocol-domain, R, CoreId, FiatShamir, ConstructionId)
ProtocolInterfaceId = H(interface-domain, R, ProtocolId, canonical(PI))
ProverPlanId         = H(plan-domain, R, ProtocolId, canonical(PP))
```

The exact hash, encoding grammar, and domain constants are later normative
work. The Stage 1 decision is the dependency and sensitivity structure.
Diagnostic aliases are outside these identities; external ABI names are in
`ProtocolInterfaceId`; raw-byte transcript codecs are in
`TranscriptConstruction`; and a plan that changes verifier-visible events is
not merely another `ProverPlan`.

Fresh-coin and Fiat--Shamir Protocols therefore have different `ProtocolId`s.
They are connected by a named, theorem-backed `FSCompile` relation rather than
unrestricted equality. This preserves the quantitative and assumption-bearing
distinction found in the theory survey
([interactive and compiled denotations](cases/protocol-semantics-theory.md#22-interactive-and-compiled-denotations-differ)).

The semantic regime is inside every semantic identity domain. Identical
canonical payload bytes under different regimes do not name one semantic
subject. A raw content digest may still be retained as a transport fact, but it
is not a semantic ID.

## 4. Candidate bundles

### 4.1 `A*`: strengthened lifecycle quotient

`A*` keeps Open and admitted Protocol representatives in one MLIR PIR dialect
and defines identity through a canonical semantic encoder. It is strengthened
beyond the original baseline with:

- the common subject factorization above;
- a strict closed admitted profile;
- fail-closed handling of unknown canonical semantics;
- immutable admitted capabilities;
- explicit `ProtocolInterfaceId` and `ProverPlanId`; and
- consumer-specific views only after admission.

Its defining property is that admitted bodies need not be one physical normal
form. Multiple carrier representatives may have one `ProtocolId`. Therefore
every normative consumer must satisfy the quotient-congruence law:

```text
same ProtocolId and same separately identified inputs
    => same normative consumer result
```

The current relabeling observation shows this is a real, not hypothetical,
pressure: equal Protocol IDs can currently project to different endpoint and
relation-facing interfaces
([current correspondence](cases/current-zkc-correspondence.md#61-protocol-identity-does-not-close-endpointinterface-behavior)).

### 4.2 `B*`: closed canonical MLIR PIR level

`B*` reserves canonical `pir` for a small closed semantic vocabulary. Mutable
workbench modules may mix canonical PIR operations with authoring, synthesis,
or import dialects, but all noncanonical content must be exhaustively lowered
away before a candidate reaches the canonical boundary:

```text
mixed mutable workbench
  -> full closure and zkc-defined normalization
  -> closed canonical PIR candidate
  -> independent admission
  -> opaque immutable AdmittedProtocol
```

“Canonical” means one zkc-defined abstract semantic normal form: defaults are
materialized, sets are deterministically ordered, event positions and the
total schedule are explicit, references are closed and typed, and diagnostic
metadata is excluded. It does **not** mean that MLIR's best-effort generic
canonicalizer defines Protocol identity, nor that every MLIR text or bytecode
version must have identical bytes. The multi-level survey explicitly rules out
that interpretation
([canonicalization and transforms](cases/multilevel-mlir.md#44-canonicalization-and-transforms)).

MLIR full conversion can enforce the syntactic last-legal phase, but successful
conversion is not semantic admission, preservation, projection coverage, or a
property proof
([conversion legality](cases/multilevel-mlir.md#42-conversion-legality)).
Closure constructs a candidate; an independent admission path verifies the
normal form, dependency closure, regime, and identity before issuing the
capability.

### 4.3 `D*`: carrier-neutral complete semantic package

`D*` materializes the same normative factorization as a complete
language-neutral package. That package is the primary runtime subject; MLIR PIR
is an authoring and optimization adapter. Independent implementations decode
and check the package directly.

This is coherent and gives the strongest immediate non-MLIR full-Protocol
boundary. It does not eliminate correspondence work: it makes the
MLIR-to-package bridge a permanent central transition. It also creates a
second complete schema before a concrete consumer or compatibility window
requires one. The ZK case study supports language-independent semantics while
specifically not deriving a second Rust semantic core from that requirement
([implication for MLIR](cases/zk-proof-adjacent-irs.md#11-implication-for-mlir)).

### 4.4 `B*+P`: `B*` with purpose-specific projections

`B*+P` retains `B*` as the only complete semantic subject and derives a minimal
authenticated projection for a named consumer and claim. Each projection must
bind at least:

- source `ProtocolId` and, where relevant, `ProtocolInterfaceId` or
  `ProverPlanId`;
- semantic regime and projection-schema identity;
- exact observation classes and facts retained;
- exact claim the projection is sufficient to check; and
- producer/checker version or a separately specified projection relation.

A projection cannot answer a new question merely because it is authenticated.
If the consumer needs the complete Protocol, it consumes admitted canonical PIR
or triggers reconsideration of `D*`; the view must not accrete into an unnamed
shadow IR.

## 5. Architecture hard gates

These gates are conjunctive. A conditional result is a durable risk, not half
a pass.

| Gate | `A*` | `B*` | `D*` | `B*+P` |
|---|---|---|---|---|
| Every normative result is a function of identified inputs | **Conditional:** all consumers must honor the semantic quotient and never read erased carrier facts | **Pass:** only normalized semantic content and separately identified inputs cross admission | **Pass:** the package can close all semantic inputs | **Pass:** `B*` closes the source; each projection closes its declared subset |
| Ordered interaction and observer classes are explicit | **Pass** if the admitted profile requires the total Core schedule and effect classes | **Pass** | **Pass** | **Pass** through the source; projections declare retained observers |
| Admission, projection, properties, plans, and realization are distinct judgments | **Pass** | **Pass** | **Pass** | **Pass** |
| Unknown meaning fails closed | **Conditional:** same-dialect authoring and admitted syntax require a perfect profile firewall | **Pass:** authoring-only content is illegal at the canonical boundary | **Pass:** the package schema and dependency policy reject it | **Pass:** both canonical source and view schema reject it |
| Meaning is regime-qualified and independent of transport | **Pass** | **Pass** | **Pass** | **Pass** |
| Named transform relations replace unqualified equivalence | **Conditional:** validators must operate on the quotient, not incidental representatives | **Pass:** source and target normal forms are exact subjects | **Conditional:** both MLIR-to-package and package evolution need checked correspondence | **Pass:** source transforms remain `B*`; projection has its own scoped relation |
| An independent consumer can inspect no more authority than it needs | **Conditional:** it must implement the quotient and admitted subset | **Pass:** a small canonical checker need not import the optimizing compiler | **Pass:** this is `D*`'s strongest case | **Pass:** narrow consumers receive exact minimal views |
| One complete semantic authority exists per subject | **Pass** if the encoder is the only quotient authority | **Pass** | **Conditional:** normative specification, package schema, and MLIR adapter can drift into dual authority | **Pass** if projections remain derived and claim-scoped |

`B*` is the only bundle that passes every architecture gate without already
requiring a second complete schema or a system-wide congruence discipline.

## 6. Twelve-scenario evaluation

### 6.1 Equal authoring forms with one intended Protocol

**Required behavior.** Locations, diagnostic aliases, default spelling, and
declared representation-neutral ordering differences may converge to one
`ProtocolId`. A difference in an identified observer, external interface,
construction, or plan must not be erased accidentally. The native audit shows
that current sealed PIR is an equivalence-class representative rather than a
physical normal form
([current correspondence](cases/current-zkc-correspondence.md#62-sealed-pir-is-a-representative-not-a-physical-normal-form)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Conditional.** The canonical encoder can identify the forms, but every downstream consumer must be congruent with that quotient. One carrier field read after erasure falsifies the bundle. |
| `B*` | **Pass.** Closure maps both authoring forms to one canonical semantic normal form; independent admission authenticates that subject. |
| `D*` | **Pass.** Both adapters must produce the same canonical package. The bridge is the correspondence obligation. |
| `B*+P` | **Pass.** The source converges under `B*`; projections are functions of the admitted subject and identified auxiliary subjects only. |

### 6.2 One Protocol core with different external interfaces

**Required behavior.** Canonical semantic ports stay in the Core while ABI
names, encodings, dispatch, and external relation wiring produce different
dependent `ProtocolInterfaceId`s. `ProtocolId` may remain the same; projected
OIR identities can differ because they consume `(ProtocolId,
ProtocolInterfaceId, role)`. Presentation-only aliases remain diagnostic.

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Conditional.** The explicit interface subject repairs the known label leak only if raw representative labels are inaccessible to projection and Relations. |
| `B*` | **Pass.** The canonical Core exposes positional typed ports; external interface data cannot enter by ambient carrier lookup. |
| `D*` | **Pass.** The package represents the dependency explicitly, provided transcript codecs are classified under construction rather than mislabeled as ABI. |
| `B*+P` | **Pass.** Interface-bound endpoint views authenticate both IDs and cannot masquerade as Protocol-only projections. |

### 6.3 One verifier behavior with several prover plans

**Required behavior.** Several plans may realize the same abstract prover
obligations without changing verifier-visible events, proof ABI, or
`ProtocolId`. Each has a distinct `ProverPlanId`; `PlanRealizes` is a separate
judgment. If a plan changes an observable message, it denotes a new Protocol or
Interface rather than a plan variant. This distinction is supported by the ZK
survey's separation of relation, witness construction, and full proof protocol
([Noir ACIR and Brillig](cases/zk-proof-adjacent-irs.md#41-relation-versus-witness-construction)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Pass** only in its strengthened form, which removes plans from Protocol identity and forbids consumers from recovering them from the representative. |
| `B*` | **Pass.** Canonical PIR owns abstract prover obligations; separate plan subjects bind to them. |
| `D*` | **Pass.** The package must preserve the same split rather than publishing one privileged honest-prover algorithm as Protocol meaning. |
| `B*+P` | **Pass.** A plan-checking view may bind `ProtocolId` and `ProverPlanId`; verifier-only views omit plan-private facts. |

### 6.4 Interactive and Fiat--Shamir constructions over one core

**Required behavior.** One `CoreId` may support fresh-coin and several
Fiat--Shamir Protocols. Each compiled construction has its own `ProtocolId` and
exact `ConstructionId`; `FSCompile` carries theorem, assumptions, parameters,
and quantitative deltas. The total observable schedule remains in the Core.

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Pass** if the quotient includes all schedule and construction-sensitive distinctions and consumers cannot read alternative authored order. |
| `B*` | **Pass.** Closure authenticates one ordered Core, and construction interpretation produces separately identified Protocols. |
| `D*` | **Pass.** Carrier neutrality neither weakens nor strengthens the required semantic relation. |
| `B*+P` | **Pass.** A theorem checker can receive a scoped construction view, but the view does not turn `FSCompile` into equality. |

### 6.5 SSA-independent operations with wire or check effects

**Required behavior.** Absence of an SSA edge does not authorize reordering.
The protected observation classes include at least `FS`, `WIRE`, `PUBLIC`,
`CHECK`, `ARTIFACT`, `CLAIM`, and `TERMINAL`. A checked independence relation
must name which observers it preserves. The theory dossier gives concrete
counterexamples where dataflow equality loses Protocol behavior
([counterexamples](cases/protocol-semantics-theory.md#9-counterexamples-to-ordinary-dataflow-equivalence)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Conditional.** It can protect the total schedule, but a pass that reasons from a noncanonical representative or generic MLIR effects alone violates the quotient law. |
| `B*` | **Pass.** The total Core schedule and typed footprints are canonical semantic data; rewrites produce a new candidate checked under a named relation. |
| `D*` | **Pass.** The package can encode the same facts, although MLIR optimizers require a validated bridge back to package semantics. |
| `B*+P` | **Pass.** Transformation occurs over `B*`; an observer-specific validation view retains exactly the protected footprints it claims. |

### 6.6 Authoring-only or unknown extension content

**Required behavior.** Authoring conveniences must lower completely before
admission. Unknown meaning-bearing canonical content is rejected. Exact cited
contracts and opaque external subjects require typed closure; material may be
ignored only if every normative consumer is invariant to its removal. The
portable survey derives this taxonomy from mature extension systems
([portable hypotheses](cases/portable-ir-contracts.md#6-stage-1-hypotheses-produced-by-this-dossier)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Conditional.** A same-dialect sealed profile can refuse unknown content, but authoring-operation accretion continually enlarges the firewall audit. |
| `B*` | **Pass by refusal.** Full closure rejects any surviving authoring or unknown semantic operation; admission accepts only the closed canonical vocabulary and explicit dependencies. |
| `D*` | **Pass by refusal.** The package decoder/admitter rejects unknown meaning; adapters must not hide unsupported content during export. |
| `B*+P` | **Pass by refusal.** Both source admission and the named projection schema fail closed; an older view checker never treats omitted unknown meaning as harmless. |

### 6.7 Content-changing cost optimization with property deltas

**Required behavior.** A cheaper successor that changes a bound, adds an
assumption, or weakens a conditional property receives a new `ProtocolId` and
a named `IntentionalChange` or refinement result. `CostDominates` and
`PropertyTransport` are orthogonal judgments. It is not representation
equivalence. Translation validation is applicable to each produced successor,
but structural validation alone does not transport a cryptographic property
([translation validation](cases/protocol-semantics-theory.md#52-translation-validation)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Conditional.** Source and target quotient subjects can be related, but validation must never compare incidental representatives or infer property preservation from equal carrier shape. |
| `B*` | **Pass.** Both normal forms have exact identities; evidence names the claimed relation, validation rule, assumptions, and property deltas. |
| `D*` | **Conditional.** The package can express the result, but optimizer output and package successor need a permanent validated bridge. |
| `B*+P` | **Pass.** A cost view and a property-transport view may be separate, each scoped to its exact claim and source/target IDs. |

### 6.8 Composition with shared or interleaved challenges

**Required behavior.** Composition constructs a new Core with tagged child
occurrence namespaces, explicit port/claim mappings, causal seams, challenge
sharing rules, composition domain, and one total interleaving. Invoking the
same child twice must not alias occurrences. Graph union, constraint
concatenation, or ordinary symbol linking is insufficient; the ZK survey makes
the analogy limit explicit
([zkInterface transfer](cases/zk-proof-adjacent-irs.md#7-zkinterface-and-r1cs-interchange)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Conditional.** It can encode the new composed subject, but canonical occurrence renaming and all composition-sensitive facts must be complete in the quotient. |
| `B*` | **Pass.** Composition is an authoring transform that must close into a new canonical ordered Core and, for Fiat--Shamir, a new construction context. |
| `D*` | **Pass.** The package can be the output of the same explicit constructor; carrier neutrality does not make package concatenation valid composition. |
| `B*+P` | **Pass.** Composition authority remains in `B*`; a projection may expose the resulting occurrence/coverage map but cannot compose Protocols itself. |

### 6.9 Independent checker without the optimizing compiler

**Required behavior.** The checker must not import mutation passes, heuristic
optimizers, synthesis machinery, or broad compiler state. It still needs the
complete facts necessary for its exact claim. A parser plus small canonical PIR
schema, independent admission logic, and claim-specific rules is distinct from
the optimizing compiler even if both use MLIR core libraries. MLIR's structural
interfaces remain useful but do not supply zkc semantics
([MLIR mechanism boundary](cases/multilevel-mlir.md#41-mechanism-not-a-denotation)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Conditional.** The checker must implement the canonical quotient and admitted-profile firewall while accepting physically noncanonical representatives; that imports more semantic surface. |
| `B*` | **Pass.** A checker can depend only on the small canonical dialect/profile, canonical-form verifier, and relevant judgment rules. It need not import the optimizing compiler. |
| `D*` | **Pass.** This is the strongest positive scenario for a complete package; an independent decoder can avoid MLIR entirely. |
| `B*+P` | **Pass for a named scoped claim; refusal for unspecified full admission.** A narrow checker consumes an authenticated sufficient view. A checker of complete Protocol admission consumes `B*` or triggers `D*`; no lossy view may claim completeness. |

### 6.10 Same meaning across a carrier revision

**Required behavior.** Transport text, bytecode, or layout may change without
changing semantic identity when both decode to the same canonical subject
under the same regime. Carrier correspondence is checked explicitly. A version
number or successful adapter alone does not prove Protocol preservation
([portable conversion limits](cases/portable-ir-contracts.md#43-validation-and-conversion-limits)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Pass** if both carriers feed the one specified semantic encoder and no consumer observes carrier-only differences. |
| `B*` | **Pass.** `ProtocolId` is defined over the zkc semantic normal form, not MLIR bytecode; a new carrier decoder may recover the same subject. |
| `D*` | **Pass.** Package transport can revise independently of package semantics, provided decoding authenticates the same canonical package. |
| `B*+P` | **Pass.** Source identity remains stable; projection schema identities evolve separately when their own content changes. |

This pass is not a v0 promise to read historical carriers. Tools may fail
closed on an unsupported carrier even when a semantic correspondence could in
principle exist.

### 6.11 Same canonical bytes under two semantic regimes

**Required behavior.** The subjects have different semantic IDs even if their
raw payload bytes agree. A regime cannot silently reinterpret an existing ID.
Long-lived IR experience supports modeless meaning and separate version axes
([long-lived hypotheses](cases/long-lived-ir-contracts.md#6-stage-1-hypotheses-produced-by-this-dossier));
the native audit identifies this exact counterexample
([same bytes under two regimes](cases/current-zkc-correspondence.md#8-native-counterexamples)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Pass** in its strengthened form because the regime is in the semantic hash domain; a bytes-only Protocol ID would **fail**. |
| `B*` | **Pass.** Admission authenticates `(SemanticRegimeId, canonical subject)` and never mutates old meaning. |
| `D*` | **Pass.** The package must carry or be evaluated under an identified regime; schema equality alone is insufficient. |
| `B*+P` | **Pass.** Both source and derived view bind the regime; a view cannot merge cross-regime subjects by payload digest. |

### 6.12 Source-free OIR whose original coverage is appraised

**Required behavior.** Raw source-free OIR can authenticate its own syntax,
identity, and endpoint-local semantics. It cannot establish that every
obligation of an absent source Protocol was projected, that the declared source
ID existed, or that projection preserved source behavior. The native case
study states this exact epistemic boundary
([source-free OIR](cases/current-zkc-correspondence.md#8-native-counterexamples)).

| Candidate | Verdict and reason |
|---|---|
| `A*` | **Pass by refusal.** Source coverage requires admitted source PIR plus the interface and projection relation, or an independently checkable certificate carrying sufficient authenticated source facts. |
| `B*` | **Pass by refusal.** Raw OIR is not promoted into evidence about an absent canonical Protocol. |
| `D*` | **Pass by refusal.** A complete portable Protocol package supplied beside OIR could enable checking, but then the input is not raw source-free OIR. |
| `B*+P` | **Pass by refusal for raw OIR; pass with a sufficient paired projection certificate or source view.** The certificate's exact coverage claim and source commitments must be checkable; provenance strings alone are insufficient. |

Any design that reports source coverage from raw source-free OIR **fails** this
scenario. This is a limit of available evidence, not a missing convenience
feature.

## 7. Decisive falsifiers

### 7.1 `A*`

`A*` is falsified by any pair of admitted representatives with the same
`ProtocolId` and same separately identified inputs that yields different
normative admission, projection, Analysis, relation binding, plan checking, or
realization results. It is also falsified if an independent checker must import
the optimizing compiler to reproduce the quotient. The present label example
is already a counterexample to the unstrengthened Candidate A; the proposed
`ProtocolInterfaceId` and capability firewall must eliminate the entire class,
not just those labels.

### 7.2 `B*`

`B*` is falsified if any rejection-relevant semantic distinction cannot be
retained in the closed form, if the canonical level grows into a second
optimizing workbench, or if normalizing authoring input necessarily chooses
unidentified policy rather than preserving or exposing it. It is also
falsified if independent admission cannot be implemented without importing
authoring and optimization machinery. Mere reuse of canonical operations in
the workbench is not duplication and does not falsify it.

### 7.3 `D*`

`D*` is falsified as a language-neutral authority if two independent decoders
cannot implement the package from the normative specification, or if the
package merely serializes compiler-private MLIR decisions. It loses its stated
advantage if the MLIR-to-package bridge remains the only implementation of
meaning. As a v0 choice it is also unjustified until a concrete full-Protocol
consumer, trust/deployment boundary, or independent release cadence cannot
reasonably consume the small canonical MLIR level.

### 7.4 `B*+P`

The projection complement is falsified if a checker needs facts not committed
by the view for its declared claim, if two views disagree about shared
identified facts, or if projections accrete into a complete independently
evolving Protocol schema. A projection that contains everything should be
recognized as a trigger to reconsider `D*`, not quietly maintained as a second
authority.

## 8. Residual obligations after selection

Selection resolves the architecture, not its normative schemas or proofs.
Stage 2 and later owners must still discharge:

1. the exact denotation and well-formedness rules for `InteractiveCore`, both
   Protocol interpretations, interfaces, and plans;
2. the precise canonical normal form and identity preimage grammars, including
   semantic regime rules and invariance/sensitivity fixtures;
3. the exact boundary between semantic ports, external ABI, transcript codec,
   diagnostic names, and plan-private routes;
4. the admission lattice, including whether every canonical event must derive
   an abstract endpoint obligation or some event class is explicitly
   non-projectable;
5. complete protected-observer footprints and named transform relations;
6. explicit composition constructors, occurrence namespace rules, challenge
   sharing, and domain separation;
7. an independently implementable canonical-profile checker surface and
   differential conformance corpus;
8. the exact scope, sufficiency theorem or validation rule, and authentication
   format for each concrete purpose-specific projection; and
9. the formal-model correspondence boundary, which must model abstract
   Protocol semantics rather than become another mutable compiler IR.

The current reserved artifact-verification case shows why admission and
projectability must be resolved explicitly rather than inferred from syntactic
seal success
([current correspondence](cases/current-zkc-correspondence.md#63-reserved-artifact-verification-exposes-an-admission-status-gap)).

## 9. Enabled and deliberately deferred capabilities

| Bundle | Materially enabled | Deliberately deferred or burdened |
|---|---|---|
| `A*` | Maximum same-dialect authoring flexibility; minimal immediate representation count; cheap vocabulary evolution | Full-system quotient audits; small independent checking; confidence that ignored carrier fields never leak |
| `B*` | MLIR-native transformation and diagnostics; one exact admitted surface; independent admission; stable semantic identity across transport revisions; clean formal correspondence target; later portable export without identity redesign | Immediate non-MLIR full-package consumption; historical compatibility windows; arbitrary authoring extensions after closure |
| `D*` | Independent language implementations; non-MLIR deployment; a natural public interchange boundary | Duplicate complete schema, permanent adapter validation, compatibility governance, risk of freezing immature semantics, weaker direct optimizer ergonomics |
| `B*+P` | Small purpose-built checkers, formal kernels, caches, or endpoint evidence without broad compiler imports | Any claim outside the projection's declared scope; universal reuse of one lossy fact schema; source coverage from raw OIR |

The selected design does not foreclose a future portable package. Because
normative semantics and identity are independent of MLIR transport, a future
package can decode to the same regime-qualified subject and be related by
`RepresentationEq`. What is deferred is the public compatibility promise and
the permanent second schema, not language-independent meaning.

## 10. Reversal triggers and latest responsible decisions

### 10.1 Reconsider `A*`

Reconsider a one-dialect quotient only if the canonical and authoring
vocabularies remain demonstrably small, no information-loss boundary exists,
and an exhaustive consumer audit plus independent checker demonstrates the
quotient-congruence law. If the required solution is a strict normalized
profile and capability firewall, it has substantively converged on `B*`
regardless of dialect namespace spelling.

### 10.2 Introduce a portable complete package or compatibility dialect

Reconsider `D*`, or a Candidate-C-style portable compatibility representation,
when at least one of these becomes concrete:

1. a committed independent full-Protocol consumer cannot or should not import
   MLIR core plus the canonical PIR profile;
2. a deployment or trust boundary requires a substantially smaller non-MLIR
   decoder;
3. independent producers and consumers need a published compatibility window;
4. durable artifacts must outlive compiler carrier releases under an owned
   upgrade policy; or
5. two independent package decoders/checkers and a conformance corpus can be
   maintained.

Before that trigger, a version hook and fail-closed refusal are sufficient.
StableHLO/VHLO, SPIR-V, ONNX, WebAssembly, LLVM, and Sierra demonstrate that
compatibility machinery is valuable after an external contract exists, not
that zkc benefits from speculatively creating one
([cross-case synthesis](cross-case-synthesis.md#53-stable-compatibility-now-versus-later)).

### 10.3 Add a purpose-specific projection

Add a projection only after naming its consumer, exact claim, sufficient fact
set, authentication rule, and failure behavior. Prefer the smallest projection
that supports the claim. Promote it to a complete portable subject only if
several consumers repeatedly require the full Protocol and accept the
governance burden.

## 11. Convergence decision

Stage 1 should promote `B*` with the following exact commitments:

1. Normative Protocol semantics are language- and carrier-independent.
2. MLIR remains the primary v0 workbench and the structural carrier of the
   admitted canonical Protocol.
3. Canonical PIR is a distinct, small, closed level; authoring-only constructs
   live outside its admitted vocabulary and must fully lower away.
4. The zkc canonical semantic normal form, not MLIR text, bytecode, generic
   canonicalization, or current C++ object layout, defines identity.
5. All semantic identities are qualified by an immutable `SemanticRegimeId`.
6. The identity-bearing total observable schedule is part of
   `InteractiveCore`; partial-order authoring is a pre-Core template.
7. Fresh-public-coin and Fiat--Shamir Protocols are different subjects related
   by `FSCompile`.
8. External interfaces have dependent `ProtocolInterfaceId`s; prover
   construction strategies have separate `ProverPlanId`s.
9. Admission yields an immutable capability; all normative consumers take that
   capability or an authenticated purpose-specific projection derived from it.
10. Raw source-free OIR must refuse every claim of original source coverage.
11. No complete portable Protocol package or compatibility window is promised
    in v0; the reversal triggers above remain explicit.

This choice keeps MLIR's demonstrated structural and transformation value,
localizes canonicality and admission obligations at one small boundary, and
preserves a clean path to later independent carriers without paying their
permanent cost before a real consumer exists.
