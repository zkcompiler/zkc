# Formal Assurance Architecture Research

> **Kind:** Temporary cross-cutting research-program index
> **State:** Active; first F0 architecture pass, bounded F1-R0 package/checker
> pass, bounded F1-R1A target profile/source-basis pass, and one-slice F1-R1B
> target carrier/admission pass complete at research resolution. Owner-view
> F1-R1C, integrated-package F1-R1D, live-owner F1-I, and F2 remain dependent
> feasibility programs, not selected product implementation
> **Authority:** None. This package changes no current or target semantics,
> artifact identity, theorem status, Analysis judgment, implementation claim,
> or product-roadmap priority.
> **Main-lane relation:** Side research against the holdout-stable semantic
> candidate. It does not replace the dependency-ordered post-freeze program or
> activate Stage 4B.
> **Deletion rule:** Absorb selected contracts, rationale, and explicit
> deferrals into their durable owners, then remove this package before
> `docs-next/` cutover.

## Central question

What is the ideal assurance architecture for turning one exact admitted zkc
subject into a formally interpreted subject and then into one qualified,
property-specific Analysis judgment, while:

- preserving zkc-native interaction, reduction, interleaving, challenge,
  Oracle, failure, and terminal meaning;
- permitting VCVio-native operational and game reasoning;
- reusing ArkLib or another theorem library only when an exact correspondence
  is established;
- allowing untrusted, replaceable, or proof-producing exporters and compiler
  passes behind small independently checked boundaries; and
- preventing a proof assistant, theorem name, receipt, formal syntax, producer,
  or serialized proof artifact from becoming ambient semantic authority?

The current design is one candidate, not the default winner. F0 may recommend
alignment, an additive formal subject, a changed owner boundary, or a larger
semantic redesign when the gain and migration cone justify it.

## Program sequence

```text
F0  ideal assurance architecture and current-design falsification
  -> F1-R0  package/checker feasibility                 [complete, bounded]
  -> F1-R1A exact target profile/source basis           [complete, bounded]
  -> F1-R1B exact target carrier/admission              [complete, bounded slice]
  -> F1-R1C exact owner views/read closure              [open]
  -> F1-R1D exact integrated target package             [open]
  -> F1-I   live admitted-owner correspondence          [open]
  -> F2  zkc-native operational interpretation and one property pilot
```

### F0 — assurance architecture

Reconstruct the exact current and selected target boundaries, derive a clean-
room ideal architecture, compare equal-resolution candidates, and identify
every required subject, identity, authority, proposition, checker, trust root,
and refusal. F0 ends with a provisional architecture, explicit main-design
changes or positive non-change rationale, and exact F1/F2 entry contracts.

### F1 — subject reification

Test the F0 architecture by deriving one complete formal subject from an exact
admitted bounded Protocol/Relations/Analysis source. The exporter may be
untrusted; a smaller independent checker or proof object must establish the
claimed subject correspondence. F1 may reveal that F0 omitted an observable,
bound the wrong identity, or assigned authority to the wrong owner; such a
finding reopens F0 explicitly.

The first executable pass exposed a necessary sequencing distinction. F1-R0
tests the package/checker boundary over manual target-shaped data. F1-R1A
establishes that the exact target profile and source declarations are
independently reconstructible and mechanically distinguishes them from K2's
witness-local profile and eight-field carrier. F1-R1B now forms and admits one
complete fourteen-field finite Schnorr target slice and requires its admitted
handle for Fresh Protocol formation. It is an offline bounded evaluator, not
the live compiler owner or a complete evaluator for every target constructor.
F1-R1C/R1D still need owner views, Relations roots, and the integrated package.
F1-I then binds the same proposition class to admitted live owner handles and
authority. No Q1 claim is complete before F1-I.

### F2 — operational semantics

Interpret the F1 subject as a typed oracle computation, initially using VCVio
as the leading candidate substrate, and establish one bounded runner or trace
correspondence plus one property-specific theorem path. A second discriminating
case must exercise a zkc-native feature such as interleaving, shared challenge,
or Fiat--Shamir game structure. ArkLib remains a comparison and selective
theorem-provider candidate where its subject matches exactly.

F1 and F2 are research programs, not commitments to one Lean encoding,
provider, extraction tool, or durable schema.

## Package record

- [`f0-charter-and-method.md`](f0-charter-and-method.md) fixes F0 scope,
  candidate discipline, workstreams, scenarios, gates, and handoff contracts.
- [`f0-current-baseline.md`](f0-current-baseline.md) starts the live current-
  and target-model reconstruction and records the first design pressures and
  non-implications.
- [`f0-source-ledger.md`](f0-source-ledger.md) records the first exact live
  VCVio/ArkLib source pass, the broader primary-source formal-method
  comparison, material open boundaries, and the resulting architecture
  implications and source limits.
- [`f0-owner-identity-observation-map.md`](f0-owner-identity-observation-map.md)
  reconstructs current and target owners, source closures, identities,
  authority, current receipt limitations, and the missing formal-reification
  edge.
- [`f0-formal-method-patterns.md`](f0-formal-method-patterns.md) compares
  whole-compiler verification, translation validation, proof-carrying output,
  hybrid certifying compilation, extraction, proof-environment validation, and
  several cryptographic proof frameworks at their exact assurance boundaries.
- [`f0-candidate-matrix.md`](f0-candidate-matrix.md) instantiates Candidates
  P/A/S/C/R at equal resolution and records the provisional A/S/C convergence
  with explicit reversal conditions.
- [`f0-scenario-pressure-tests.md`](f0-scenario-pressure-tests.md) executes the
  first Schnorr, sequential-reduction, shared-challenge/interleaving,
  Fiat--Shamir, Oracle, Compiler-transition, and future-realization falsifiers
  against the written architecture.
- [`f0-assurance-lattice-and-trust.md`](f0-assurance-lattice-and-trust.md)
  separates source admission, reification, provider correspondence, theorem
  environment/truth/applicability, property, transition, transport, endpoint,
  and realization claims and records their trust DAGs.
- [`f0-provisional-architecture-and-entry-contracts.md`](f0-provisional-architecture-and-entry-contracts.md)
  selects the provisional two-layer source-package architecture for
  falsification, records the rotation cone and non-changes, and fixes exact
  staged F1/F2 entry and worktree contracts.
- [`f1r-reference-package-feasibility.md`](f1r-reference-package-feasibility.md)
  records the 18-case, two-checker F1-R0 result, the protected-observation/read
  and alias-free closure refinements, the exact nonclaim about manual source
  bodies, and the staged F1-R1/F1-I sequence.
- [`f1r1a-target-basis-and-admission-gap.md`](f1r1a-target-basis-and-admission-gap.md)
  records the independently reconstructed frozen target Interaction profile,
  target/K2 carrier discriminator, executable identity-versus-admission gap,
  and the refined F1-R1A/R1B/R1C/R1D sequence.
- [`f1r1b-target-core-admission.md`](f1r1b-target-core-admission.md) records the
  complete target carrier and bounded ten-stage admission result for one
  finite Fresh Schnorr slice, exact dependency and live-handle findings, the
  27-case mutation evidence, explicit unsupported surface, and R1C contract.

The first pass provisionally favors exact owner-derived Analysis source views
plus a stable question-relative neutral source package and untrusted,
proof-producing exporters behind independent checkers. Provider terms remain
native to VCVio, ArkLib, SSProve, EasyCrypt, or another exact framework; no
universal formal AST is selected. This is a research result, not a target
change.

The F2 property gate is now concrete: the first path uses VCVio's
`Schnorr.sigma_complete` at revision
`de0a3108140e3e04a7ebf0075aa110b459ee6e8a`. The pinned module built, the
declaration probe succeeded, and its reported axiom closure excludes
`sorryAx`; the exact quantitative conclusion is honest acceptance probability
`1`. This closes theorem selection only. Source/provider correspondence and
applicability remain F2 obligations.

F1-R0 passes 18/18 frozen cases with a zero-dependency Python checker and a
standalone no-crate Rust checker that share no parser or canonical encoder.
F1-R1A passes 10/10 heterogeneous boundary checks: the exact target profile
and source routing are available, while fixture profile substitution and
identity-only recursive relabelling are refused. F1-R1B passes 27/27 cases for
one exact target slice: the fourteen-field Core and Fresh Protocol admit, while
identity, dependency, declaration/ABI, schedule, visibility, liveness,
profile, and authority substitutions fail closed. None of these results is Q1. F1-R1C
and R1D must still form exact owner views and the integrated package before
F1-I supplies live implementation authority. F2 starts only after one
affirmative bounded Q1 correspondence and retains separate operational,
property, and zkc-native discriminator stages.

## Known risks and non-claims

- A formal interpretation is not automatically faithful to the admitted zkc
  subject.
- A checked correspondence does not establish a cryptographic property.
- A property theorem does not establish compiler-pass preservation or backend
  realization.
- A VCVio or ArkLib proof does not by itself verify zkc's C++, MLIR carrier,
  canonical encoder, generated code, cryptographic primitives, or deployment.
- A feasibility prototype is disposable evidence and cannot rotate a durable
  profile, establish theorem truth, or authorize implementation.
- Internal agreement over a manual source package is not admitted-source Q1
  correspondence; coherently formed bytes have no source authority.
- F0 may find no required kernel change; that outcome is valid only after the
  generative and capability-expanding candidates receive equal-resolution
  treatment.

## Intended durable destinations

- integrated architecture and owner boundaries: `docs-next/project/`;
- formal subjects and exact source views: `docs-next/pir/` and
  `docs-next/relations/`;
- theorem providers, validation bases, qualified judgments, trust closure,
  and property transport: `docs-next/analysis/`;
- transformation preservation and decision consumption: `docs-next/compiler/`;
- endpoint projection and operational correspondence: `docs-next/oir/` and,
  only after activation, `docs-next/realization/`;
- execution order and deferred product commitments: the single authoritative
  roadmap under `docs/`.

No durable page may depend semantically on this package.
