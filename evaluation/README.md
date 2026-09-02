# Evaluation

This directory contains optional, version-pinned integration evidence. It is
not required to build the compiler, and its results are scoped to the exact
fixtures and revisions named here.

## Semantic revalidation witnesses and probes

Run the bounded semantic checks from the repository root. The fast tier covers
the actively edited cross-owner seam; the full tier runs every selected
redesign gate without a timeout and is required once at a checkpoint rather
than after every local edit:

```sh
python3 -B evaluation/semantic_checks.py --tier fast
python3 -B evaluation/semantic_checks.py --tier full
```

The full runner executes the expensive Analysis test classes in four isolated
processes. This preserves the exact discovered test set while preventing
repeated canonical reconstruction in one class from serializing unrelated
classes. The focused Analysis runner retains a one-process mode by default and
accepts `--jobs N` when isolated parallel validation is desired.

Neither tier combines the scopes below into one proof or conformance claim.

These packages are temporary semantic-revalidation research instruments. They
are not compiler components, protocol implementations, security evaluators, or
evidence that a listed portfolio case is supported. Their results have
different strengths and must not be summarized as one green test count.

| Package | Classification | Retained evidence and exact limit |
|---|---|---|
| [`formal-source-package-f1r/`](formal-source-package-f1r/README.md) | F1-R portable formal-source package/checker feasibility falsifier | An untrusted producer forms one manual Fresh Schnorr package plus shared-challenge/interleaving and Fiat--Shamir discriminators. Zero-dependency Python and standalone Rust checkers with separate parsers and canonical encoders agree exactly on three affirmative source/read propositions and fifteen exact-class mutations, including retained IDs, missing/phantom reads, equal-content coordinate aliasing, shared-challenge duplication, schedule reordering, cross-profile replay, FS transcript omission, excluded owner-local support, dormant reads, and incomplete protected-observation coverage. This is bounded package-contract evidence over manual target-shaped bodies, not live-owner Q1 correspondence, checker verification, provider Q2 correspondence, theorem truth/applicability, a property, or product-format selection. |
| [`formal-source-target-basis-f1r1a/`](formal-source-target-basis-f1r1a/README.md) | F1-R1A exact target-profile basis and fixture-substitution discriminator | Reuses two independent publication compilers to reconstruct the frozen target Interaction profile and owner-source routing, checks the fourteen-field Core and two-field Protocol source shape, and refuses K2 profile substitution, eight-field Core reuse, identity-only relabelling, and a recursively relabelled Protocol dependency. This closes only the profile/source prerequisite; it is not a target body compiler, admission evaluator, owner-view evaluator, Q1 result, or implementation-conformance claim. |
| [`formal-source-target-core-f1r1b/`](formal-source-target-core-f1r1b/README.md) | F1-R1B exact-target carrier and bounded admission falsifier | Forms all fourteen Core fields and both Fresh Protocol fields for one finite `Z/3Z` Schnorr-shaped target subject under the frozen Interaction profile. The bounded evaluator authenticates exact Foundation/profile/module/algorithm/contract closure, runs the ten applicable admission stages, and requires a process-local admitted Core handle for Fresh formation. A separate encoder agrees across seven Core carrier shapes and one Protocol, an independent interpreter exhausts all 81 equation inputs, and the 27-case gate classifies retained IDs, exact-used modules, declaration/ABI/scope/backlink/visibility/sharing/claim/fallback failures, profile and authority substitution, and one unsupported target family. This is offline bounded evidence for one target slice, not a complete target evaluator, current Q0 admission, owner views, Q1, execution, cryptographic security, or implementation conformance. |
| [`formal-source-owner-views-f1r1c/`](formal-source-owner-views-f1r1c/README.md) | F1-R1C0 exact owner-view source-determinacy audit | Reconstructs the frozen Interaction profile through both publication compilers, independently inventories the raw manifest and authenticated static-view source, and re-admits the F1-R1B Core/Protocol controls. Its 13-case gate finds that the six view surfaces are authenticated but the promised owner-local schema catalog, exact nested body grammars, field-to-law bindings, and complete authority-envelope bodies are not published, so exact read-manifest formation is `CannotAnswer` and K2 view substitution is refused. This reopens F0 only at the PIR owner-view publication boundary; it is not a target repair, view evaluator, Q1 result, or defect in the admitted Core. |
| [`formal-source-owner-view-repair-f0v/`](formal-source-owner-view-repair-f0v/README.md) | F0-V1 owner-view publication-topology feasibility gate | Uses in-memory source/manifest overrides to publish six Interaction view-schema declarations, split common consumer/purpose role bodies from four profile-local authority-envelope compilers across Interaction and five direct dependents, and advance those six synthetic revisions. Two independent publication compilers agree on all eighteen resulting profile bodies and the exact sixteen-profile rotation cone; ten dual-path mutations refuse schema, owner, law, selector, reachability, revision, and cross-kind routing substitutions. The 18/18 result establishes only that the selected topology fits the existing publication mechanism. Canonical view/coordinate/manifest grammar and proper-subset read closure remain `CannotAnswer`; no target profile or identity changed. |
| [`semantic-profile-publication/`](semantic-profile-publication/README.md) | Stable semantic-profile publication conformance instrument | Two independently coded compilers reconstruct the complete bodies, typed references, direct-use imports, exact root closures, and derived identity table for all eighteen indexed target profiles, retaining six frozen v0 PIR profiles as byte-for-byte controls. Mutation tests cover source normalization, dependency topology, declaration reachability, identity feedback, receipt parameterization, and rotation locality. This is publication-format and finite-source evidence, not a formal law calculus, target body-compiler implementation, protocol theorem, or runtime conformance claim. |
| [`recursive-composition-boundary/`](recursive-composition-boundary/README.md) | Recursive-composition owner-boundary falsifier | Exercises exact recursion-facing instance coverage, closed incremental-composition-family selection and complete-body digest derivation, two-run/two-instance grounding, exact owner-local Relations-result ingress into Analysis, two-source Plan preparation, portable re-admission without causal aliasing, theorem-derived obligation reporting, the CycleFold same-step guardrail, and theorem application through existing Analysis judgments rather than live recurrence chains. It is finite architecture evidence, not a recursion implementation, relation-preservation result, hash-security claim, or IVC/PCD theorem. |
| [`k1-executable-foundations/`](k1-executable-foundations/README.md) | K1 foundation reference and independent identity oracle | The focused package gate covers the constitutional value/identity surface, typed domain values, bounded portable terms, deterministic charges, qualified outcomes, and its frozen oracle vectors. The package README and runner own the current case count. The oracle is independent only for values and identity; term evaluation has one Python implementation, and the instrument does not decode the complete serialized request carrier or establish a protocol or cryptographic claim. |
| [`k2-protocol-fiat-shamir/`](k2-protocol-fiat-shamir/README.md) | K2 bounded contract vectors and Protocol/Fiat--Shamir behavioral instrument | The bounded instrument includes target-exact K1-backed vectors only for its named canonical bodies. The remaining results are fixture-exact or behavioral-shape evidence over a simplified carrier: ordered transcript influence, represented public-coin sinks, Fresh/FS pairing, finite oracle activity, sampling, schedule-anchored reduction declarations, and runtime-only Fresh challenge resolution. Its package README and runner own the current case count. It does not implement the complete target carrier or establish a protocol or security theorem. |
| [`k3-dependent-surfaces/`](k3-dependent-surfaces/README.md) | K3-B dependent-surface boundary instrument | The bounded instrument exercises finite positive and mutation cases for Interface assignment and Statement coverage, Plan admission and realization, scope-gated public-input reads, witness projection and binding, four-role Relations attachment, replay-qualified public run grounding, semantic/validation identity separation, three non-substitutable value-bridge lanes, artifact facts and equations, and a tagged carrier round trip over the bounded K2 executable shape. Its package README and runner own the current case count. It is not an implementation of the durable schemas, relation satisfaction, theorem applicability, protocol conformance, cryptographic proof, or protocol-family closure. |
| [`k3-analysis-closure/`](k3-analysis-closure/README.md) | K3-C minimum Analysis boundary instrument | The bounded gate separates a family-neutral AFK theorem schema, abstract-family applicability and transport, and exact pointwise specialization to one native member. It exercises the selected source/target profiles, quantifier order, finite family/member manifests, bounded formulas, theorem applicability, and typed loss imports. Its package README and runner own the current case count. The all-`n` source capability, family laws and process correspondence, the classical ROM, and theorem truth remain explicit premises; this is not a proof of special soundness, knowledge soundness, Fiat--Shamir security, concrete-hash security, protocol conformance, or implementation support. |
| [`k3-oir-projection/`](k3-oir-projection/README.md) | K3-D bounded OIR-projection instrument | The bounded gate separately derives the selected PIR source graph, independently constructs and locally admits an OIR graph, checks exact source-relative equality and mismatch sets, derives the static endpoint contract, exercises graph-only access and the reachable Plan quotient, and fails closed at the unsupported boundaries. Its package README and runner own the current case count. Its positive profile remains base non-Oracle, non-module P01 FS Verifier and Plan-specialized Prover; dynamic execution, target-only pairing, full OIR syntax, refinement, protocol-family support, and cryptographic claims remain outside K3-D. |
| [`k3-integrated-closure/`](k3-integrated-closure/README.md) | K3-E bounded joined-closure instrument | Joins the finite K3-C and K3-D paths over one P01-derived total-uniform N=8 Schnorr variant, exact shared K1/K2/K3-B module identity, and owner APIs. This is not the retained `r2-p01-schnorr` artifact. Its endpoint basis distinguishes K2 static views, one affirmative checked FS construction plus its issued FS view, the K3-B Interface correspondence view, and an affirmative `CheckedPlanRealizes` for the Prover path. The Analysis lane deterministically rederives selected records and checks stable IDs; no live Analysis capability crosses into K3-D. Rich endpoint facts still use an explicitly checked future-owner supplement whose absence is `MissingDependency` and whose reconstructed or portable-only bearer is refused. This is finite integration evidence, not general authority implementation, protocol-family coverage, theorem truth, projection proof, or security evidence. Run its focused checker for the current result; this index does not duplicate an unverified count. |
| [`r2-protocol-model/`](r2-protocol-model/README.md) | Repaired `FRI-Grind-1` fixture witness | A 41-case frozen replay-verified corpus and 39 local tests close the named finite source-residual pressure. The model stops before authenticated FRI opening and acceptance; it is not a native FRI/IOR case. |
| [`r2-p01-schnorr/`](r2-p01-schnorr/README.md) | Retained T3 portfolio case `P01` | The prior 62-test snapshot failed cold review on modeled causality, equal-content occurrence aliasing, and incomplete independent-basis closure. The staged repair now passes 69/69 tests: 8 semantic, 27 execution/Interface, 8 provenance/diagnostics, 13 Relations/Analysis, and 13 report/replay. Its rotated source-bound report executes 45 cases—22 affirmative and 23 nonaffirmative—with 39 distinct public codes, and reproduces Fresh `c=3,z=3` and FS v3 `c=6,z=2`, proof `1002`. A separately coded query path is bound to the executed package initializer and shared term and semantic dependencies; it is diversity evidence, not independent semantic authority. The refrozen expected projection and minimal copied-checkout replay pass. Separate lifecycle and provenance cold rechecks pass on the final identity, closing Gate 10 and retaining P01 at T3 only for this exact finite scope. |
| [`native-fri-ior/`](native-fri-ior/README.md) | Native FRI/IOR semantic validation | One finite logical-oracle FRI case executes through commitment and work construction declarations with validation-bound one-execution receipts, admitted Fresh/Fiat--Shamir pairing, public-only replay, Relations grounding, and Analysis-question formation. A separately coded verifier agrees on selected exact positive public-execution facts; the producer separately classifies two authenticated late negatives at distinct fold and terminal refusals. The result supports the central factorization only at this finite scope; it is not general construction admission, exact paper-algorithm correspondence, family coverage, or a security theorem. |
| [`indexed-core-elaboration/`](indexed-core-elaboration/README.md) | Bounded indexed-Core authoring experiment | Authenticates the complete AST and complete canonical formation-and-interpreter law descriptor of a closed `Static`/finite-`Repeat` grammar and interprets FRI-shaped and sumcheck-shaped programs above exact finite Cores. Twelve FRI program/index routes and three sumcheck indices delegate to unchanged concrete Core admission and identity authentication and execute as same-Core Fresh/Fiat--Shamir pairs. Structurally distinct ASTs can produce one output-only `CoreId`; static output/work bounds remain semantic while evaluator limits do not. A complete pre-encoding AST carrier meter and all-fiber range preflight bound structural and materialization work. AST-derived authoring measurements and explicit malformed, boundedness, and dynamic-topology refusals keep the result finite; absence of an all-index theorem is a nonclaim, not falsification evidence. |
| [`plan-continuation-semantics/`](plan-continuation-semantics/README.md) | Bounded Plan-continuation semantic validator | Executes five finite accumulation, folding, and recursion pressure shapes through an admitted Plan adapter around the existing Protocol reference executor. It checks Plan-owned decision and accepted-terminal recipes, confidential witness views, private grounding, one-use direct output-to-ingress handoff, distinct public recurrence grounding, and independently derived continuation OIR contracts. The package is a semantic falsifier, not a protocol-family implementation, source-conformance result, recurrence proof, or cryptographic claim. |
| [`r2-probe-commitment/`](r2-probe-commitment/) | Cross-cutting commitment/opening invariant probe | Thirty-three unit tests. It is not portfolio case `P02`. |
| [`r2-probe-logup/`](r2-probe-logup/) | Cross-cutting LogUp claim-routing invariant probe | Twenty-nine unit tests. It is not portfolio case `P03` or any other numbered case. |
| [`r2-probe-value-bridges/`](r2-probe-value-bridges/) | Cross-cutting value-bridge invariant probe | Eighteen unit tests. It is not portfolio case `P04`. |
| [`r2-probe-guard-cost/`](r2-probe-guard-cost/) | Cross-cutting guard-cost invariant probe | Twenty-two unit tests. It is not portfolio case `P05`. |

The protocol namespace is reserved: `Pnn` names primary protocol cases, `Vnn`
recent variants, and `Hnn` holdouts. Cross-cutting packages use
`r2-probe-<subject>` and `R2-<SUBJECT>-...` codes so their existence cannot be
mistaken for portfolio progress.

Run P01's current suite and source-bound public replay from the repository
root:

```sh
python3 -m unittest discover -s evaluation/r2-p01-schnorr/tests -v
python3 evaluation/r2-p01-schnorr/run.py --check
```

The runner builds and strictly verifies the report before reading the expected
projection. Its successful comparison is exact finite replay evidence, not a
cryptographic theorem or complete diagnostic reachability result.

[`coverage.py`](coverage.py) produces a manually curated live boundary-coverage
snapshot. It pools reached boundaries across instruments and relies on an
authored invariant-to-boundary map, so its labels prioritize review; they are
not R2 closure verdicts. [`reachability.py`](reachability.py) instruments the
current suites and reports declared versus fired result codes. A fired code is
not proof that the boundary discharges an invariant, and an unreached code is
not automatically a defect.

Run the current diagnostics from the repository root:

```sh
python3 evaluation/coverage.py
python3 evaluation/reachability.py
python3 evaluation/reachability.py --witness r2-p01-schnorr --list-unreachable
```

## Plonky3

[`upstream/plonky3-replay/`](upstream/plonky3-replay/README.md) is the active
evaluation harness. One locked Rust crate provides:

- upstream BabyBear/Poseidon2 duplex observations;
- deterministic proof capture and verifier replay;
- mutation checks;
- a value-faithful prover fill consumed by zkc's native endpoint path; and
- a grading judge that decodes zkc's canonical wire into the pinned upstream
  proof shape and hands it to the upstream verifier, so acceptance comes from
  an implementation zkc does not own.

The corresponding lit coverage is in
[`plonky3-replay.test`](../test/Evidence/plonky3-replay.test),
[`plonky3-fri-value-faithful.mlir`](../test/Oir/plonky3-fri-value-faithful.mlir),
[`plonky3-duplex-replay.test`](../test/Oir/plonky3-duplex-replay.test),
[`prover-real-fill.test`](../test/Oir/prover-real-fill.test),
[`emit-fri-prover.test`](../test/Emit/emit-fri-prover.test), and
[`emit-fri-scale.test`](../test/Emit/emit-fri-scale.test). These checks do
not establish general Plonky3 conformance, protocol soundness, or production
readiness.

[`fri-bench/`](fri-bench/README.md) records generation-versus-upstream
benchmark evidence: the pinned upstream prover and an emitted zkc prover
timed over the same instance, with the emitted wire held byte for byte to a
recorded golden wire before anything is timed. The measured numbers live in
[`RECORD.md`](fri-bench/RECORD.md) with machine, revision, and instance
provenance; the soundness-accounting alignment against upstream's
p3-security tooling lives in [`PRICING.md`](fri-bench/PRICING.md). These are
recorded evidence, not CI gates; only the deterministic byte-equality scale
gate runs in lit.

## Regression provenance

Two current PIR regression pairs are derived from public source history.
The fixtures model only transcript ordering and material binding; they do not
execute the named systems.

| Fixtures | Reviewed source coordinates | Modeled boundary |
|---|---|---|
| `linea-rlc-*` | Linea [before](https://github.com/Consensys/linea-contracts-fix/commit/65238564c9dd6bee9669116dcec0b72e689662ae) and [after](https://github.com/Consensys/linea-contracts-fix/commit/4ff29606881d576264b282957808e56fb62460a8) | Equation material precedes its random-linear-combination challenge. |
| `sp1-rlc-*` | `p3-fri` [0.1.4-succinct](https://crates.io/crates/p3-fri/0.1.4-succinct) and [0.2.0-succinct](https://crates.io/crates/p3-fri/0.2.0-succinct); Plonky3 [repair](https://github.com/Plonky3/Plonky3/commit/b5ec4d96bc752e78990db0707f6b60c4f3d9930a) | Opening values precede their random-linear-combination challenge. |

The executable fixtures and C++/Python parity checks are in
[`ordered-rlc-parity.test`](../test/Evidence/ordered-rlc-parity.test).
