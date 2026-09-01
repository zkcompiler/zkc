# F0 Primary-Source Ledger

> **Kind:** Temporary primary-source and framework ledger
> **State:** First live-source pass complete for VCVio/ArkLib and the
> cross-method/compiler-validation comparison; the first F2 property theorem
> is pinned and build/axiom-probed, while broader provider audits remain open
> **Authority:** None. Source inspection informs candidates. Only the explicit
> bounded build/probe below establishes its recorded result; it does not prove
> zkc correspondence or theorem applicability.
> **Observed:** 2026-09-02

## 1. Snapshot ledger

| Source | Inspected revision | Role in F0 | Limit of use |
|---|---|---|---|
| [VCVio](https://github.com/Verified-zkEVM/VCVio) | `de0a3108140e3e04a7ebf0075aa110b459ee6e8a`, 2026-09-01 | Candidate foundation for typed oracle computations, denotational probability, handlers/simulation, game reasoning, RBR, Fiat--Shamir, interaction, and implementation correspondence | The selected Schnorr module and theorem probe built successfully; no zkc encoding, source/provider correspondence, applicability result, or zkc property judgment was established |
| [ArkLib](https://github.com/Verified-zkEVM/ArkLib) current main | `9cf545c02a461ac7dbe6e522b3fb7bd803d35d89`, 2026-09-01 | Candidate higher-level IOR/reduction, composition, protocol, and proof-system theorem provider | Current source is not the revision authenticated by zkc receipts; source inspection does not establish theorem completeness or axiom freedom |
| ArkLib revision pinned by zkc | `fad5cbf808774838924dc8273715724c6a6caa1f`, 2026-07-25 | Exact source of current zkc ArkLib receipt and surveyed-absence claims | Intentionally historical; it cannot be used to report current ArkLib-main capability |
| ArkLib's current VCVio dependency | `f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24` | Shows the actual foundation beneath current ArkLib `OracleComp`, probability, simulation, and related infrastructure | Dependency does not make ArkLib and VCVio theorem interfaces identical or make ArkLib theorems applicable to zkc |
| [CompCert manual](https://compcert.org/man/manual001.html) | CompCert 3.17 online documentation, observed 2026-09-02 | Whole-compiler semantic-preservation comparator and explicit verified-interval boundary | CompCert's C/Asm semantics and theorem do not model zkc Protocols or cryptographic properties |
| [Verified Validation of Lazy Code Motion](https://xavierleroy.org/publi/validation-LCM.pdf) | Published paper artifact, Tristan and Leroy | Verified translation-validator pattern: unverified transform plus proved validator | One LCM validator does not validate zkc transformations; its relation is optimization-specific |
| [Alive2](https://github.com/AliveToolkit/alive2) | Upstream `master` documentation observed 2026-09-02; not pinned | Engineering comparator for per-run LLVM refinement checking and solver-backed bug finding | Current docs exclude interprocedural transforms; LLVM refinement does not contain zkc-native semantic observations |
| [Proof-Carrying Code](https://doi.org/10.1145/263699.263712) | POPL 1997 published artifact | Untrusted producer plus receiver-defined policy and small proof-checker pattern | A certificate proves only its exact policy; it does not define zkc correspondence automatically |
| [Cogent](https://arxiv.org/abs/1601.05520) | Published arXiv artifact | Hybrid language meta-proofs plus per-program translation validation in one top-level theorem | Cogent's language restrictions, Isabelle semantics, and C bridge are not a ready zkc toolchain |
| [hax manual](https://hax.cryspen.com/manual/) | Current online manual observed 2026-09-02; not pinned | Multi-backend Rust extraction comparator | Extraction support and generated terms do not prove admitted-zkc-subject correspondence |
| [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) | Current official reference observed 2026-09-02; exact future integration version not pinned | Axiom dependency inspection and independent kernel-replay trust distinctions | `#print axioms` and kernel replay do not establish intended statement meaning or zkc applicability |
| [SSProve](https://eprint.iacr.org/2021/397.pdf) | Journal paper/formalization artifact and upstream repository docs observed 2026-09-02 | Independent Rocq provider model with packages, state, composition, subdistribution failure, and relational cryptographic logic | Its package semantics and memory conditions still require an exact zkc adapter |
| [EasyCrypt](https://easycrypt.gitlab.io/easycrypt-web/) | Current official documentation observed 2026-09-02; toolchain not pinned | Independent code-based game/program-logic provider and solver-trust comparator | Its modules, adversaries, games, and solver basis do not derive from PIR without checked translation |

The current ArkLib main inspected here is 93 commits beyond the zkc pin. A
scoped source diff over `OracleReduction`, `ProofSystem`, `README.md`, and the
Lake configuration reports substantial change, including new and revised RBR,
composition, transcript-tree, protocol-component, FRI, Sumcheck, Binius, STIR,
and toy-problem material. This is a refresh trigger, not evidence that a
previously missing zkc obligation is now closed.

## 2. VCVio source observations

### 2.1 Computation subject

**Observed:** `OracleComp spec α` is a free monad over an indexed
`OracleSpec`. Its canonical cases are pure return and one oracle query followed
by a response-indexed continuation. `OptionT (OracleComp spec)` supplies an
explicit failure layer.

**F0 use:** This is a plausible semantic target for an ordered zkc interaction
runner because interaction is represented as computation rather than as fields
on one universal protocol record.

**Limit:** A free oracle-computation tree does not by itself carry zkc's
Protocol, relation, occurrence, identity, visibility, challenge-prefix,
reduction-group, terminal, or owner-authority meaning. An interpretation and a
checked correspondence remain necessary.

### 2.2 Interpretation and handlers

**Observed:** `simulateQ` replaces each oracle query with a supplied
`QueryImpl` in a target monad. Current VCVio contains logging, caching,
pre-generation, query bounds and costs, programming, tracing, random-oracle,
and operational/coinductive interaction support.

**F0 use:** This supports the hypothesis that transcript execution, random
oracle interpretation, logging/caching correspondence, resource observation,
and later implementation semantics can be separate handlers over one zkc-
derived computation.

**Limit:** Handler composability in VCVio does not prove that a handler order
or state split matches zkc's event order, absorb/squeeze discipline, failure
precedence, or shared state.

### 2.3 Probability and program logic

**Observed:** VCVio exposes measure-valued and finite-subprobability semantics,
output/event/failure probabilities, unary Hoare-style reasoning, relational
coupling-style reasoning, and game-transform tactics. The current tree also
contains round-by-round, Sigma-protocol, Fiat--Shamir, forking/rewinding,
asymptotic, cost, and interactive-system modules.

**F0 use:** VCVio is now a materially stronger F2 candidate than the older
local ecosystem summary alone demonstrated. It can potentially host both
operational correspondence and property-specific game reasoning.

**Limit:** The current generic RBR layer documents a strictly alternating
message/challenge model, with padding for absent sides. Whether that faithfully
represents arbitrary zkc schedules, interleaving, joint challenges, and
multi-effect reductions is a required F2 discriminator, not an assumption.

### 2.4 Exact first F2 property theorem and bounded validation

**Selected declaration:**
[`Schnorr.sigma_complete`](https://github.com/Verified-zkEVM/VCVio/blob/de0a3108140e3e04a7ebf0075aa110b459ee6e8a/Examples/Schnorr/SigmaProtocol.lean#L99-L109)
at the VCVio revision in the snapshot ledger. Its elaborated signature is:

```text
forall (F : Type) [Field F] [SampleableType F]
       (G : Type) [AddCommGroup G] [Module F G]
       [SampleableType G] [DecidableEq G] (g : G),
  (Schnorr.sigma F G g).PerfectlyComplete
```

The referenced `PerfectlyComplete` definition quantifies over every statement
and witness satisfying the relation and states that the honest commit,
uniform-challenge, response, and verification computation outputs `true` with
probability exactly `1`. The selected theorem therefore has an exact
quantitative conclusion. It does not require `Fintype F`, `DecidableEq F`, a
generator hypothesis, or a scalar-to-group bijection; those stronger
hypotheses enter other Schnorr properties, not this completeness result. The
library supplies the uniform-oracle interpretation used by the definition.

**Executed validation on 2026-09-02:**

- toolchain: the revision's `lean-toolchain`, Lean `v4.33.1`;
- dependency environment: the revision's `lake-manifest.json`;
- build: `lake build Examples.Schnorr.SigmaProtocol`, completed successfully;
- declaration probe: imported the built module and ran `#check`, `#print`, and
  `#print axioms` on `Schnorr.sigma_complete`; and
- reported axiom closure: `propext`, `Classical.choice`, and `Quot.sound`, with
  no `sorryAx` in the reported closure.

**F0 interpretation:** This closes the *theorem-selection* part of the F2
entry contract. It does not close Q2 provider correspondence, Q5
applicability, or Q6 target property. F2 must still show that one exact
reified zkc Fresh Schnorr subject corresponds to `Schnorr.sigma F G g`, that
its challenge and probability regimes match, and that the relation
`decide (sk • g = pk)` is the intended target relation. The probe was ordinary
Lean elaboration/kernel checking through the pinned environment, not an
independent `lean4checker` replay. Only the selected module was built; the full
VCVio repository was not validated.

## 3. ArkLib source observations

### 3.1 ArkLib is layered on VCVio

**Observed:** Current ArkLib's Lake configuration directly requires VCVio.
`OracleReduction` imports VCVio oracle-computation and simulation modules, and
several compatibility files record functionality moving upstream to VCVio.

**Consequence:** F0 should not frame the design as choosing unrelated theorem
foundations. The more accurate candidate topology is:

```text
VCVio generic oracle/probability/game substrate
  -> ArkLib higher-level IOR/proof-system abstractions and theorems
  -> optional exact adapter for a matching zkc subject
```

zkc may still use VCVio directly when its native subject does not fit ArkLib's
higher-level ontology.

### 3.2 High-level protocol and reduction shape

**Observed:** `ProtocolSpec n` is an indexed finite sequence of prover-to-
verifier or verifier-to-prover steps and associated types. `OracleReduction`
adds input/output statements, witnesses, oracle statements, prover/verifier
algorithms, execution, relations, and security notions. Sequential composition
has substantial definitions and theorem surfaces.

**F0 use:** ArkLib remains a strong selective provider for standard IOR and
sequential-reduction subjects and a useful comparison model for the minimum
information a zkc formal view must preserve.

**Limit:** zkc's structural reduction also binds claim-flow, owner occurrences,
event subsets, transcript influence, interleaving, shared challenges, checks,
terminal routes, and exact source views. Shape similarity cannot establish
that one ArkLib `OracleReduction` denotes the same subject.

### 3.3 Current open boundaries material to zkc

**Observed:** At the inspected current main:

- `OracleReduction/Composition/Parallel/Basic.lean` remains an explicit TODO
  surface rather than a general parallel-composition theorem library;
- the basic Fiat--Shamir file defines the transformation and a completeness
  theorem with an open proof, while state-restoration-to-Fiat--Shamir
  soundness remains a TODO in that file; and
- comments in the current reduction layer still describe active prover-model
  refactoring and distinctions among soundness, knowledge soundness, honest
  prover input/output, and adversarial interaction.

**Consequence:** Direct VCVio modeling is not merely a fallback for an old
ArkLib snapshot. It remains a credible route for zkc-native parallel,
interleaved, shared-challenge, transcript-runner, and Fiat--Shamir questions.

**Limit:** These source observations are file-local. They do not assert that no
other ArkLib module proves a related theorem, and they do not replace an
axiom-sweep or exact theorem-demand audit.

## 4. Cross-method source observations

### 4.1 Whole-compiler proof and validation close different propositions

**Observed:** CompCert states a universal semantic-preservation theorem over
formal source and target behaviors and composes it from per-pass proofs. It also
documents front- and back-end boundaries outside the proved interval.
Translation validation instead checks one produced source/target pair. The
verified LCM validator proves its checking algorithm sound, while Alive2 uses a
symbolic/refinement/SMT architecture with explicit unsupported boundaries.

**F0 use:** zkc can begin with per-artifact validation for reification, one PIR
transition, and later realization, while retaining whole-pass verification as
the stronger stable-pass endpoint. Both require an exact zkc observation and
relation; neither substitutes for a cryptographic property theorem.

### 4.2 Proof-carrying output localizes production trust

**Observed:** PCC and certifying compilation let a complex untrusted producer
emit an artifact-specific proof for a receiver-defined proposition. Cogent
combines reusable language-level proof with per-program validation into a
top-level theorem.

**F0 use:** An untrusted package exporter or compiler transform can emit a
certificate. A smaller checker validates exact source/package correspondence
or source/target preservation. Reusable owner-view and checker laws can later
compose with artifact-specific results.

**Limit:** A well-typed package, a safety certificate, and a semantic-
correspondence certificate are different propositions. No certificate format
should be selected before the exact proposition and observation map exist.

### 4.3 Extraction is a producer path, not the authority boundary

**Observed:** hax translates a large subset of Rust to several formal
languages, including Lean, Rocq, EasyCrypt, F*, and ProVerif.

**F0 use:** Extraction may later reduce duplication for a Rust reference
interpreter, checker, emitter, or cryptographic component and may help test
provider diversity.

**Limit:** zkc's current implementation is C++/MLIR and its target semantic
authority is independently specified. Extraction neither authenticates that
target nor proves that a supported source subset and foreign/runtime boundary
match it.

### 4.4 Kernel validation is not semantic correspondence

**Observed:** Lean's official guidance distinguishes transitive axiom
inspection from replaying stored declarations through `lean4checker`, and
states explicit trust limits for intended statement meaning, imported
libraries, `.olean` handling, and extensibility.

**F0 use:** Future theorem-source validation should identify toolchain,
dependency lock, declarations, statements, axiom profile, kernel-check mode,
and residual assumptions. Current receipts already preserve part of this
information.

**Limit:** A kernel-accepted theorem about the wrong formal subject remains the
wrong theorem for zkc. Subject correspondence and applicability are separate
checked propositions.

### 4.5 Independent cryptographic frameworks reject a universal formal AST

**Observed:** SSProve uses package interfaces, state, sequential/parallel
composition, subdistribution failure, and a probabilistic relational program
logic in Rocq. EasyCrypt uses code-based probabilistic games/modules with
adversarial code and relational program logics, with Why3/SMT support. VCVio's
native center is a typed oracle computation and handlers. These are related
but materially different semantic organizations.

**F0 use:** The provider-neutral boundary should be the exact zkc source
package, correspondence proposition/result envelope, and trust accounting—not
one proof-assistant-independent formal language. Provider adapters remain
partial and native.

**Limit:** Framework modularity does not prove that zkc's shared challenges,
interleaving, transcript construction, Oracle commitment extent, failures, or
relation roles map to a framework object.

## 5. Initial architecture implications

### I1 — generalize the provider model

F0 should compare a provider-neutral Analysis validation basis with both:

- direct VCVio operational/property proofs; and
- ArkLib declarations whose formal subjects have an exact checked adapter.

The provider identity must include the formal environment and trust profile,
but it must not enter the intrinsic identity of the zkc Protocol.

### I2 — split generic operational correspondence from theorem-library adaptation

A reusable zkc-to-VCVio interpretation may establish runner, trace, handler,
and probabilistic meaning. A separate, partial zkc-to-ArkLib adapter may reuse
high-level theorems. One adapter's success must not be required for the other,
and neither may silently widen the property claim.

### I3 — refresh is separate from bridge progress

The current ArkLib pin predates substantial upstream work. F0 must eventually
refresh the theorem-demand inventory against current main or a new reviewed
pin. Moving the pin, reproducing more declarations, or observing fewer
`sorryAx` dependencies is provenance progress only until exact zkc subject
correspondence and consumer admission are checked.

### I4 — the F2 discriminator must exceed strict alternation

The first VCVio pilot may use a simple alternating Schnorr or sequential
reduction. F2 cannot select the architecture on that case alone. It must also
test one zkc-native schedule with interleaving, shared challenge, explicit
terminal/failure meaning, or another observation that a simple alternating
model could erase.

### I5 — separate neutral source from native formal terms

The stable independent-consumer artifact should package exact owner source
coordinates and values. VCVio/ArkLib/SSProve/EasyCrypt terms remain provider-
native artifacts checked against that package. This avoids both trusted
provider-specific exporters and a universal formal AST that would become a
second semantic center.

### I6 — use a hybrid proof/validation program

F1 should begin with an untrusted exporter and small package/correspondence
checker. Reusable proofs of view closure, package checking, and provider
interpretation can be added without waiting for a verified compiler. Stable
passes may later replace repeated per-run checks with universal preservation
theorems while retaining the same proposition identity.

## 6. Pending primary-source work

F0/F1/F2 still require:

- exact VCVio theorem and trust surfaces beyond the first pinned completeness
  path, especially the zkc-native F2 discriminator;
- an ArkLib current-main axiom/theorem-demand refresh without changing the zkc
  pin prematurely;
- the complete F2 provider-environment trust profile and independent replay
  policy beyond the bounded Lean/VCVio probe, including ArkLib only if used;
- exact SSProve/EasyCrypt versions only if an adapter prototype is selected;
- a validator/checker-soundness route for the F1 package checker;
- the precise certificate or derivation calculus only after the F1
  correspondence proposition is fixed; and
- a property-specific refinement/observation theorem for the first Compiler
  transition rather than a generic compiler-correctness slogan.

## 7. Non-claims

The selected VCVio Schnorr module and one declaration probe were built as
recorded in Section 2.4. No full-repository build, independent kernel replay,
ArkLib/Rocq/EasyCrypt declaration check, repository-wide axiom sweep,
zkc-to-provider mapping, or applicability check was performed, and no external
theorem was admitted by zkc. All other literature, documentation, revision,
and source-shape observations are research evidence only.
