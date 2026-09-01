# F0 Formal-Method Pattern Comparison

> **Kind:** Temporary primary-source comparison and trusted-boundary analysis
> **State:** First cross-method pass complete; exact pilot-specific trust audits
> remain for F1/F2
> **Authority:** None. Literature analogies constrain candidates but establish
> no zkc theorem, correspondence, compiler result, or implementation claim.
> **Observed:** 2026-09-02

## 1. Why the methods must not be ranked on one axis

“Formally verify the compiler,” “use translation validation,” “extract the
model,” and “attach a certificate” are answers to different questions. Their
strength depends on the exact edge being checked:

```text
source meaning
  -> reified formal subject
  -> provider interpretation
  -> property theorem
  -> transformed subject
  -> endpoint implementation
```

A strong proof on one edge does not repair an undefined relation on another.
In particular, a proof assistant can kernel-check a theorem about the wrong
formal subject, and a verified compiler can preserve an inadequate source
semantics perfectly.

## 2. Pattern matrix

| Pattern | Unit of assurance | Producer trust | Required semantic work | Principal residual trust | Best zkc use | Does not establish |
|---|---|---|---|---|---|---|
| whole-compiler verification | every successful run of a pass/compiler under a universal theorem | verified implementation and proof development rather than each run's producer output | formal source/target semantics, observations, and simulation/refinement for every pass | proof assistant/kernel, formal semantics adequacy, unverified front/back boundaries, axioms | long-term verified lowering or a small stable semantic pass set | cryptographic property truth, theorem applicability, external libraries, or deployment unless included |
| verified translation validation | one concrete source/target pair accepted by a validator whose soundness is proved | transformer may be untrusted | formal source/target semantics, exact accepted relation, validator soundness | validator extraction/runtime, proof kernel, model adequacy; any solver/certificate assumptions | per-artifact PIR transitions and later OIR/Realization checks | transformations the validator cannot model; global producer correctness; source property truth |
| solver-backed translation validation | one concrete bounded refinement/equivalence query | transformer untrusted; validator/solver trusted according to basis | symbolic semantics, refinement relation, bounds, query encoding | SMT solver, validator, modeling and boundedness | bug finding and bounded transition checks after zkc observations are encoded | unbounded correctness or zkc-native transcript/security meaning merely from LLVM support |
| proof-carrying or certifying production | one output plus a proof/certificate for a receiver-defined proposition | producer and proof search may be untrusted | exact proposition, certificate language, verification-condition or query generation, checker | checker, policy/proposition adequacy, source/output binding | portable reification, transform, domain, or realization evidence | any property outside the certificate proposition; correspondence if the certificate proves only safety |
| hybrid meta-proof plus per-program validation | reusable pass/language theorems composed with artifact-specific generated proofs | complex compiler pieces may remain outside the TCB | top-level composition theorem plus exact per-program obligations | proof kernel, generators only where unchecked, semantic correspondence | likely medium-term zkc architecture: reusable view/reification laws plus package- and pass-specific validation | a universal proof for unsupported families or unmodeled effects |
| source extraction to a prover language | translation of code or typed AST into a formal language | extraction tool is trusted unless separately validated | supported source subset, translation semantics, foreign-function and unsafe boundaries | extractor/frontend, source compiler, target prover, model adequacy | later Rust implementation verification or disposable formal-model production | that extracted terms equal the admitted zkc semantic subject or that proofs transport back |
| proof-environment authentication | exact declaration, statement, dependency/axiom profile, and kernel replay | theorem authoring remains semantically trusted; tactics need not be in final kernel TCB | exact environment/revision and theorem statement | kernel/checker, library axioms, statement's intended meaning | strengthen current receipts and theorem-truth validation | subject correspondence, applicability, or property transport |
| cryptographic game framework | exact games/packages/oracle computations and relational/probabilistic proof | model and proof authoring checked under framework | adversary interfaces, state, failure, probability, assumptions, and observations | framework logic/kernel, axioms, model adequacy | VCVio-native runner/games, selective ArkLib theorem use, provider-diversity tests with SSProve/EasyCrypt | correspondence to PIR or endpoint code without a separate checked bridge |

## 3. Whole-compiler verification: the CompCert comparator

The [CompCert manual](https://compcert.org/man/manual001.html) states semantic
preservation as: when compilation of source `S` succeeds and produces target
`C`, the observable behavior of `C` improves one allowed observable behavior of
`S`. The theorem is stated over formal source and target AST semantics. The
verified core is composed from fifteen pass proofs; preprocessing, parts of
elaboration, textual assembly, assembling, and linking remain outside that
core in the documented release.

Three lessons transfer directly:

1. a compiler theorem needs an explicit observation model, including
   termination/failure rather than only final values;
2. refusal to compile is compatible with a strong theorem; and
3. source-level properties transport only through the exact semantic-
   preservation relation and its premises.

Candidate R would pursue a CompCert-like center for zkc. It is coherent, but
its cost is not “write the current C++ in Lean.” It requires formal semantics
and pass relations for authoring/carrier decoding, Core/Protocol/Relations,
Analysis-relevant observations, MLIR transport, projection, OIR, and backend
boundaries. Even then, it would not prove a cryptographic property until a
separate theorem relates the source semantics to the security experiment.

The CompCert boundary also warns against an “end-to-end” label that silently
starts after decoding or stops before assembling/deployment. zkc should report
the exact verified interval and the excluded boundaries.

## 4. Translation validation

### 4.1 Verified validator

Tristan and Leroy's
[Verified Validation of Lazy Code Motion](https://xavierleroy.org/publi/validation-LCM.pdf)
defines translation validation as a posteriori validation of one compilation
or transformation run. Its validator includes an optimization-specific check
for anticipability so that code that may fail is not moved before a loop that
may diverge. The validator's correctness is mechanically proved, while the LCM
implementation remains unverified.

This is the closest formal-method pattern for a zkc pass:

```text
untrusted transform proposal
  -> PIR admits the target independently
  -> property-specific validator checks the exact transition
  -> checked transition result
```

The hard part is the relation, not the word “validator.” A validator for event
multiset equality cannot establish challenge-prefix noninterference. A
validator for terminal decision equality cannot establish preservation of
relation satisfaction, quantitative soundness, or Oracle commitment extent.

### 4.2 Alive2 as a bounded engineering comparator

[Alive2](https://github.com/AliveToolkit/alive2) combines an IR, symbolic
executor, LLVM-to-Alive2 converter, refinement checker, and SMT abstraction.
It demonstrates that per-run translation validation can find real optimizer
miscompilations without verifying the optimizer. Its current documentation
also explicitly excludes interprocedural transformations and warns that using
it there may produce spurious counterexamples.

Alive2 is therefore a method reference, not a zkc validator. Reusing it at a
later LLVM boundary could check the LLVM semantics it models. It cannot see
zkc challenge correlation, transcript influence, Oracle modes, relation roles,
cryptographic experiments, or qualified failure unless those are first given a
sound semantics and preserved through the lowering boundary. Solver timeouts
or bounded loop exploration must remain noncompletion, not affirmative
preservation.

## 5. Proof-carrying and certifying production

Necula's [Proof-Carrying Code](https://doi.org/10.1145/263699.263712) requires
an untrusted producer to supply code plus a proof of a receiver-defined safety
policy. The receiver checks the proof rather than trusting the producer.
Certifying compilation applies the same split to a compilation result: one run
emits an artifact-specific proof checked separately.

The transferable architecture is:

```text
complex, replaceable producer
  -> candidate + certificate
small receiver-owned checker and policy
  -> accept exact proposition or refuse
```

For F1, the candidate is a source package or provider artifact and the policy
is exact correspondence to one admitted source closure. For a Compiler pass,
the proposition is one exact preservation/refinement relation. The two
certificates are not interchangeable. A proof that a package is well typed
does not prove source correspondence; a proof that target code is memory-safe
does not prove protocol semantics.

The certificate itself carries no zkc authority. The zkc owner must reconstruct
the proposition, check subject/package binding, validate the certificate under
an exact basis, and mint a fresh qualified capability for one consumer and
purpose.

## 6. The Cogent hybrid

[Cogent](https://arxiv.org/abs/1601.05520) is a useful architecture comparator
because its compiler produces C, a shallow Isabelle/HOL semantic embedding,
and a proof that the C implementation refines that embedding. Its top-level
certificate combines reusable language-level meta-proofs with per-program
translation-validation phases.

This suggests a practical zkc decomposition:

- prove reusable laws for owner-view formation, required-read closure, package
  checking, and one provider interpretation;
- validate each concrete package and transform instance independently; and
- compose only the exact results needed by one Analysis or Compiler claim.

This can approach verified-compilation strength incrementally without trusting
the exporter or proving every search/optimization implementation. It still
requires a checked top-level composition theorem before several local results
can be advertised as one end-to-end guarantee.

## 7. Extraction

[hax](https://hax.cryspen.com/manual/) translates a large subset of Rust to
formal languages including F*, Lean, Rocq, EasyCrypt, and ProVerif, and can
also emit a typed AST. This demonstrates useful provider diversity from one
implementation source.

Extraction changes where manual duplication occurs; it does not eliminate the
correspondence question. The supported Rust subset, frontend/typed-AST
semantics, unsafe and foreign interfaces, transformations, target backend, and
proof environment form the relevant boundary. zkc is currently centered on
C++/MLIR and an independently specified semantic target, so hax is not an F0
semantic center. It may become useful for a Rust reference interpreter,
emitter, cryptographic component, or checker after its source relation is
defined.

An extracted checker is stronger than a handwritten checker only if the
extraction theorem or validation path and runtime assumptions are included in
the validation basis. Generated code plus passing tests is not such a theorem.

## 8. Proof environment versus statement meaning

Lean's official
[proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
distinguishes axiom inspection from kernel replay. `#print axioms` exposes
transitive axiom dependencies such as `sorryAx`, custom axioms, or
`Lean.trustCompiler`. `lean4checker` can replay declarations stored in `.olean`
files through the kernel, while retaining explicit format, library, system,
and intended-statement trust limits.

The current zkc receipt driver already checks a useful subset: exact pin,
declaration resolution, normalized printed statement, and axiom set. A future
validation basis can add toolchain/lock identity, independent kernel replay,
module/dependency closure, and explicit treatment of custom axioms. None of
these checks answers whether the theorem's types and definitions model zkc.
That is a separate formal-correspondence proposition.

## 9. Provider-diversity pressure test

### 9.1 VCVio and ArkLib

The exact VCVio/ArkLib source observations are in
[`f0-source-ledger.md`](f0-source-ledger.md). Current ArkLib is layered on
VCVio. The likely topology is direct VCVio interpretation for zkc-native
oracle/runner/game semantics plus a partial ArkLib adapter for matching
higher-level IOR and proof-system theorems.

### 9.2 SSProve

[SSProve](https://github.com/SSProve/ssprove) is a foundational Rocq framework
for modular cryptographic proofs. Its journal formalization uses a hybrid
embedding: pure computation is shallow while effects are represented deeply
with a free monad. It provides package interfaces, state, sequential and
parallel composition, subdistribution failure, a probabilistic relational
program logic, and mechanized case studies including Sigma protocols and
Schnorr.

SSProve is useful to F0 for two reasons. First, its package/interface ontology
is materially different from VCVio's typed oracle computation, so a supposedly
provider-neutral zkc contract must not bake in one Lean free-monad type.
Second, explicit state separation and package import/export conditions show
that shared state and adversary composition are theorem premises, not adapter
implementation details.

SSProve does not remove the zkc bridge. A zkc occurrence schedule, challenge
correlation, failure partition, relation grounding, and transcript
interpretation still need an exact mapping to SSProve packages and memories.

### 9.3 EasyCrypt

[EasyCrypt](https://easycrypt.gitlab.io/easycrypt-web/) models cryptographic
security goals and assumptions as probabilistic programs or games with
unspecified adversarial code and proves relational properties with program-
logic techniques. Its proof engine can use Why3 and SMT solvers, so its
validation and trust accounting differs from a Lean or Rocq kernel-only path.

EasyCrypt is a strong independent test of the contract: the neutral source
package should let an adapter reconstruct games, modules, adversary interfaces,
state, observations, and loss without embedding Lean declaration names.
Solver-assisted obligations must expose solver/version/configuration and any
unproved assumptions in the validation basis.

The provider-diversity result is decisive: **provider neutrality should apply
to source coordinates, correspondence propositions, evidence envelopes, and
consumer policy—not to one universal formal AST.** Each framework should keep
its native operational and proof language behind an exact partial adapter.

## 10. Trusted-computing-base decomposition

| Trust component | Why it matters | How F0 localizes it |
|---|---|---|
| zkc semantic specification and profile laws | defines the source meaning being preserved | remains with existing owners; no formal provider can override it |
| canonical source decoder and identity recomputation | binds bytes/package entries to exact subjects | require at least two independent decoders/checkers when the durable neutral-package trigger is selected |
| owner-view and required-read-closure implementation | selects and closes the formal source observations | reusable checked laws plus differential/negative tests; eventually formalize or validate the checker itself |
| exporter | may omit, alias, or fabricate mappings | untrusted by default |
| source-package checker | establishes exact source reification | small receiver-owned checker; later verified or independently duplicated |
| provider adapter | may change schedule, state, failure, or quantifiers | separate partial translation contract and correspondence result per provider |
| proof kernel or relational logic | checks derivations | exact provider/environment identity and trust profile |
| SMT solver or native evaluator | may be trusted or certificate-producing | explicit validation-basis branch; timeout is noncompletion |
| imported axioms and cryptographic assumptions | theorem is conditional on them | exact theorem-truth treatment and support partition |
| theorem applicability checker | binds a generic theorem to one target | distinct structural proposition; inapplicability is not a negative property |
| Compiler transition checker | transports meaning across one pass | property/observer/direction-specific; no universal “equivalent” Boolean |
| OIR/backend realization checker | connects semantic endpoint to executable artifact | later target-specific validator or explicit trusted-producer residual assumption |

## 11. Method selection for the next phases

The current leading method is a hybrid:

1. untrusted production of a portable semantic-read package and provider
   artifact;
2. a small independent package/correspondence checker;
3. reusable proof-assistant laws for the checker and provider interpretation
   where practical;
4. artifact-specific translation validation for each package, pass, and later
   realization;
5. exact proof-environment and residual-trust validation; and
6. property-specific Analysis and Compiler consumption.

Whole-compiler verification remains the long-term high-assurance comparator,
not the F1 prerequisite. Extraction remains an implementation option, not a
semantic architecture. Proof-carrying output is an evidence mode layered on
the correspondence proposition, not a new authority owner.

## 12. Non-claims

The cross-method comparison itself did not build the surveyed frameworks. The
separate bounded VCVio Schnorr build and theorem probe is recorded in
[`f0-source-ledger.md`](f0-source-ledger.md); it does not validate any other
framework or bridge. No VCVio, ArkLib, SSProve, EasyCrypt, Lean, Alive2, hax,
CompCert, or Cogent artifact was admitted by zkc. Bibliographic and current-
documentation observations do not establish tool correctness, theorem
applicability, source correspondence, or a zkc security property.
