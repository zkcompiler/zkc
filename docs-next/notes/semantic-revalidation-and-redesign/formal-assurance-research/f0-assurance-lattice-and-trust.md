# F0 Assurance-Claim Lattice and Trust Map

> **Kind:** Temporary judgment-separation and trusted-boundary dossier
> **State:** First complete F0 claim decomposition; the first provider theorem
> is pinned, while bridge/applicability/property instances remain open
> **Authority:** None. Temporary `Q*` labels are explanatory only and are not
> proposed public result-family names.

## 1. The assurance result is a partial order, not one score

There is no sound scalar meaning of “zkc is 70% formally verified.” The
relevant claims have different subjects and can be incomparable. A theorem may
be kernel-checked while inapplicable; a package may correspond exactly while
the theorem remains assumed; a pass may preserve Protocol behavior while an
endpoint emitter remains unvalidated.

The minimum dependency graph is:

```text
Q0 source admission
  -> Q1 portable source reification
       -> Q2 provider-subject correspondence

Q3 provider environment authentication
  -> Q4 theorem truth treatment

Q0 + Q1 + Q2 + Q3
  -> Q5 theorem applicability

Q4 + Q5 + exact assumptions/support
  -> Q6 property-specific Analysis judgment

target Q0 + source/target relation
  -> Q7 checked Compiler transition

source Q6 + Q7 + exact preservation/transport theorem
  -> Q8 successor property judgment

Q0 + projection relation
  -> Q9 OIR correspondence

Q9 + target-specific realization relation
  -> Q10 realization correspondence

Q10 + deployment/resource/operator authority
  -> live invocation authority
```

The arrows are necessary dependencies for the displayed route, not universal
implications. Another property family may have a direct checker and bypass a
theorem-provider route; it still needs an exact source proposition and
validation basis.

## 2. Claim table

| Label | Exact subject | Affirmative meaning | Principal checker or authority | Does not imply |
|---|---|---|---|---|
| Q0 source admission | one exact Core, Protocol, Interface, Plan, Relation, Analysis, Compiler, OIR, or other owner subject under one profile/regime | the owner admits the immutable subject under its closed laws | exact semantic owner and evaluator | a property, source/formal correspondence, another owner's admission, or implementation correctness |
| Q1 source reification | exact owner roots, authentication preimages, manifests, selected reads, and package contract | package roots and reads equal the exact admitted owner meanings selected by the contract | source-package checker using owner laws and source authorities | provider semantics, theorem applicability, theorem truth, or portable secret authority |
| Q2 provider correspondence | one reified source package and one provider-native formal artifact under one observation relation | the provider artifact denotes or refines the selected source observations in the stated direction | provider-specific translation/correspondence checker | theorem truth or applicability; another provider's correspondence |
| Q3 environment authentication | exact proof environment, repository/revision, dependency lock, modules, declaration, statement, axiom profile, checker mode | the inspected theorem artifact/environment is exactly the one named | source validation, kernel replay, package manager and digest checks | intended statement meaning, source correspondence, theorem truth beyond stated axioms, or applicability |
| Q4 theorem truth treatment | one exact theorem schema/proposition under one environment and assumptions | theorem is established by a checked proof, or explicitly retained as assumed with exact source validation | proof kernel/certificate checker or explicit assumption policy | that the theorem's subject matches zkc or that assumptions hold |
| Q5 theorem applicability | exact theorem schema, source/target provider subjects, maps, quantifiers, models, resources, side conditions, and loss transform | the theorem statement structurally applies, conditionally, to exactly these subjects | Analysis applicability checker and exact support | theorem truth or the target property; inapplicability is not a negative property |
| Q6 property judgment | one exact experiment/property proposition and complete support partition | the property result has the exact polarity, bound, hypotheses, validation basis, and trust closure | Analysis family checker/transport operation | Compiler preservation, endpoint realization, asymptotic generalization, or assumption truth |
| Q7 Compiler transition | exact predecessor, admitted successor, observer/model, direction, maps, protected observations, and permitted deltas | the one transition satisfies its stated relation | relation owner and/or property-specific validator | source property truth, another observer, search completeness, or backend correctness |
| Q8 property transport | predecessor property, exact Q7 result, preservation theorem/check, and target proposition | the reconstructed successor property follows with exact inherited assumptions/loss | Analysis property transport | unrelated properties or later lowering |
| Q9 OIR correspondence | admitted Protocol/OIR pair and exact projection observation | OIR realizes the stated abstract endpoint semantics | OIR projection checker/validator | concrete backend, cryptographic primitive, ABI, or deployment correctness |
| Q10 realization correspondence | admitted OIR and one target artifact under target semantics | target artifact realizes the exact OIR observations | target-specific validator, proof, or explicit trusted-producer basis | deployed resource/operator state or source-relative invocation without its authorities |

## 3. Where the current implementation sits

The current `FormalizationReceipt` path provides a bounded part of Q3:

- repository and revision pin;
- declaration identity;
- normalized printed statement;
- axiom profile and `sorryAx`-sensitive state; and
- source-drift reproduction for six pinned ArkLib declarations.

Its `covers`/`does_not_cover` and unmatched slots are authored annotations.
They are not Q1, Q2, or Q5. A mechanized receipt contributes no Q4 capability
to the current Soundness Kernel because annotations are structurally excluded
from rule application. Current structural sealing and soundness derivation are
separate current judgments; neither should be relabeled as the target Q0/Q6
without an explicit correspondence.

The selected target specifies generic homes for Q0 and Q3--Q8, including exact
source support, translation/checker contracts, theorem-source validation,
applicability, property transport, transition checking, and residual trust.
It does not yet instantiate Q1/Q2 for a portable formal source package or a
provider artifact, and the implementation does not implement that target.

## 4. Outcome partition at every checked edge

Every Q1--Q10 operation must preserve the owner-defined qualified partition.
The exact available variants differ by owner, but the following distinctions
cannot collapse:

| Outcome class | Meaning at a formal bridge | Forbidden reinterpretation |
|---|---|---|
| Affirmative | the exact formed proposition holds under the retained basis/support | “all nearby properties are verified” |
| Negative | the exact formed proposition is false, with mismatch or counterexample facts | malformed proof, unavailable provider, or unsupported family |
| Unsupported | the exact family, provider, theorem regime, or operation is not implemented | negative property or malformed subject |
| MissingDependency | a required exact named durable preimage is absent after its typed coordinate forms | unavailable live evidence (`CannotAnswer`) or a false semantic proposition |
| CannotAnswer | supported formed question lacks required live evidence, authority, support, or provider result | negative property |
| Refused | invocation, policy, profile, map, subject, or use is prohibited or semantically mismatched | theorem counterexample |
| KindMismatch | typed owner/regime/family/ABI coordinate is wrong | ordinary inapplicability if no question can form |
| Malformed | package, proof, certificate, map, identity body, or framing cannot form | false certificate conclusion |
| DeterministicLimitExceeded | declared finite checker/evaluator control exhausted | CheckerFailure or semantic failure |
| CheckerFailure | checker/provider contradicted its contract or failed operationally without a semantic conclusion | Negative |

For a formed certificate proposition, a certificate verifier returning false
may be a Negative result only when the family contract defines that exact
polarity. A parse error, unsupported calculus, timeout, or checker crash is not
such a negative.

## 5. Trust DAG

### 5.1 Source side

```text
semantic specification/profile laws
  -> canonical subject/body encoding
  -> decoder and identity recomputation
  -> owner admission and view issuance
  -> required-read closure
  -> source-package checker
```

The first F1 implementation may trust some of these components, but every
qualified result must name the residual roots. Differential tests between the
production decoder and an independently written checker are bounded evidence;
they do not prove either implementation. A later verified checker can reduce
the implementation TCB without changing Q1 proposition identity.

### 5.2 Provider side

```text
provider language semantics
  -> zkc-to-provider translation contract
  -> provider artifact elaborator/decoder
  -> proof kernel, program logic, solver, or certificate checker
  -> imported libraries and axioms
  -> theorem declaration and proof
```

VCVio, ArkLib, SSProve, and EasyCrypt produce different DAGs. ArkLib's current
VCVio dependency is part of its environment closure; it does not merge their
adapter or theorem identities. EasyCrypt's Why3/SMT route and Lean kernel-only
route must not share one undifferentiated `FormalProof` assurance class.

### 5.3 Reliance side

```text
checked inert result
  + exact source authority
  + owner result policy
  + consumer trust-acceptance policy
  + named consumer and purpose
  -> fresh attenuated capability
```

A consumer may reject an otherwise affirmative result because its residual
trust includes a solver, an assumed theorem, a custom axiom, a trusted
exporter, or an unverified decoder. Rejection changes reliance, not the
underlying proposition or checked record.

## 6. Assurance classes that must remain distinct

| Pair commonly collapsed | Required distinction |
|---|---|
| proof checked / theorem true unconditionally | a checked proof may depend on exact axioms and cryptographic assumptions |
| theorem true / theorem applicable | truth is about the schema; applicability maps it to exact subjects and quantifiers |
| formal subject well formed / formal subject corresponds to zkc | provider typing does not check the zkc source map |
| source correspondence / cryptographic property | reification preserves meaning but supplies no security proof |
| structural equality / directed refinement | optimization may select or improve behavior under a defined direction |
| trace agreement / probabilistic-distance bound | exact traces and distributions are different observations |
| deterministic replay / causal execution | replay cannot mint strategy nonanticipation or confidential provenance |
| Protocol property / pass preservation | a target can be admitted yet lose the source property |
| pass preservation / endpoint realization | canonical IR correctness stops before target-specific semantics |
| tests/fuzzing / theorem | tests can falsify and bound evidence; they cannot quantify over all subjects |
| extraction / verified translation | generated formal terms require a correspondence theorem or validator |

## 7. Trust-reduction ladder

F0 recommends a ladder rather than one all-or-nothing verification milestone:

1. **explicit trusted adapter:** useful only as a bootstrap and always retained
   as residual trust;
2. **untrusted exporter plus independent checker:** first F1 target;
3. **two independent decoders/checkers plus mutation and differential suites:**
   stronger implementation evidence, still not a theorem;
4. **verified package/correspondence checker or proof-producing checker with a
   small kernel:** removes the checker implementation from the principal TCB;
5. **reusable provider interpretation theorem plus per-package validation:**
   Cogent-like hybrid route;
6. **property-specific verified validators for stable Compiler passes and
   realizations:** narrows artifact-specific trust; and
7. **composed end-to-end theorem over the exact activated interval:** only
   after OIR/Realization and every boundary are included or explicitly
   retained.

Differential fuzzing should enter at steps 2--6 as a falsifier. It is highly
valuable for package decoder parity, manifest omissions, provider mapping,
and pass counterexamples, but it never advances a claim to the next rung by
itself.

## 8. Non-claims

This page does not prove that the dependency graph is complete for every
future property family, implement any Q-level operation, assign a numerical
assurance score, or make temporary labels durable. The graph is a minimum
separation discipline for the F0/F1/F2 program.
