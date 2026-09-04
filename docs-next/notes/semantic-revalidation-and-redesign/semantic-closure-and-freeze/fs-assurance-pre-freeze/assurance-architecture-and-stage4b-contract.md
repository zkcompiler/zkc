# Fiat--Shamir Assurance Architecture and Stage 4B Contract

> **Kind:** Temporary candidate architecture and downstream entry contract
> **Status:** Selected research recommendation; not a published profile
> **Authority:** None. Candidate names below are illustrative and may rotate
> during durable profile publication.

## 1. Selected architecture

The smallest coherent extension is an owner-separated assurance chain:

~~~text
PIR structural result
  + Relations Statement-correspondence result
  + Analysis cryptographic qualifications
  + OIR projection result
  + Realization conformance result
  -> Compiler or deployment policy decision
~~~

No new top-level FS authority is introduced. In particular:

- PIR remains the sole authority for InteractiveCore and the derived
  canonical FS construction;
- Relations remains the sole authority for external Statement and relation
  meaning;
- Analysis owns properties, experiments, assumptions, source validation,
  theorem applicability, and quantitative conclusions;
- OIR owns endpoint semantics and projection correctness;
- Realization owns concrete lowering, providers, parsers, execution, and
  RealizesOir;
- Compiler and deployment policy may consume qualified results but cannot
  reinterpret them.

The extension is primarily a reusable **Analysis profile family**, plus an
explicit Stage 4B intake contract. It is not an FSKernel, TranscriptAuthority,
or semantic MLIR token.

## 2. Why a single FS verdict is the wrong type

Consider four candidates:

1. the exact PIR prefix passes, but two limb streams alias at the concrete
   transition;
2. the transition is injective, but the modulo decoder is biased;
3. the decoder is uniform, but the source IOP lacks the theorem's
   state-restoration property; and
4. every mathematical premise holds, but the parser accepts trailing bytes.

All four require different owners, counterexamples, evidence, and repair
actions. A single StrongFS Boolean must either hide the reason or acquire
authority over unrelated semantics.

The proposed design keeps the results independently addressable and joins
them only for a named goal:

~~~text
Question
  -> exact subject and requested property
Goal
  -> exact experiment, theorem regime, target property, and bound
Proposition
  -> owner-issued sources plus explicit assumptions
Qualification
  -> affirmative, negative, or typed noncompletion
Judgment
  -> exact conclusion for this subject, regime, and use
Policy
  -> reliance decision outside Analysis
~~~

This follows the existing Analysis lifecycle rather than adding another
security-result mechanism.

## 3. Assurance lattice

The end-to-end request is a conjunction of independently owned facts:

| Layer | Candidate judgment | Owner | Typical negative witness |
|---|---|---|---|
| L1 | StructuralPrefixComplete | PIR | omitted, duplicated, substituted, or reordered receipt |
| L2 | ClosedStatementCorrespondence | Relations | missing/extra external Statement route or incomplete cover |
| L3 | LogicalQueryEncodingAdequate | Analysis | two distinct logical query tuples share one encoding |
| L4 | TransitionBindingAdequate | Analysis, with concrete provider fact later from Realization | length/radix/truncation/padding alias |
| L5 | ChallengeSamplerAdequate | Analysis | bias, out-of-range decode, unmodeled exhaustion |
| L6 | OracleProcessCorrespondence | Analysis | only marginals match; adaptive/repeat/off-image process differs |
| L7 | SourcePropertyAndTheoremApplicable | Analysis | absent source property, invalid source theorem, quantifier or loss mismatch |
| L8 | ProjectionCorrect | OIR | static construction, prefix, namespace, sampler, or failure field differs |
| L9 | RealizesOir | Realization | weak query index, provider mismatch, parser remainder, state/failure mismatch |
| L10 | DeploymentApproved | Consumer policy over Realization | wrong ciphersuite/session/resources/threat model |

The layer numbers are explanatory only. Durable identities should refer to
exact owner coordinates, not numeric labels.

## 4. Candidate reusable Analysis profile family

### 4.1 Scope

The candidate family should own L3 through L7. It may consume affirmative L1
and L2 source capabilities and later be consumed alongside L8 and L9. It must
not manufacture any of those foreign-owner results.

One illustrative subject is:

~~~text
FiatShamirAnalysisSubject = {
  exact_protocol_id,
  exact_core_id,
  exact_construction_id,
  exact_checked_same_core_result,
  exact_statement_correspondence_result,
  exact_selected_challenges,
  exact_property_regime,
  exact_target_property
}
~~~

The subject includes IDs only where the Analysis source contract resolves and
checks the corresponding owner-issued views. A raw ID does not grant view
authority or establish admission.

### 4.2 Source manifest

The profile should use a closed read manifest drawn from current owner views:

| Source slot | Required content |
|---|---|
| PIR transcript declaration | Construction/Core identity, initialization, typed frame law, algorithms, state ABI, retry and failure |
| PIR RequiredInfluence | Exact challenge coordinates and ordered required prefix projection |
| PIR challenge transition | Namespace, requested bytes, decoder, acceptance, state advance, draw/retry law |
| PIR checked construction | Same-Core Fresh/FS structural result and exact failure boundary |
| Relations Statement result | Exact complete selected Statement routes and value correspondence |
| Optional Oracle-commitment result | Exact structural source/target correspondence for BCS-like compilation |
| Analysis source property | Special, state-restoration, RBR, RBR-knowledge, HVZK, or other theorem-specific property |
| Theorem source-validation result | Exact theorem/version/proposition and independent validation status |
| Primitive/model declarations | Classical RO, ideal permutation, QROM, or named concrete model |

Every slot is exact-used. Missing, duplicate, extra, substituted, wrong-family,
or wrong-regime sources fail before proposition evaluation. Profiles must not
copy round structure into an Analysis-authored table.

### 4.3 Subquestions

The following are candidate Analysis-local questions. Their names are
descriptive, not proposed stable identifiers.

#### A. LogicalQueryEncodingAdequacy

Inputs:

- exact logical query carrier derived from the PIR construction;
- exact serialized/index carrier visible to the theorem model;
- exact encoder and decoder/range contracts;
- adversarial domain and length bounds.

Affirmative meaning:

- encoding is total on the selected logical domain;
- canonical representations are unique;
- distinct selected logical queries have distinct indices;
- decoding, when required, is distribution-preserving or has an exact
  theorem-compatible law; and
- noncanonical and trailing representations have an explicit refusal rule.

A finite collision search is Evidence, not a universal affirmative judgment,
unless the complete selected domain is finite and exhaustively covered under
the admitted evaluator.

#### B. TransitionBindingAdequacy

Inputs:

- exact semantic frame encoding;
- every adapter from frame bytes/values to primitive input symbols;
- length, padding, radix, limb, range, and reduction laws;
- selected state-transition model and bounds.

Affirmative meaning:

- source-distinct selected transition-input streams cannot alias before the
  modeled primitive under the named property; and
- every bit or field distinction required by the query model reaches the
  state transition.

This question should be factored when appropriate:

~~~text
semantic encoder injective
  AND adapter chain injective/range preserving
  AND primitive-state binding assumption or theorem
~~~

Calling the whole chain collision resistance is permitted only if the exact
primitive property and reduction are supplied.

#### C. ChallengeSamplerAdequacy

Inputs:

- squeeze-output distribution in the selected model;
- decoder and acceptance predicate;
- draw namespace and state-update law;
- retry bound and exhaustion failure;
- theorem-expected challenge law.

Possible affirmative forms must be distinct:

1. total exact uniform;
2. conditional exact uniform plus explicit exhaustion term;
3. bounded statistical distance plus exact loss;
4. theorem-native nonuniform distribution.

The profile must not convert the second through fourth forms into the first.

#### D. OracleProcessCorrespondence

Inputs:

- complete logical query index;
- adaptive query ABI;
- same-index repeat law;
- distinct-index joint law;
- image and off-image behavior;
- query budget;
- adversary and extractor capabilities;
- concrete or ideal primitive model.

Affirmative meaning is process-level correspondence for every admitted
strategy in the bound, not equality of selected outputs or marginal
uniformity. Classical RO, ideal permutation with inverse queries, concrete
hash assumptions, and QROM are different profile variants.

#### E. InteractiveSourceProperty

Inputs:

- exact Fresh or logical-IOP subject;
- exact experiment and adversary;
- Statement/setup timing;
- extractor, restoration, rewinding, or doomed-state interface;
- quantitative parameters.

The result names one property only. Special soundness cannot fill a
state-restoration or RBR slot unless a separately validated implication
theorem applies in the exact direction.

#### F. TheoremSourceValidation

Inputs:

- exact source snapshot and proposition;
- proof dependency closure;
- mechanized or independent validation result;
- known errata, restrictions, and unresolved proof obligations.

Outcomes:

- Affirmative only for the exact validated proposition;
- Negative when a counterexample or proof defect falsifies it;
- CannotAnswer when the selected validation method has insufficient live
  basis;
- Unsupported when no evaluator supports that theorem family.

A citation, familiar theorem name, or successful parsing of a PDF is not
Affirmative.

#### G. TheoremApplicabilityAndTransport

Inputs:

- all preceding qualified results;
- exact theorem source;
- exact source and target experiments;
- adversary/query/setup correspondence;
- quantitative parameters and loss;
- target property.

Output:

~~~text
Qualified FS property judgment
  for exact subject
  under exact regime and assumptions
  with exact bound/loss
  and explicit residuals
~~~

The judgment cannot omit assumptions merely because a deployment policy has
accepted them.

### 4.4 Profile variants

At minimum, the family should distinguish:

| Variant | Primitive/process model | Typical source premise |
|---|---|---|
| Classical multi-round RO | One adaptive lazy random function | Special soundness or theorem-specific source property |
| BCS / commitment-compiled IOP | RO plus exact commitment/opening compiler | State-restoration, RBR, or theorem-specific property |
| Duplex ideal permutation | Mutable random permutation, potentially inverse queries, salt and codecs | State-restoration/knowledge plus codec and HVZK conditions |
| QROM | Quantum-accessible oracle and measure/reprogram interface | QROM-specific source theorem |
| Concrete instantiation | Named hash/sponge/adapter implementation or assumption | A concrete reduction, explicit assumption, or conservative deployment policy |

These variants may share helper propositions. They must not share an
affirmative result merely because their challenge outputs have the same type.

## 5. Qualification and failure semantics

The candidate profile should inherit the existing exact outcome partition:

| Outcome | FS interpretation |
|---|---|
| Affirmative | The exact proposition was established under the named basis and limits |
| Negative | A typed mismatch, counterexample, or false premise was established |
| Unsupported | The exact authenticated family or requested check is not supported |
| MissingDependency | A named durable source, theorem snapshot, model, or artifact is absent |
| CannotAnswer | The request is well formed and supported, but a required live evaluator/capability/basis is unavailable |
| KindMismatch | A supplied coordinate has the wrong owner, family, regime, or ABI |
| Refused | Required authority is absent or the invocation is prohibited |
| Malformed | The request, framing, or finite structure is invalid |
| DeterministicLimitExceeded | The declared bounded evaluator exhausted its limit |
| CheckerFailure | The checking operation failed without a semantic conclusion |

Two rules are essential:

1. Unsupported and CannotAnswer are legitimate non-activation results. They
   must not be converted into a weaker affirmative theorem.
2. A Negative encoding or transition-binding witness blocks the joined claim
   even if every other premise is affirmative.

## 6. Joined security judgment

The joined Analysis result should be mechanically derived from exact
subresults rather than manually asserted:

~~~text
QualifyFiatShamirSecurity(
  structural_source_capability,
  statement_correspondence_capability,
  encoding_result,
  transition_binding_result,
  sampler_result,
  oracle_process_result,
  source_property_result,
  theorem_validation_result,
  theorem_applicability_result,
  exact quantitative inputs)
~~~

The join checks:

- same Protocol/Core/construction and selected challenge set;
- same Statement/setup boundary;
- same query encoding and challenge distribution;
- same adversary and oracle model;
- same theorem version and source-property coordinates;
- complete assumption and loss propagation; and
- no Negative or noncompletion result in a required slot.

It outputs an Analysis property judgment only. OIR projection,
RealizesOir, and deployment approval remain later joins.

## 7. Compiler and deployment policy

A Compiler profile may use qualified Analysis results to select among
semantically valid algorithms or reject a target. It must not turn selection
into proof:

~~~text
semantic profile
  -> qualified Analysis judgment
  -> Compiler selection policy
  -> OIR projection
  -> Realization check
  -> deployment policy
~~~

Example policies:

- a research interpreter may permit a structural-only FS endpoint and label
  all security properties unqualified;
- a classical-ROM experiment may require the complete classical Analysis
  result but not QROM;
- a production verifier may additionally require transition-binding,
  RealizesOir, exact parser, deployment ciphersuite, and side-channel review;
- a post-quantum claim must require the QROM variant rather than accept a
  post-quantum hash choice.

Policy decisions should retain which assumptions they accepted. They do not
erase those assumptions from the underlying judgment.

## 8. Stage 4B entry contract

### 8.1 Static intake

Stage 4B may begin for one FS endpoint only when it receives:

1. an admitted canonical OIR endpoint;
2. an affirmative exact static ProjectionCorrect result;
3. the complete OIR-derived requirement set;
4. exact algorithm and codec declarations;
5. selected proof ABI and failure types;
6. any Analysis-qualified constraints needed by the target; and
7. a target contract naming the intended lowering and runtime regime.

The target contract must state whether security qualification is required for
generation, verification, deployment, or only later consumer reliance.
Structural execution experiments may proceed with unsupported Analysis
properties if they are labeled accurately.

### 8.2 Dynamic semantic surface

The dynamic OIR/Realization boundary must retain at least:

- initialization state and application/session inputs;
- one ordered occurrence for every active semantic frame;
- pre- and post-state for every absorb;
- namespace, requested length, squeeze output, and post-state for every draw;
- decoder input/output and acceptance result;
- retry draw ordinal and state progression;
- SamplingExhausted and every other typed failure;
- challenge values consumed by later computations;
- parser consumption and proof-message/value correspondence;
- terminal result and observable effect trace.

This surface should be expressed as a target semantic relation, not merely a
debug trace. Debug traces may supply Evidence to the checker but cannot define
the source behavior after compilation.

### 8.3 Responsibility handoff

| Handoff | Sender guarantees | Receiver must establish |
|---|---|---|
| PIR to OIR | Complete owner-issued static endpoint view | Independent local target validity and exact ProjectionCorrect |
| Analysis to Compiler | Exact qualified property/bound/assumptions | Policy eligibility only; no reinterpretation |
| OIR to Realization | Admitted endpoint and complete requirements | Concrete preservation under target/provider/parser contract |
| Realization to deployment | Admitted realization and retained assumptions | Exact resource, ciphersuite, session, and threat-model approval |
| Deployment to invocation | Live scoped capability | Per-run input/session binding and typed execution result |

No serialized artifact carries source-view, provider, or deployment authority.
Cold recovery reauthenticates and rechecks the required boundaries.

## 9. SSA lowering

### 9.1 State-threaded core

An SSA lowering should make transcript state an ordinary linear dataflow:

~~~text
state0 = fs.initialize(headers, bindings)
state1, receipt1 = fs.absorb(state0, frame1)
state2, receipt2 = fs.absorb(state1, frame2)
bytes0, state3, draw0 = fs.squeeze(state2, namespace0, length0)
challenge0, accepted0 = fs.decode(bytes0)
state4, receipt3 = fs.absorb(state3, next_frame)
...
~~~

Each state has one definition. A squeeze consumes the exact state after every
required prior absorb. Later challenge use depends on the decoded value, and
later transcript operations depend on the post-squeeze state.

This makes accidental use-before-absorb, stale-state squeeze, duplicated
state fork, and many reorderings inspectable by local dataflow validation.

### 9.2 Optional token-like sequencing

A target dialect may also thread a token-like SSA value:

~~~text
state1, token1 = fs.absorb(state0, token0, frame1)
bytes0, state2, token2 = fs.squeeze(state1, token1, namespace0, length0)
~~~

This is useful when:

- transcript operations have externally visible effects;
- provider calls can throw or consume a resource;
- ordinary value dependencies do not order all observations;
- parser and transcript operations share an effect region; or
- a backend's effect analysis needs one explicit linear chain.

The token must remain a lowering mechanism owned by the target dialect or
Realization. It must not become a second source of transcript membership,
round structure, challenge identity, or security meaning.

### 9.3 What SSA and tokens do not prove

Even perfectly linear state/token SSA does not prove:

- the application declared the complete Statement;
- the source DerivedPrefix is the correct mathematical dependency;
- frame or adapter encoding is injective;
- the primitive transition is collision resistant;
- decoding is unbiased;
- the source property or theorem holds;
- the lowering implements the exact provider ABI; or
- the parser rejects every alternate proof representation.

Those are separate propositions consumed by the realization check.

## 10. Target-specific RealizesOir relation

For an FS target, RealizesOir should compare more than accepted proof results.
At minimum it should relate:

| Facet | Required correspondence |
|---|---|
| Construction and algorithms | Exact construction ID and exact absorb/squeeze/advance/decode uses |
| Logical query | Same session, instance, typed frames, order, namespace, requested length, and draw |
| State | Target pre/post states follow the selected abstract transition or named refinement |
| Challenge | Exact decoder/acceptance behavior and typed value |
| Retry/failure | Same draw count, namespaces, state progression, and failure classification |
| Proof ABI | Every proof field is decoded under the selected codec and reaches its semantic occurrence |
| Parser | Canonical input and exact end-of-input; malformed/trailing data has the specified result |
| Terminal behavior | Same acceptance/rejection/failure and relevant observations |
| Effects | Same allowed order and no extra transcript/provider effect |

The checker may use one of three bases:

1. **Translation validation:** independently validate each emitted artifact
   against the exact relation.
2. **Verified producer theorem:** rely on a separately proved general
   compiler-refinement theorem and check that this producer/artifact lies in
   its correspondence domain.
3. **Named trusted producer:** retain a visible residual assumption when no
   smaller independent checker exists.

Build success, test vectors, and differential tests remain bounded Evidence.
They may discover mismatches and support engineering confidence, but only the
selected exact basis may establish RealizesOir.

## 11. Parser and serializer contract

Transcript encoding and proof serialization are related but distinct:

- transcript encoding determines the logical query to the challenge process;
- proof serialization transports prover messages and other proof values;
- parsing reconstructs typed values that then enter the transcript and
  verifier checks.

The Stage 4B proof ABI should require:

- one canonical encoding for every admitted proof value;
- exact field order, type, length, range, and version;
- no ambiguous optional/default/trailing-zero representation;
- decoder behavior consistent with the theorem's distribution premises where
  random encodings are involved;
- parser/serializer round-trip laws on canonical values;
- refusal of noncanonical encodings;
- exact end-of-input; and
- negative corpora for truncation, extension, reordering, duplicate fields,
  range overflow, alternate encodings, and parser/serializer disagreement.

Absorbing parsed values through canonical transcript frames does not excuse a
parser that accepts two proof encodings when protocol or deployment semantics
require uniqueness.

## 12. BCS Stage 4B specialization

A BCS-like endpoint needs two linked but distinct lowerings:

1. the Oracle-commitment elaboration must realize commitment publication,
   coin-derived query positions, openings/authentication paths, and checks; and
2. canonical FS must realize the challenge process over that independently
   admitted concrete Core.

The assurance join additionally requires:

- commitment/opening binding assumptions or theorem;
- the source IOP's exact state-restoration/RBR property;
- BCS theorem validation and applicability;
- Merkle/domain-separation and query-index correctness;
- random-oracle process correspondence and query count;
- quantitative soundness/knowledge loss; and
- implementation preservation of both the commitment compiler and FS
  endpoint.

A verified noninteractive verifier can close the last implementation relation
without closing the preceding cryptographic premises.

## 13. Duplex Stage 4B specialization

The duplex sibling requires a distinct endpoint profile with:

- proof-tuple parser and salt position;
- exact salt source, length, scope, and uniqueness law;
- raw prover-message wire codec and transcript encoder correspondence;
- mutable rate/capacity state, partial squeeze, and unread-output behavior;
- decoder fibers and bias;
- permutation and inverse-query provider model;
- query budgets and failure behavior; and
- exact correspondence to the independently validated duplex theorem.

Canonical-framed headers and namespaces must not be silently inserted into the
paper construction, and the paper's raw codecs must not be silently treated as
canonical-framed query encodings. Either change forms a different
construction and theorem target.

## 14. QROM specialization

A QROM target adds:

- quantum query capability and resource accounting;
- coherent query-domain representation;
- exact measurement/reprogramming interface used by the reduction;
- ordered multi-round extraction law;
- disturbance and query-loss terms;
- QROM theorem source validation and applicability; and
- a correspondence from the PIR-derived logical query to the theorem's
  quantum oracle index.

No concrete post-quantum hash choice fills these slots. Until the distinct
profile is affirmative, the exact outcome is Unsupported,
MissingDependency, or CannotAnswer according to the available basis.

## 15. Negative validation program

Every durable profile or checker should ship with same-boundary positive and
negative cases:

| Boundary | Required mutation families |
|---|---|
| PIR | omitted, duplicated, reordered, substituted, late, wrong-scope, wrong-kind frame; irrelevant-message positive control |
| Relations | omitted/extra/substituted Statement route; partial/overlapping selector; complete-cover positive control |
| Encoding | boundary concatenation, type confusion, alternate canonical form, trailing zero, radix/range/high-bit aliases |
| Sampler | bias, out-of-range result, retry/exhaustion omission, namespace reuse |
| Oracle process | repeat inconsistency, correlated distinct indices, off-image mismatch, query-count drift |
| Theorem | wrong source property, wrong direction implication, theorem version change, quantifier/setup mismatch, missing loss term |
| OIR | construction/frame/prefix/namespace/algorithm/sampler/failure substitution |
| Realization | stale state, weak index, provider mismatch, parser remainder, serializer disagreement, changed failure |
| Deployment | ciphersuite/session/application mismatch, unsupported threat model, stale provider/resource binding |

One mutation passing at the wrong layer is a profile or checker defect. One
mutation failing at an unrelated earlier layer is not evidence that the
intended boundary is covered.

## 16. Minimum durable changes

The research recommends only the following semantic commitments before or
immediately after freeze:

1. preserve the current PIR construction and its explicit cryptographic
   nonclaims;
2. retain exact Interface/Relations Statement coverage and document the
   application-manifest premise;
3. publish a reusable Analysis FS assurance family using existing
   Question/Goal/Proposition/Qualification/Judgment machinery;
4. keep classical RO, BCS/RBR, duplex ideal-permutation, QROM, and concrete
   instantiation variants distinct;
5. preserve every selected FS coordinate in OIR;
6. define dynamic Stage 4B and target-specific RealizesOir before endpoint
   activation; and
7. let Compiler/deployment policy consume exact qualified judgments without
   changing their meaning.

Everything else in this chapter is an implementation and research program
under those boundaries, not a new semantic authority.
