# Stage 4A integrated scenario results

> **Document kind:** Temporary comparative scenario record
> **Document state:** Stage 4A.3--4 post-repair evaluation; Candidate B remains
> the research-leading hypothesis and is not selected
> **Authority:** None. These scenario evaluations do not define an Analysis or
> Compiler judgment, establish a property or compilation result, admit a
> subject, mint a capability, report implementation support, authorize
> migration, or change current normative authority.
> **Basis:** The Stage 4A charter, frozen Stage 3 intake, current-model
> reconstruction, primary-source research, design forces, and the
> equal-resolution [candidate portfolio](candidate-models.md)
> **Portfolio audit state:** The repaired candidate portfolio passed its
> independent equal-resolution closure audit. These results are now eligible
> convergence inputs, but remain comparative findings rather than a selected
> architecture.
> **Disposition:** Retain reviewed scenario decisions, falsifiers, alternative
> dispositions, and reversal triggers in the convergence record; absorb target
> contracts into durable owners; delete this page with the temporary package.

## 1. Purpose and method

This page pressure-tests all five integrated candidates against the same exact
inputs, authorities, requested results, consumer behavior, and falsifiers. It
does not count safe refusal as useful support and does not manufacture a hard
failure merely because a candidate chooses a narrower supported surface.

The candidates are:

| Code | Candidate |
|---|---|
| A | Extended Soundness Kernel and Enumerated Compiler |
| B | Federated Typed Analysis and Validated Decision Compiler |
| C | Universal Claim IR and Proof-Carrying Transform Graph |
| D | External-Prover-Centric Obligation Compiler |
| E | Certified Relational Synthesis and Symbolic Optimization |

Verdicts use `P`, `C`, `S`, and `F` as defined in the
[validation matrices](validation-matrices.md#2-verdict-interpretation). A
verdict evaluates the written architecture, not an implementation. `C` means
that the exact family model, adapter, certificate language, or checker remains
an unclosed obligation; until it closes, the only correct runtime result is a
qualified non-result. `S` is safe but does not satisfy the scenario's positive
capability opportunity.

## 2. Chartered scenarios

These are the nineteen scenarios fixed by the Stage 4A charter.

### C01. Structurally equal Protocols with an incomplete or ill-typed map

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Exact admitted Protocols `P` and `Q`, owner-created equality views, and an unauthoritative proposed occurrence/value map `M`. In one variant `M` is ill-typed or falsely declares totality; in the other it is a valid partial hint but the family requires a complete map. |
| Expected qualified result and capability | The ill-typed or falsely total question is `Malformed`. A well-typed but insufficient question is `CannotAnswer` or an exact refusal for missing required input. Neither result mints equality, inequality, or negative capability. |
| Consumer behavior | Compiler leaves the relation assessment unavailable and cannot treat either non-result as semantic ineligibility. A corrected exact question is a new attempt. |
| Falsifier | Analysis fills the map from ambient state, infers equality from target identity, or turns map failure into a negative semantic judgment. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C02. Trace equality changes with the observer

| Field | Evaluation |
|---|---|
| Exact setup and authorities | The same admitted pair `P`, `Q` under one exact trace model. Public observer `O_pub` sees equal traces; diagnostic observer `O_dbg` sees one different event. Each observer and trace projection is an exact owner-defined operand. |
| Expected qualified result and capability | `TraceEq[O_pub]` is affirmative. `TraceEq[O_dbg]` is negative with an exact counterexample when its checker is complete. Their questions, propositions, and capabilities are distinct. |
| Consumer behavior | A public-trace constraint accepts only the public capability. A diagnostic preservation constraint consumes the diagnostic negative and rejects the pair. |
| Falsifier | Observer identity is omitted, or one result is reused under the other observer. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | C | C | C |

### C03. Directed refinement with intentional verifier-visible change

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Admitted source and target Protocols; target introduces one verifier-visible audit effect. One question requests directed refinement under a protected observer. A separate admitted `ChangeContract` declares exactly that effect permitted while protecting all others. |
| Expected qualified result and capability | Protected `TraceRefines[source,target,O]` is negative. The separate exact `ChangeConforms(source,target,ChangeContract,O,model,maps)` proposition may be affirmative. Neither the declaration nor conformance result changes refinement's direction or meaning. |
| Consumer behavior | A request explicitly permitting the audit effect may consume the affirmative `ChangeConforms` capability; the `ChangeContract` alone grants nothing, and an ordinary preservation constraint must reject the target. |
| Falsifier | The label “intentional” implies refinement, protected effects disappear, or direction is reversed. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | C | C | C |

### C04. Distributional closeness retains abort mass

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Admitted Protocols under an exact subdistribution model, input distribution, correlation regime, measurable projection, distance metric, and direction. The source terminates normally; the target aborts with mass `delta`. |
| Expected qualified result and capability | `DistributionEq` is negative. `DistributionClose <= delta` may be affirmative. A requested bound smaller than `delta` is negative when the procedure is complete. Every capability retains the metric and abort policy. |
| Consumer behavior | Compiler compares only results with compatible probability models, metrics, direction, and conditioning policy. |
| Falsifier | The checker conditions on success, renormalizes away aborts, drops failure mass, or compares incompatible metrics. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

### C05. Conditional soundness with explicit hypotheses and bound

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Exact admitted Protocol and relation operands, property-family view, adversary/oracle experiment, resources, typed hypotheses, rule basis, and quantitative derivation. |
| Expected qualified result and capability | An affirmative conditional claim of the form `H => Adv <= epsilon(q,t)` with every inherited hypothesis, exact resource substitution, and dimensioned expression retained. It is not an unconditional property. |
| Consumer behavior | Compiler may accept the capability only when request policy accepts the exact hypotheses, model, and bound predicate. |
| Falsifier | A hypothesis disappears, a model is coerced, or probability, time, query, round, field-size, and byte dimensions mix. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | C | C | C |

### C06. Unsuccessful derivation search without completeness

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A well-formed supported question and exact basis profile; bounded derivation search finds no proof and has no completeness theorem. The search process has no semantic authority. |
| Expected qualified result and capability | `CannotAnswer(SearchIncomplete)` plus an attempt record. No affirmative or negative semantic capability is minted. |
| Consumer behavior | A required Compiler assessment remains incomplete. Closed `NoEligibleCandidateIn<D,Q>` is unavailable unless a different complete basis classifies the member. |
| Falsifier | Search failure becomes property negation, candidate ineligibility, or closed `NoEligibleCandidateIn<D,Q>`. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C07. Checked external theorem without zkc correspondence

| Field | Evaluation |
|---|---|
| Exact setup and authorities | An external theorem name or proof artifact, exact external environment, and successful external proof check. The exact external-statement, symbol/model, or sufficient-implication correspondence to the zkc question is missing. |
| Expected qualified result and capability | The proof-check result may be retained as a basis sub-result. Final Analysis is `CannotAnswer(MissingCorrespondence)` and mints no zkc claim capability. |
| Consumer behavior | Compiler cannot use the external receipt as a property or relation input. |
| Falsifier | A theorem name, digest, proof file, repository, or prover exit status directly mints zkc authority. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C08. Structural Fiat--Shamir construction without theorem basis

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Admitted Fresh and Fiat--Shamir Protocols, admitted transcript construction, and affirmative `CheckedFSConstruction` with exact maps. No applicable theorem/model basis exists. |
| Expected qualified result and capability | FS theorem instantiation, or `FSCompile` if that name is retained, is `Unsupported` or `CannotAnswer`. It exposes no property port. Direct target analysis remains a separate possible lane. |
| Consumer behavior | A source property cannot qualify the target through the structural capability. |
| Falsifier | Structural FS construction transports security, knowledge, completeness, or zero knowledge by default. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C09. Two property transports over one FS construction

| Field | Evaluation |
|---|---|
| Exact setup and authorities | One exact checked construction. Soundness port uses a classical-ROM theorem with assumptions `H_s` and loss `L_s`; knowledge port uses a QROM theorem with different assumptions `H_k` and loss `L_k`. Exact source-property capabilities are supplied. |
| Expected qualified result and capability | Distinct theorem-instance, basis, property-port, and target-claim identities. Each port accepts only its exact source family and produces the exact target result with retained losses and hypotheses. |
| Consumer behavior | Compiler must request and consume the precise transported property. A mismatched source result is a typed refusal, not approximate evidence. |
| Falsifier | One generic “preserves security” capability, blended assumptions, or shared loss. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | C | C | C |

### C10. Property composition with shared challenges and intentional change

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Independently admitted children and target, affirmative `CheckedCoreComposition`, exact child occurrences and property judgments, shared challenge/randomness map, captured failure/reach behavior, terminal policy, one admitted `ChangeContract`, and its exact affirmative `ChangeConforms` capability. |
| Expected qualified result and capability | Without a theorem covering the exact sharing and conforming declared change: `CannotAnswer`. With one: a property-specific target result retaining occurrence maps, the contract and conformance premise, assumptions, and combined bound. Child occurrence capabilities are non-substitutable. |
| Consumer behavior | Compiler accepts only the exact target-property capability, never the child set or structural composition alone. |
| Falsifier | Independence is assumed implicitly, the declaration is treated as conformance, or structural composition yields property composition. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

### C11. Occurrence-local relation satisfaction and private witnesses

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Exact admitted relation definition, interface, instance, and interpretation regime; two occurrence identities; two private process-local witness assignments, one satisfying and one not. Correspondence and admission are separate facts. |
| Expected qualified result and capability | Exactly one semantic owner. The satisfying occurrence receives an affirmative confidential capability. The other may receive a private fact-retaining negative only from a complete checker. No public judgment identity or record exposes witness bytes. |
| Consumer behavior | Completeness or knowledge analysis consumes only the exact occurrence capability. It cannot reuse it at another occurrence. |
| Falsifier | Correspondence implies satisfaction, secret bytes enter public identity, or one witness capability becomes global. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | C |

### C12. Identity-preserving and content-changing proposals

| Field | Evaluation |
|---|---|
| Exact setup and authorities | One admitted source; one unauthoritative proposal produces source-identical content and one produces changed content. Proposal labels, recipes, maps, and certificates are hints only. |
| Expected qualified result and capability | PIR independently authenticates and admits each target. The identity case may obtain exact Protocol equality; the changed case requires its requested directed or intentional-change relation. Proposal identity does not identify the semantic target. |
| Consumer behavior | Compiler creates a transition case only after target admission and exact relation checking. |
| Falsifier | Producer labels or target admission establish the predecessor/successor relation. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | P |

### C13. Well-formed proposal whose target admission fails

| Field | Evaluation |
|---|---|
| Exact setup and authorities | One `DeclaredAlternativeId` in an exact frozen `ProposalScope` yields bytes that fail PIR authentication or admission. PIR alone owns the exact negative result. |
| Expected qualified result and capability | No admitted target, transition case, relation question, or `CandidateId` exists. The total `AlternativeResolutionLedger` may record `ConclusivelyExcluded` from the exact PIR fact for that declared alternative. Only checked total alternative-resolution coverage and the canonical-image rule can later establish the resulting `CandidateDomain`; the failed attempt by itself establishes neither proposal-scope coverage nor closed candidate absence. |
| Consumer behavior | Proposal-scope closure accounts for the failed declared alternative in the alternative-resolution ledger. It does not insert that alternative into `D`, `Q`, or an assessment ledger, and it cannot silently omit the entry while claiming total resolution. |
| Falsifier | Relation checking raw target bytes, minting a candidate, treating the failed alternative as a member of `D`, or dropping its resolution entry while retaining completeness. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C14. Negative, unsupported, and failed transform relations

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Three declared alternatives in one exact frozen `ProposalScope` yield independently admitted targets. Checking the exact affirmative transition propositions returns, respectively, a family-specific exact negative, `Unsupported`, and `CheckerFailure`. |
| Expected qualified result and capability | The exact negative may conclusively exclude its declared alternative from candidate formation. `Unsupported` and `CheckerFailure` remain unresolved `AlternativeResolution` entries; they are not negative transition facts and do not enter `D`. Unless another resolved alternative exists, no `CandidateId`, qualification-resolution entry, member of `Q`, or candidate assessment exists for these three alternatives. The unresolved entries block a closed scope-derived candidate-domain claim and therefore block `NoEligibleCandidateIn<D,Q>`. |
| Consumer behavior | The total `AlternativeResolutionLedger` preserves all three qualified outcomes without Boolean coercion. Assessment begins only for comparison alternatives derived from admitted, relation-qualified members of a separately checked `D`. |
| Falsifier | All outcomes collapse into “invalid candidate,” unresolved alternatives are inserted into `D` or an assessment ledger, or the three outcomes support the same closed no-selection conclusion. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C15. Negative Analysis result under positive and negative constraints

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A complete Analysis procedure returns exact negative `TraceEq[O]` with a scoped counterexample. Two requests differ only in constraint polarity: `RequireChange[O]` and `PreserveTrace[O]`. |
| Expected qualified result and capability | The negative capability may satisfy the explicitly negative constraint. It cannot satisfy the affirmative constraint, which rejects the transition. |
| Consumer behavior | Constraint typing retains family, model, observer, and polarity. |
| Falsifier | Generic Boolean false is reusable under either constraint. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | P |

### C16. Incomplete producer search cannot establish `NoEligibleCandidateIn<D,Q>`

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A resource-bounded heuristic producer stops after finding no proposal or only some exact feasible candidates. It has no checked closure basis. |
| Expected qualified result and capability | `IncompleteSearchReport`, `QualifiedFeasibleCandidate`, or `NondominatedInAssessedSubset`, depending on what was validated. None carries domain closure, optimality, complete-frontier, or closed-absence authority. |
| Consumer behavior | A consumer may use a feasible result under an explicitly open comparison claim; it cannot treat it as best or exhaustive. |
| Falsifier | “Found none” becomes `NoEligibleCandidateIn<D,Q>`, or a partial explored set becomes the complete domain. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C17. Complete finite domain with equal scores

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Checked total alternative resolution and canonical-image closure establish an exact finite semantic `CandidateDomain D` with two admitted, relation-qualified `CandidateId` values. A total `QualificationResolutionLedger` derives a checked closed `ComparisonAlternativeDomain Q`. Every member of `Q` has a complete assessment-input portfolio, separate affirmative portfolio-completeness result, exact use edges, and decision-complete assessment; the two candidates have equal typed objective vectors. Provider enumeration order is deliberately permuted. |
| Expected qualified result and capability | `BestInEnumeratedClosedDomain<D,Q>` retains the complete optimal-equivalence class. The declared comparison and representative policy then chooses the canonical representative and its exact comparison alternative before unique projection to one semantic `CandidateId`; an intended user priority must instead be an explicit `DeclaredPolicyPreference` objective. The result is invariant under incidental provider order. |
| Consumer behavior | Cold replay reconstructs `D`, the qualification ledger, `Q`, portfolio bodies, completeness and use results, assessments, comparator, optimal-equivalence class, and representative policy. |
| Falsifier | Enumeration ordinal, hash-table order, scheduling, or an undeclared preference silently decides the representative; or a best claim omits closure of either `D` or `Q` or complete assessment of `Q`. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C18. Endpoint feasibility is not a hidden Compiler criterion

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Compile request omits Stage 4B endpoint feasibility. An ambient endpoint registry would reject the target, but no exact Stage 4B result is a request operand. |
| Expected qualified result and capability | Compiler evaluates only declared Protocol-semantic constraints and objectives and may select the target. The decision explicitly makes no endpoint claim. |
| Consumer behavior | Stage 4B may later return a separate negative feasibility result. It does not retroactively change the Stage 4A comparison meaning. |
| Falsifier | Ambient endpoint state secretly filters or reorders candidates. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### C19. Serialized records do not preserve live authority

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Exact derivation or decision replay bundle is persisted, the process and live capabilities are destroyed, and the bytes are loaded under a fresh process. |
| Expected qualified result and capability | Loaded data are inert. Replay reauthenticates subjects, reloads exact bases, rechecks admissions, relations, Analysis, domain, and decision, then mints fresh process-local capabilities. Missing dependencies produce replay failure. |
| Consumer behavior | Consumers accept only freshly reconstructed live capabilities, not IDs, signatures, receipts, or serialized tokens. |
| Falsifier | Deserialization, digest equality, signature, or cache hit rehydrates authority. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

## 3. ZK-specific pressure scenarios

### Z20. Property notions do not form an implicit subtype lattice

| Field | Evaluation |
|---|---|
| Exact setup and authorities | An exact plain-soundness judgment exists. Knowledge soundness, special soundness, RBR, and state-restoration questions lack their exact extractors, games, or theorem instances. |
| Expected qualified result and capability | The unavailable questions are `Unsupported` or `CannotAnswer`. A matched theorem may derive only its exact stated direction under its relation/language projection and side conditions. |
| Consumer behavior | Every consumer requests one exact property family and regime. |
| Falsifier | Generic `Security`, inheritance by property name, or plain soundness satisfying knowledge. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | C | C | C |

### Z21. RBR aggregation is theorem-specific

| Field | Evaluation |
|---|---|
| Exact setup and authorities | One per-round error vector is interpreted under two exact theorem profiles: one concludes a sum and another concludes `1 - product(1 - epsilon_i)` under different definitions and premises. |
| Expected qualified result and capability | Separate source profiles, theorem bases, propositions, and results. No aggregate is intrinsic to the raw vector. |
| Consumer behavior | A consumer chooses the exact aggregate theorem rather than projecting a canonical scalar. |
| Falsifier | Universal sum, maximum, or product normalization is built into the result family. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

### Z22. Classical ROM does not imply QROM

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A classical-ROM FS theorem instance and exact source property are available. The requested target property is quantum-ROM with superposition queries and a quantum adversary profile. |
| Expected qualified result and capability | Without an exact QROM theorem, the request is `Unsupported` or `CannotAnswer`; the ROM capability is non-substitutable. |
| Consumer behavior | Compiler rejects the ROM property port from a QROM constraint. |
| Falsifier | QROM is modeled as a stronger Boolean setting or inherits classical reduction steps. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | C | C | C |

### Z23. Fiat--Shamir with aborts and unbounded retry

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Structural FS construction is affirmative. The target uses rejection sampling or potentially unbounded retry, while the proposed theorem covers a one-shot or differently conditioned experiment. |
| Expected qualified result and capability | The theorem instantiation is `CannotAnswer` until retry, expected runtime, termination, accepted/rejected transcript programming, and conditioning correspond exactly. |
| Consumer behavior | No soundness, knowledge, or ZK transport occurs through the structural result. |
| Falsifier | Rejected transcripts, retry count, conditioning mass, or nontermination disappear. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

### Z24. Duplex transcript and codec parameters are semantic inputs

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Two admitted FS targets differ in transcript codec, domain separator, salt, rate, capacity, or oracle-state construction. A theorem instance corresponds to only one exact configuration. |
| Expected qualified result and capability | The matching target may obtain an exact property port. The other is `CannotAnswer` or `Unsupported` despite using the same nominal hash or permutation family. |
| Consumer behavior | Property constraints match exact construction/model identity. |
| Falsifier | “Same hash,” equal proof bytes, or empirical trace similarity substitutes for theorem applicability. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

### Z25. Zero knowledge is observer- and schedule-indexed

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Exact child single-session or sequential ZK judgments; a structurally admitted parallel or interleaved composition shares verifier auxiliary input, challenges, or programmable-oracle state. |
| Expected qualified result and capability | Without an exact simulator-composition theorem for the observer and schedule, target ZK is `CannotAnswer`. A complete distinguishability procedure may instead return an exact negative counterexample. |
| Consumer behavior | Structural composition and child ZK cannot satisfy the target ZK constraint. |
| Falsifier | Generic `ZK(children) => ZK(composite)` or observer/schedule erasure. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

### Z26. Concrete security does not automatically lift to asymptotic security

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Exact concrete advantage bound over finite resources; request asks for a negligible asymptotic conclusion. Parameter family, feasible-adversary class, and eventual side conditions are absent in the first variant and exact in the second. |
| Expected qualified result and capability | First variant is `CannotAnswer`. Second may derive a new asymptotic claim through a named lift with all side conditions retained. |
| Consumer behavior | Concrete and asymptotic capabilities remain distinct. |
| Falsifier | A small finite number, syntactic polynomial, or extensional equality silently becomes negligible or feasible. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

### Z27. Knowledge is occurrence-, adaptivity-, and extractor-indexed

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A static straightline knowledge judgment exists for relation occurrence `i` and extractor `E`. A request changes the occurrence, selects instances adaptively, or requires rewinding/state-restoration access. |
| Expected qualified result and capability | Existing capability is non-substitutable. A new exact theorem/model basis is required; otherwise the request is `CannotAnswer`. Relation satisfaction at one occurrence does not establish knowledge. |
| Consumer behavior | Compiler matches occurrence, relation, adaptivity, extractor access, abort policy, and resource profile exactly. |
| Falsifier | Quantification, occurrence, extractor, or access mode is treated as decorative metadata. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | C | C | C |

## 4. Capability-expanding opportunity scenarios

### O28. Multiple proof bases establish one semantic claim

| Field | Evaluation |
|---|---|
| Exact setup and authorities | An internal derivation and an externally checked proof with complete correspondence establish exactly the same policy-read Analysis property proposition and residual hypotheses under different validation bases. The candidate's required admission and transition propositions were qualified independently. |
| Expected qualified result and capability | One `AnalysisPropositionId`; distinct semantic-basis, validation-basis, support-instantiation, derivation, judgment-record, replay-bundle, and live-capability identities. Compiler retains one semantic `CandidateId`. Its immutable `AssessmentInputPortfolio` body records the exact Analysis result support required by policy; distinct `AssessmentInputUse` edges bind accepted facts to that candidate and policy schema, and a separate completeness result checks required corroboration, assurance, and residual-trust coverage. Generic property support does not create a transition `QualificationId`, enlarge `Q`, or create another semantic candidate. |
| Consumer behavior | A declared assessment-input policy may require corroboration or choose an accepted trust basis through the exact portfolio, use, and completeness path. Only when the proposition itself is an exact required transition proposition does its support participate in transition qualification and qualification resolution. |
| Falsifier | Proof choice changes claim meaning, generic property support silently changes `D` or `Q` cardinality, or the portfolio body asserts its own completeness. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | C |

### O29. Direct target analysis and property transport are separate bases

| Field | Evaluation |
|---|---|
| Exact setup and authorities | One policy-read target property is established by direct target analysis and by checked source-to-target property transport. The candidate's admission and required transition propositions are qualified independently. In one variant the property result and residual hypotheses coincide; in another the bounds or residual hypotheses differ. |
| Expected qualified result and capability | Coincident conclusions with the same residual hypotheses share one `AnalysisPropositionId` and have distinct bases and support instantiations. Different bounds or residual hypotheses produce distinct propositions over one transition case. The exact owner result records enter the immutable `AssessmentInputPortfolio`; separate `AssessmentInputUse` edges establish candidate-and-schema association, and a separate completeness result checks the policy-required property coverage. No automatic minimum, assumption intersection, or unconditional strengthening occurs. |
| Consumer behavior | Compiler applies the exact assessment-input policy to the portfolio, use, and completeness results without turning a generic property basis into a transition qualification, comparison alternative, target identity, or semantic candidate identity. If an exact transport proposition is itself declared as a required transition proposition, only that proposition follows the transition-qualification path. |
| Falsifier | A generic derivation path creates semantic candidates or members of `Q`, the portfolio certifies itself, incompatible bounds are minimized, or hypotheses are silently combined. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | C |

### O30. Adding one property family does not perturb unrelated identities

| Field | Evaluation |
|---|---|
| Exact setup and authorities | An unsupported ZK profile or new checker is added without changing any input read by existing TraceEq or Soundness questions. Old replay bundles remain available. |
| Expected qualified result and capability | Existing question, proposition, semantic-basis, validation-basis, and replay-bundle identities remain stable. The new family is exactly `Unsupported` until its semantic profile, basis registry, and validation profile close. |
| Consumer behavior | Existing consumers need no global requalification for an unread extension. |
| Falsifier | Aggregate catalog, global logic, or ambient prover version changes unrelated proposition meaning or invalidates replay without an exact dependency. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| F | P | C | C | C |

### O31. Symbolic finite-domain optimality certificate

| Field | Evaluation |
|---|---|
| Exact setup and authorities | An exact but large finite grammar has already been materialized into a canonical image of PIR-admitted, transition-qualified `CandidateId` values. Exact membership and duplicate rules, constraints, objective, and separate symbolic closure, assessment, and optimality certificates describe that admitted image. |
| Expected qualified result and capability | In v0, independently checked certificates may compress reconstruction of the already materialized candidate image, qualification expansion, repeated assessment, closure, and `BestInCertifiedSymbolicDomain<D,Q>` or exact infeasibility. They cannot avoid target materialization, PIR admission, transition qualification, or closed derivation of comparison domain `Q`. Invalid or unsupported certificates yield no optimality or `NoEligibleCandidateIn<D,Q>`. |
| Consumer behavior | The decision consumer relies on the exact admitted candidate image, domain proposition, certificate bases, and qualification policy, not solver status. A stronger lazy denotation over unnamed or unadmitted targets requires a future Stage 3 reopening and is not a v0 result. |
| Falsifier | Symbolic syntax, solver success, unproved pruning, or a certificate over unmaterialized targets implies candidate identity, PIR admission, transition qualification, or domain closure. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| S | P | P | C | P |

### O32. Anytime feasible choice and partial frontier

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Nondeterministic heuristic search yields successive exact admitted, related, and assessed feasible candidates but never proves domain closure. |
| Expected qualified result and capability | `QualifiedFeasibleCandidate`, `NondominatedInAssessedSubset`, or `IncompleteSearchReport`, each scoped to its exact admitted candidate or assessed subset. A later run may improve the result without falsifying the earlier bounded claim. None mints candidate-domain closure, comparison-domain closure, global frontier, optimality, or `NoEligibleCandidateIn<D,Q>` authority. |
| Consumer behavior | Consumers may use the exact bounded feasibility or assessed-subset nondominance claim when their policy accepts that scope. No consumer may treat any open report as an optimality capability. |
| Falsifier | Feasible means optimal, a partial frontier means complete, an “open optimality” authority is invented, or interruption means infeasible. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### O33. Proposal producers are replaceable

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Manual, MLIR, e-graph, and learned producers yield the same declared proposals, admitted targets, and exact domain. Producer provenance is retained only as attempt metadata. |
| Expected qualified result and capability | Admissions, relations, assessments, and decision are unchanged. A new producer can enlarge a complete domain only through a new checked closure basis. |
| Consumer behavior | Compiler and replay do not rerun or trust a mutable discovery engine. |
| Falsifier | Adding a producer expands semantic authority or silently changes completeness and selection meaning. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | P |

### O34. Semantic checkpoints differ from producer-internal IR

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A producer uses many MLIR or e-graph nodes internally. Some nodes are only operational; two named intermediates are claimed as Protocol-semantic transform steps. |
| Expected qualified result and capability | Operational nodes remain unauthoritative and need no Protocol admission. Every semantic intermediate is independently admitted and every adjacent claimed edge checked. |
| Consumer behavior | Compiler may also request an end-to-end relation, but it cannot use that result to erase semantically read adjacent steps without a rule. |
| Falsifier | All internal nodes become Protocols, or a semantically claimed intermediate remains unadmitted. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | P |

### O35. Evidence-derived objectives remain epistemically qualified

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Evidence supplies measurements bound to exact target, hardware, software, procedure, sampling, uncertainty, and time. Request explicitly declares an `EvidenceDerivedEstimate` objective. |
| Expected qualified result and capability | Compiler may compare compatible measurements under the exact objective policy. The measurement does not mint an Analysis cost theorem or Stage 4B feasibility capability. If absent from the request, it is ignored. |
| Consumer behavior | Decision reports the objective's Evidence qualification and residual uncertainty. |
| Falsifier | Environment-free benchmark values become timeless semantic scores or hidden endpoint filters. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | P |

### O36. Cache entries become stale under basis drift

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A cache stores an affirmative relation, Analysis, or domain result under model/checker basis `v1`; current replay uses `v2` or a changed dependency closure. |
| Expected qualified result and capability | The entry is only a hint. Exact basis comparison rejects or revalidates it. Matching bytes do not mint authority. |
| Consumer behavior | Replay either reconstructs a fresh result under `v2` or reports unavailable replay. |
| Falsifier | Cache-key equality or prior receipt establishes current validity. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | P | P |

### O37. The same target through semantically different paths

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Two checked transform paths reach the same admitted target. Relations, intentional effects, or a path-read cost/property differ. |
| Expected qualified result and capability | Distinct transition cases whenever the path is semantically read. Deduplication is permitted only through an explicit quotient policy proving path and basis irrelevant to every constraint, objective, replay, and consumer. |
| Consumer behavior | Compiler compares the exact transition cases or applies the declared quotient. |
| Falsifier | Target identity alone deduplicates semantically different paths. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | P |

### O38. Counterexamples can guide but not validate production

| Field | Evaluation |
|---|---|
| Exact setup and authorities | A family-specific negative result retains an exact trace, observer, input, or witness counterexample. An unauthoritative producer uses it to propose a repair. |
| Expected qualified result and capability | The counterexample remains a reusable scoped fact. The new proposal still requires target admission and fresh relation/property checks. |
| Consumer behavior | Compiler may expose the negative fact to an authorized producer without accepting the proposed repair by attribution. |
| Falsifier | Counterexample-guided generation reports its result as verified or widens the counterexample beyond its model. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| P | P | P | C | P |

### O39. Property coverage consumes an owner-defined obligation surface

| Field | Evaluation |
|---|---|
| Exact setup and authorities | Protocol structural owner supplies the exact required claim, round, observation, or obligation manifest. Analysis receives an exact set of qualified property judgments. Endpoint realization coverage is a different owner input. |
| Expected qualified result and capability | Analysis may answer whether the exact judgment set covers the exact manifest. It cannot invent the manifest or infer endpoint coverage. |
| Consumer behavior | Compiler or release policy consumes the property-coverage result and endpoint coverage separately. |
| Falsifier | Analysis defines required structure, generic derivation count implies coverage, or property coverage implies endpoint support. |

| A | B | C | D | E |
|---:|---:|---:|---:|---:|
| C | P | P | C | P |

## 5. Scenario synthesis

The scenario record does not select Candidate B. After candidate repair and
equal-resolution audit, it shows:

1. All five candidates can preserve truth and authority for most laundering
   probes by returning exact non-results; those are not differentiating wins.
2. Candidate A's repaired identity model now separates proposition meaning,
   proof basis, operational search, and semantic candidate identity. Its
   remaining structural failure is extension locality: the aggregate native
   context and central sum still perturb the regime for otherwise unrelated
   families. It also deliberately omits the v0 symbolic-certificate lane.
3. Candidate C now closes occurrence-local relation satisfaction and open
   search reporting, but remains conditional on a universal proof substrate
   faithfully carrying each owner-defined semantic family. Candidate D also
   closes open reporting, while its family coverage remains conditional on
   exact external environments and correspondence adapters.
4. Candidate E remains strongest on proof-carrying search, symbolic
   compression over an already admitted candidate image, and anytime reports.
   Its certificates still require independently defined family propositions
   and owner-qualified candidate facts, so it remains an optional lane rather
   than a replacement semantic center.
5. Candidate B is the only candidate that closes every charter and opportunity
   scenario as written. This is a validation result, not a selection: counts
   do not measure semantic simplicity, trusted-computing-base size, or the cost
   of closing each conditional obligation.

The repaired portfolio has passed independent equal-resolution audit.
Candidate B remains only the research-leading hypothesis until the
cross-cutting matrices, producer/consumer review, and independent convergence
review close.
