# Domain and effectful-source correspondence

Evidence for [domain values](../domains/values.md),
[tables and polynomials](../domains/polynomials.md),
[Sumcheck profile](../profiles/README.md#sumcheck-components) and
[captured/service profiles](../profiles/README.md#service-components), with the table choices in the
[table-expression rationale](../../rationale/table-expression-meaning.md). `D` denotes an inspected definition,
`T` a theorem under its actual hypotheses, and `O` an adapter/policy obligation.
Root names and optional names are separated below.

The [finite-vector contract](../domains/vectors.md) uses
`Zkc.Algebra.linearCombination_rows`, `linearCombination_smul` and
`linearCombination_product` over a semiring acting on a module. These laws
connect to the selected diagonal implementation through scoped checks and
differential execution, not a native refinement theorem. Companion results in
`Zkc.Protocols.InnerProduct.{Folding,Weights}`,
`Zkc.Protocols.RangeProof.{Relations,Bits}` and
`Zkc.Protocols.Sumcheck.CubicRound` establish algebraic identities and conditional
integer bounds. They do not establish complete security of the emitted protocols.

`LocalProver.Inputs.eval_no_default`
and `reaches_inputs` require `Ring` rather than `CommRing`. Admission's
actual input check and returned-cut preservation remain separate from an outer
handler stop, which returns no local cut. The profile index classifies
`MessageSchema` as a maintained reference client, without adopting its
natural-word header as a Sumcheck byte format.

The affine setup and
partial-response machine, exact `Program.Good`, whole-tree issuance, installed
role environment and finite commitment scheduler also use
`CorrelatedSetup.Source.same_controller`, `Service.whole_coupling`,
`Communication.cached_execution_exact`, and the stateful `Preparation.Rel`,
`run_refines`, `rule` and `experiment_mass`. The fixed-horizon fold is connected
to the operational source's history; only the latter describes retained tape
and exhaustion.

## Relation domain foundation

The [constraint specification](../domains/constraints.md) adds domain views,
without changing PIR execution or requiring every protocol to use constraints.

| Meaning | Maintained Formal connection | Scope |
|---|---|---|
| Sparse linear forms and matrix views | `Zkc.Relation.Sparse.eval_eq_sum`, `Matrix.mul_denote`, `eval_contract`, `contract_linearCombination`, `bilinear_denote` | Commutative-ring values and exact finite dimensions; duplicate terms add |
| Zero row/column padding | `RankOne.System.satisfies_pad`, `satisfies_zeroExtend`, `bound_zeroExtend` in `Zkc.Relation.Padding` | Every target assignment restricts to the original relation; extra columns remain unused, ONE/public positions unchanged |
| Coefficient normalization | `Sparse.eval_perm`, `eval_merge`, `eval_zero_entry`, `eval_eraseZeros`; `RankOne.System.satisfies_congr` | Denotation-preserving changes; no proof of the C++ normalizer |
| Exact row deduplication | `RankOne.System.satisfies_sameRows` | Mutual coverage of complete row triples, possibly different row counts; every assignment, unchanged columns/layout |
| Multilinear matrix evaluation | `Sparse.extension_coefficients`, `Matrix.atPoint_tensor`, `atPoint_boolean` in `SparsePolynomial.lean` | Established MSB/first-coordinate order; arbitrary ring points, including non-Boolean points |
| ONE and public slots | `RankOne.embed_extract`, `bound_iff`, `System.encoding`, `System.family_reorder` | A bijective complete layout; reconstruction of arbitrary bound assignments, not just honest generator outputs |
| Executable relation checking | `Reference.products_check`, `check_correct`, `Binding.layout_bound` | Typed admitted sparse systems and exact inputs; raw field/JSON decoding and native execution are separate |
| AIR locality and degree | `AIR.Expr.eval_local`, `polynomial_eval`, `polynomial_degree`, `used_read_in_range` | Derived finite reads and conservative trace-variable degree; selector/domain/quotient obligations remain external |

`Zkc.Relation.Encoding.valid_iff`, `comp` and `terminal_sound` connect actual
source/target families using both witness directions. The latter preserves the
selected target reduction's exceptional event; it supplies no probability bound.
The native LLZK adapter has not been supplied as a universally proved instance.

The ordinary `FiniteVectors`/`FiniteMatrices` references consume checked runtime
sequence carriers. The dependent sparse relation model instead exposes algebraic
proofs over bounded coordinates. Their native connection is independent execution
and differential evidence, not a theorem obtained by naming both matrices.

## Supplied endpoint join

These declarations support the
[supplied-local-endpoint join](../profiles/sumcheck/interactive.md#supplied-local-endpoints).
`Zkc.Protocols.Sumcheck.Endpoints.Prover.boundSend_exact` and
`Zkc.Protocols.Sumcheck.Endpoints.Prover.boundReact_exact` connect actual bound
local runs to the callbacks. `Zkc.Protocols.Sumcheck.Endpoints.Verifier.boundCheck_exact`,
`Zkc.Protocols.Sumcheck.Endpoints.Verifier.boundAdvance_exact` and
`Zkc.Protocols.Sumcheck.Endpoints.Verifier.boundTerminal_exact` connect the
corresponding pure local programs.
`Zkc.Protocols.Sumcheck.Endpoints.Composition.fresh_exact` and
`Zkc.Protocols.Sumcheck.Endpoints.Composition.framed_exact` establish complete
driver equality. `Zkc.Protocols.Sumcheck.Endpoints.Composition.acceptance_exact`
uses the fresh experiment's same uniform tape. Locality fixes the meaning and permitted role view. No automatic
projection, asynchronous transport or native callback theorem is inferred.

## Notation

In the Sumcheck chapter,
`evalExpression` denotes `Zkc.Polynomial.TableExpression.eval`, and
`expressionSum` denotes `Zkc.Polynomial.TableExpression.sum`. The honest-run
sentence states the initial claim `p.booleanSum` required by
`Zkc.Protocols.Sumcheck.Security.source_completeness` beside its conclusion.

## Message-shape reference clients

The profile index's informative clients correspond to:

- [MessageSchema](../../../formal/Zkc/Source/MessageSchema.lean): natural-word
  headers and payload admission at formed public dimensions.
- [Scalar-byte consumer](../../../formal/Zkc/Protocols/ScalarBytecode/Prover.lean):
  three encoded scalar words followed by construction of trusted header data;
  the natural-word header is not present in that byte stream.
- [Parameter-family messages](../../../formal/Zkc/Protocols/AlgebraicRounds/MessageShape.lean):
  field/instance tags and public degree-indexed payload vectors.

These clients do not select one common wire protocol. Their source locations
and implementation scope belong here; the profile index explains the distinct
uses without making them normative message formats.

## Root domain map

| Clause | Formal correspondence | Hypotheses and limits |
|---|---|---|
| [DOM-01](../domains/values.md#sorts-and-interpretations), [domain adequacy](../domains/values.md#domain-adequacy) | D: `Zkc.Source.Interpretation`, `Zkc.Source.Program.denote`; T: concrete source laws below | O: identifying the actual domain/inputs, operation adequacy and full adapter relation; a common type alone proves none of these |
| [DOM-02](../profiles/source/public-dimensions.md#public-dimensions), [dimension formation](../profiles/source/public-dimensions.md#dimension-formation), [dimension substitution](../profiles/source/public-dimensions.md#dimension-substitution), [shapes and actual values](../domains/values.md#shapes-and-actual-values), [sorts and interpretations](../domains/values.md#sorts-and-interpretations) | D: `Zkc.Source.PublicDimensions.Dim`, `Zkc.Source.PublicDimensions.Dim.eval`, `Zkc.Source.PublicDimensions.RawDim.scope`, `Zkc.Source.PublicDimensions.publicEnv`; T: `Zkc.Source.PublicDimensions.eval_subst`, `Zkc.Source.PublicDimensions.publicEnv_exact` | Natural public environment indexed by scope; successful list binding retains exact supplied entries; raw future/hidden cases refuse; O: raw public-parameter provenance and actual cross-sort conversion |
| [DOM-03](../domains/polynomials.md#flat-table-indexing), [points and boolean tables](../domains/polynomials.md#points-and-boolean-tables) | D: `Zkc.Polynomial.Multilinear.Table`, `Zkc.Polynomial.Multilinear.index`, `Zkc.Polynomial.Multilinear.vertex`, `Zkc.Polynomial.Multilinear.ofVector`; T: `Zkc.Polynomial.Multilinear.index_vertex`, `Zkc.Polynomial.Multilinear.vertex_index`, `Zkc.Polynomial.Multilinear.ofVector_vertex` | Every public `n`, actual typed vector and position; bijection requires no field assumptions; O: actual raw shape/identifier admission and other indexing adapters |
| [DOM-04](../domains/polynomials.md#multilinear-extension) | D: `Zkc.Polynomial.Multilinear.extension`, `Zkc.Polynomial.Multilinear.booleanPoint`; T: `Zkc.Polynomial.Multilinear.extension_boolean`, `Zkc.Polynomial.TableExpression.input_cell` | Every commutative ring, table and Boolean vertex; actual vector cells supplied to `inputTables`; no field/sample security follows |
| [DOM-05](../domains/polynomials.md#table-expressions), [boolean summation](../domains/polynomials.md#boolean-summation), [equality away from boolean points](../domains/polynomials.md#equality-away-from-boolean-points) | D: `Zkc.Polynomial.TableExpression.Term`, `Zkc.Polynomial.TableExpression.Expression`, `Zkc.Polynomial.TableExpression.factors`, `Zkc.Polynomial.TableExpression.eval`, `Zkc.Polynomial.TableExpression.sum`; T: `Zkc.Polynomial.Multilinear.productCoefficients_eval` | Ordered lists, arbitrary factor count in the source meaning; every field point, including non-Boolean; execution relation separately required for rewrites |
| [DOM-06](../profiles/sumcheck/quadratic.md#quadratic-coefficient-objects), [table compilation](../profiles/sumcheck/quadratic.md#table-compilation), [ordered coefficient encoding](../profiles/sumcheck/quadratic.md#ordered-coefficient-encoding) | D: `Zkc.Polynomial.Quadratic`, `Zkc.Polynomial.Quadratic.eval`, `Zkc.Polynomial.Quadratic.booleanSum`, `Zkc.Polynomial.TableExpression.compileFactors`, `Zkc.Polynomial.TableExpression.compile`; T: `Zkc.Polynomial.Multilinear.coefficients_eval`, `Zkc.Polynomial.TableExpression.compile_eval`, `Zkc.Polynomial.TableExpression.compile_sum`, `Zkc.Polynomial.Quadratic.coefficients_injective` | Accepted compilation over a commutative ring gives equality at every point; none for unsupported terms; encoding theorem compares coefficient objects, not arbitrary field-function equality |
| [DOM-07](../domains/polynomials.md#ordered-residuals), [coordinate list admission](../domains/polynomials.md#coordinate-list-admission), [contractions](../domains/polynomials.md#contractions), [applied and pending challenges](../domains/polynomials.md#applied-and-pending-challenges) | T: `Zkc.Polynomial.Quadratic.eval_restrict`, `Zkc.Polynomial.Quadratic.materialize_eval`, `Zkc.Polynomial.Quadratic.recompute_eval`, `Zkc.Polynomial.Quadratic.materialize_recompute`, `Zkc.Polynomial.coordinates_ofFn`, `Zkc.Polynomial.point_coordinates` | Actual prefix of exactly the indexed length and remaining point; O: binding/fact/availability and actual pending-challenge export supplied by module consumer laws |
| [DOM-08](../profiles/sumcheck/interactive.md#checked-evaluation-and-table-bound-entry), [interactive execution and failure](../profiles/sumcheck/interactive.md#interactive-execution-and-failure), [adaptive strategy and terminal equivalence](../profiles/sumcheck/interactive.md#adaptive-strategy-and-terminal-equivalence), [supplied local endpoints](../profiles/sumcheck/interactive.md#supplied-local-endpoints) | D: `Zkc.Protocols.Sumcheck.TableSource.run`; T: `Zkc.Protocols.Sumcheck.TableSource.run_compiled`, `Zkc.Protocols.Sumcheck.TableSource.run_exact`, `Zkc.Protocols.Sumcheck.TableSource.refused`, `Zkc.Protocols.Sumcheck.TableSource.accepted_iff` | Same actual input vector, source terms, accepted coefficient result, callbacks and initial state; complete equality for any coin list, terminal equivalence for exactly `n` typed coins; no native parsing theorem |
| [DOM-09](../profiles/sumcheck/interactive.md#checked-evaluation-and-table-bound-entry), [honest execution and interactive soundness](../profiles/sumcheck/interactive.md#honest-execution-and-interactive-soundness) | D: `Zkc.Protocols.Sumcheck.TableSource.acceptance`; T: `Zkc.Protocols.Sumcheck.TableSource.acceptance_exact`, `Zkc.Protocols.Sumcheck.TableSource.soundness`, `Zkc.Protocols.Sumcheck.TableSource.perfect_completeness` | Finite field, decidable equality, actual compiler success, fixed private prover state independent of uniform tape; false claim against original expression sum; completeness uses compiled polynomial in honest state |
| [DOM-10](../profiles/README.md#contrasting-domain-clients) | T: `Tests.ProtocolGenerality.Sigma.denotes_verifier`, `Tests.ProtocolGenerality.Sigma.plan_execution`, `Tests.ProtocolGenerality.Sigma.honest_execution`, `Tests.ProtocolGenerality.Merkle.walk_exact`, `Tests.ProtocolGenerality.Merkle.denotes_verifier`, `Tests.ProtocolGenerality.Merkle.plan_execution` | Sigma semiring/module arithmetic and supplied handler; Merkle fixed public height and exact ordered hash interpretation for pure fold law, generic handler for source/plan equality; no cryptographic reduction |

## Root source-profile map

| Clause | Formal correspondence | Hypotheses and limits |
|---|---|---|
| [SRC-01](../profiles/sumcheck/local-prover.md#local-prover-state-and-code), [local source admission and cuts](../profiles/sumcheck/local-prover.md#local-source-admission-and-cuts) | D: `Zkc.Protocols.Sumcheck.LocalProver.Code`, `Zkc.Protocols.Sumcheck.LocalProver.State`, `Zkc.Protocols.Sumcheck.LocalProver.eval`, `Zkc.Protocols.Sumcheck.LocalProver.coin`, `Zkc.Protocols.Sumcheck.LocalProver.Source.source` | Ring and decidable equality for expressions; natural outcomes retained separately from casts; O: actual external inputs admitted before total lookup |
| [SRC-02](../profiles/sumcheck/local-prover.md#local-source-admission-and-cuts) | D: `Zkc.Protocols.Sumcheck.LocalProver.Cut`, `Zkc.Protocols.Sumcheck.LocalProver.Source.calls`; T: `Zkc.Protocols.Sumcheck.LocalProver.Source.source_conforms`, `Zkc.Protocols.Sumcheck.LocalProver.Source.source_bound`, `Zkc.Protocols.Sumcheck.LocalProver.Source.source_returns_inputs` | Every code/state and typed reply; returned cuts retain inputs; normalization is an additional probability law, listed separately |
| [SRC-03](../profiles/services/affine.md#literal-selection-and-issuance), [issued causal experiment](../profiles/services/issued-causal.md#issued-causal-experiment) | D: `Zkc.Protocols.CapturedPrograms.Tree`, `Zkc.Protocols.CapturedPrograms.Tree.deps`, `Zkc.Protocols.CapturedPrograms.Tree.valid`, `Zkc.Protocols.CapturedPrograms.issue`; T: `Zkc.Protocols.CapturedPrograms.issue_agreement`, `Zkc.Protocols.CapturedPrograms.issued_ok`, `Zkc.Protocols.CapturedPrograms.issued_reads_bound`, `Zkc.Protocols.CapturedPrograms.issued_input_bound` | Fixed tree, commutative ring, successful issuance for availability/code validity; same permitted environment for agreement including refusal |
| [SRC-04](../profiles/services/affine.md#installed-source-environment) | D: `Zkc.Protocols.CapturedPrograms.Inputs.installAdmit`; T: `Zkc.Protocols.CapturedPrograms.Inputs.installed_environment`, `Zkc.Protocols.CapturedPrograms.Inputs.install_admission_exact`, `Zkc.Protocols.CapturedPrograms.Installation.installed_service_controller` | Actual request/capacity/world and role-qualified environment; controller law requires successful issuance; O: namespace authorization and concrete installer state/lifetime relation |
| [SRC-05](../profiles/sumcheck/scalar-rounds.md#supplied-early-round-adapter), [messages and logical rounds](../profiles/sumcheck/scalar-rounds.md#messages-and-logical-rounds) | D: `Zkc.Protocols.AlgebraicRounds.EarlySource.source`, `Zkc.Protocols.AlgebraicRounds.EarlySource.handler`; T: `Zkc.Protocols.AlgebraicRounds.EarlySource.formed`, `Zkc.Protocols.AlgebraicRounds.EarlySource.bounded`, `Zkc.Protocols.AlgebraicRounds.EarlySource.execution_exact`, `Zkc.Protocols.AlgebraicRounds.EarlySource.send_hidden_independent` | Every public count and supplied mathematical endpoints; the early adapter's `draw` is total; the table Sumcheck handler separately allows exhausted tapes; scalar return lacks terminal relation |
| [SRC-06](../profiles/services/affine.md#requests-delivery-and-history), [controller source and complete execution](../profiles/services/affine.md#controller-source-and-complete-execution), [immutable coefficient preparation](../profiles/services/affine.md#immutable-coefficient-preparation) | T: `Zkc.Protocols.CorrelatedSetup.Execution.history_exact`, `Zkc.Protocols.CorrelatedSetup.Execution.history_retained`, `Zkc.Protocols.CorrelatedSetup.Execution.issued_source_exact` | Same controller/setup/publication, request/reply boundary and actual issued service code; complete finite tape for history equality, retained prefix on exhaustion; O: native callback timing |
| [SRC-07](../profiles/services/commitment-sessions.md#finite-commitment-session-machine), [adaptive scheduling and preparation source](../profiles/services/commitment-sessions.md#adaptive-scheduling-and-preparation-source) | D: `Zkc.Protocols.CommitmentSessions.Source.source`; T: `Zkc.Protocols.CommitmentSessions.Source.execution_exact`, `Zkc.Protocols.CommitmentSessions.Source.priced_improvement` | Finite scheduler horizon, actual preparation mode and interpreted provider; result/observed trace equality, separate event-derived price condition; no asynchronous-interleaving theorem |
| [SRC-08](../profiles/README.md#evidence-and-interpretation-scope) | D: root imports of preceding definitions and separate optional package imports | O: evidence routing, actual frontend/codec correspondence and import closure; root common definitions do not imply every optional experiment law |

## Optional probability correspondence

These declarations are in `formal/integrations/arklib`; they are additional
evidence, not required root imports or newly proved root results:

- `ZkcArkLib.LocalProver.Source.execution_exact` and
  `ZkcArkLib.LocalProver.Source.normalized`: uniform finite local coins,
  the actual local code/state, both abort and commit cuts retained.
- `ZkcArkLib.CapturedPrograms.issued_no_default` and
  `ZkcArkLib.CapturedPrograms.Installation.installed_no_default`: successful
  actual issuance/installation, every admitted input index present, arbitrary
  fallback and probabilistic continuation.
- `ZkcArkLib.CapturedPrograms.experiment_bound` and
  `ZkcArkLib.CapturedPrograms.Installation.initialized_experiment_bound`:
  the declared experiment, an injective finite sample embedding, reachable
  commit point-mass cap and explicit false-claim premise. Refusal is projected
  to non-acceptance within that experiment; this is not generic privacy.

## Controls

`Tests.TableSource` checks distinct table cells/axis order, repeated-factor
multiplicity versus Boolean-only product collapse, longer-term refusal,
zero dimensions, empty sums/products, the actual successful checked run,
retained extra coins, boundary rejection and exhausted-draw prefixes. It also
instantiates soundness with the actual source sum as its premise. These finite
controls complement the universal conversion and whole-execution theorems.

Existing polynomial/factor controls exercise nonzero squared terms, incorrect
prefix order, unavailable coordinates and overwritten views. Sigma/Merkle
controls exercise non-polynomial sorts, phase order and failure inside an
expanded logical operation.

## Profiles

The dimension grammar lives in [public dimensions](../profiles/source/public-dimensions.md).
The degree-two coefficient/table compiler, scalar rounds and local code have
separate [Sumcheck owners](../profiles/README.md#definition-inventory).
Domain sorts, table meaning, axis order and factor multiplicity are common to them.
