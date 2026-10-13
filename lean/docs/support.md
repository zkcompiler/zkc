# Supported claims

All results below concern stated mathematical models and exact selected imports.
They do not certify arbitrary DSL programs or the full native lowering pipeline.

| Surface | Maintained claim | Explicit boundary |
|---|---|---|
| Core execution | Typed mathematical/role-local programs; exact process refinement; shared-state sequential composition; machine prefix/resumption and finite-process completion | General native loops and external waiting are not imported by the scalar profile |
| Scalar import | Checked admission and source-specific open-process correspondence for actual exports | Native exporter, interface resolver and constructor rendering are reviewed/tested, not universally proved |
| Constructed import | Typed admission and proved flat/raw/typed execution correspondence for actual source-checked constructed participants; all primitive results, guards and returned state | Bounded straight-line profile; native exporter and prior Local expansion, primitive meanings and Host initialization are explicit; native loops and general branches refuse |
| Semantic foundations | Lawful-monadic interpretation, exact operation-sensitive cost transport, disjoint provider composition, memoization and runtime-selected bounded control | Selected costs and observations; no inferred randomness, native loop correspondence or secret-independent timing |
| Oracle adapters | Adaptive typed-key encoding preserves outputs and projected residual caches; two-round full-prefix simulation proves cached-game correspondence with salted restoration | Fixed injective encodings; the generic encoding law alone does not translate arbitrary raw-byte adversaries or prove concrete sampling |
| Schnorr | Imported verifier completeness, two-transcript special soundness and custom invalid-equation rejection | Algebraic group/module interpretation; no discrete-log hardness reduction or whole native prover proof |
| VCVio Schnorr simulation | Equality for every event on commitment, fixed honest challenge, response and actual verifier outcome under uniform nonce/response sampling | One-session honest-verifier simulation; no malicious-verifier or concurrent theorem |
| VCVio Schnorr Fiat–Shamir | Fixed-statement extraction for a realized constructed verifier: if acceptance is `a`, extractor success is at least `a * (a / (Q+1) - 1/|F|)` | Truncated subtraction; ordinary total adaptive prover with private coins; one initially empty shared uniform-field oracle; `Q` bounds prover oracle calls; no efficiency or discrete-log hardness conclusion |
| ArkLib Sumcheck | Actual imported two-round degree-two verifier acceptance on a false public sum claim is at most `4 / |F|` | Finite field; reached fresh uniform queries; causal coefficient-message strategies, including arbitrary private probabilistic mixtures chosen before verifier draws |
| ArkLib Sumcheck Fiat–Shamir | All-prefix local knowledge conditions for quadratic Sumcheck; two-round full-prefix false acceptance at most `(Q+3) * 2/|F|` | Classical typed random oracle; adaptive statement and arbitrary full-prefix queries; `Q` bounds adversary calls; reduction/completion accesses charged; early-stop correspondence observes acceptance |
| Finite full-prefix Fiat–Shamir | Heterogeneous finite-round extraction bound `(Q+n) * error`; quadratic Sumcheck source false acceptance at most `(Q+n) * 2/|F|` | Fixed schedule; all-prefix knowledge laws; one classical typed RO; completed-path source replay identifies acceptance, not early-stop caches or arbitrary native loops |
| Public factor openings | Imported composed verifier bound `4 / |F|`; generic conditional bound `4 / |F| + epsilon` | Public polynomial factor checks prove zero opening error; PCS binding/extractability needs a separate opening theorem |
| Authored DSL target | Imported Schnorr relation denotes discrete-log; two accepting imported verifier transcripts yield a witness accepted by that relation | Bounded scalar formula adapter and tested interface selector binding |
| Clean | Admitted lookup/channel-free flat AIR export preserves constraints and selected source specification; native control fixture retained | Finite rows/field/ring interpretation; native agreement is differential, not decoder correctness |

Source forms include original, helper-based, reordered and Horner implementations.
The factor-opening case combines Sumcheck residuals with two subsequent adaptive
openings. Negative controls include early challenges, wrong residuals/points,
stale bindings, correlated-coin requests, invalid dormant definitions, false
relation bodies, wrong subjects and forbidden axioms.

The optional security package invokes ArkLib's
`Sumcheck.Interaction.Native.execute_soundness`. Its adapter constructs degree-
bounded messages and the public polynomial oracle, proves all evaluation/domain
laws and equality of accepted-event computations. No source-specific connection
law is assumed. VCVio's uniform-event transport proves Schnorr's simulator law.
The distinct FS consumers use VCVio's `knowledgeExtractor_success` and ArkLib's
`StateRestoration.restored_extraction_bound`. The Sumcheck adapter proves the
all-prefix residual predicates and existential bad-challenge bound before
applying the latter theorem. A concrete salted-key reduction retains prior
challenges and accounts for an extra access. Neither an interactive bound nor
matching honest prover/verifier challenges supplies these security arguments.
The separate [finite transcript consumer](spec/finite-transcript.md) instead
applies VCVio's adaptive bad-query theorem directly to full prefixes, charging
exactly `Q+n` accesses under the same kind of local knowledge premises.
Some unrelated upstream declarations contain `sorry`; the transitive axioms of
owned claimed results are audited separately and must use only Lean's standard
three axioms. A build of all upstream sources is not asserted.

For precise APIs read the theorem statements in `Zkc`, `ZkcExamples`, and
`integrations/arklib/ZkcSecurity`; [architecture](architecture.md) explains their
roles. [Bridge commands](../bridges/common/README.md) reproduce finite checks.
Native Z/97 comparisons do not establish BLS12-381 arithmetic, production
randomness, transcript encoding or native executable soundness.
In particular, the retained native suite is Merlin while the selected FS
interpretation is an ideal typed oracle. Security receipts concern that stated
interpretation and formal initialization. Concrete suite/Host conformance,
proof-byte decoding and lower-stage preservation remain separate boundaries.
