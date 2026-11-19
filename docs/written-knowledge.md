# Written knowledge for three-message group protocols

`zkc-knowledge` takes a scheme entry and generates a Lean module for its written knowledge clause. Two source programs exercise the same compiler and formal library.

| Scheme | Public statement | Shared first message | Written relation on the extracted scalar |
| --- | --- | --- | --- |
| `Proof` in [schnorr_example.zkc](../examples/schnorr_example.zkc) | base and point | one point | `point == base * scalar` |
| `SameLogProof` in [chaum_pedersen.zkc](../examples/chaum_pedersen.zkc) | `g, h, u, v` | two points sent as one tuple | `u == g * x and v == h * x` |

The Schnorr clause selects `DLog` and `response_difference`. The Chaum–Pedersen clause selects `SameLog` and `extract`. Each name resolves to an executable source declaration. The clauses, the relation operands, the extractors and the verifier guards all affect the generated result.

## Generate and check

From the repository root, run

```sh
(cd lean/compiler && lake -q exe zkc-knowledge ../../examples/schnorr_example.zkc ../.. Proof) > /tmp/WrittenSchnorr.lean
(cd lean/formal && lake -q lean /tmp/WrittenSchnorr.lean)
(cd lean/compiler && lake -q exe zkc-knowledge ../../examples/chaum_pedersen.zkc ../.. SameLogProof) > /tmp/WrittenSameLog.lean
(cd lean/formal && lake -q lean /tmp/WrittenSameLog.lean)
```

Use `--namespace NAME` to import several generated modules together. The default namespace is `WrittenKnowledge`. Pass `--target-only` before the namespace option and input path to emit a companion target. `WrittenKnowledge.compiledObligation` refers to three admission results. For every public statement, shared commitment and pair of distinct challenges, if the projected verifier returns on both transcripts, the compiled extractor returns a scalar and the compiled relation accepts that scalar. `certified_core_admitted` proves this for both examples under the stated model and algebra laws.

The compiler selects the scheme from the entry module, checks the closed specialization and validates an explicit prover or deciding role. This profile accepts two online roles and a public statement consisting of the shared group inputs. A scheme such as `Signature`, which adds public `message` and `domain` context, receives a located refusal. Later construction and layout directives describe a separate stage.

## From the clause to the theorem

1. **Resolve and compile.** The clause selects the relation and extractor by declaration identity, and binds the statement operands in their written order. The selected verifier's message, draw and response supply the types and selectors of a nominal `Run` record for the closed protocol. An unnamed event uses its numbered field. The ordinary expression elaborator receives `Runs<2>` as the fixed-length sequence `[Run; 2]`. It then uses the ordinary typed tree, Core function emitter and admission for each selected function. Sequence indexing, named record access, guard failure and restricted inversion therefore have their deployed Core meanings. This export supports closed functions in the serializable fragment. Source parsing, resolution and lowering remain compiler responsibilities.
2. **Check what will execute.** The module contains the stored protocol, relation and extractor and three typed bodies. Lean links each body to its own admission result by erasure and readback. Independent checks establish that each result exists. The formal target evaluates the selected functions with `fnMeaning` in the same model as the projected verifier. Keeping three singleton packages lets admission check each root without changing Core definition order. The generated application supplies the shared commitment to both leaves.
3. **Recover the verifier equations.** `model_equations` characterizes an entire returning execution in both directions for every model and call path. The trace fixes the actual operations, their positions and all three replies. Every visible pure row obtains its result from model totality. Tuple operations rearrange those values. The guard list includes tests owned by the verifier, including shared guards. The proof skips prover-private guards without reading their operands. A second theorem, `verifier_equation`, interprets the rows for which the caller supplies equations. An extra pure field comparison can remain in its original model meaning while the group proof uses the other equations.
4. **Check the local calculations.** For the supported algebraic fragment the exporter also prints short value-level calculations. `relation_agrees` and `extractor_agrees` prove equality with the executions of the compiled functions on **all** inputs, including equal challenges and stopped executions. The proof walks actual Core instructions and applies group and scalar row laws. The nonzero carrier can differ from the scalar carrier. Refinement requires a proof of nonzero input, and the laws relate forgetting and inversion to the scalar operations.
5. **Extract one witness.** The two accepting transcripts have the same commitment. The group-action lemma applied to the two challenges gives the response difference divided by the challenge difference. Chaum–Pedersen supplies two equations with that same scalar. `Std.WP.vcgen` checks the guarded calculation and resulting whole relation. The two correspondence theorems then transfer the result to the compiled functions. The kernel checks each step. [Lean verification-condition generation](https://lean-lang.org/doc/tutorials/latest/vcgen/)

A companion can prove `coreObligation` directly and apply `of_core_obligation` to the three successful admissions. This path requires a model and no automatic algebraic strategy. For example, an extractor that adds two response scalars has a Core target even when the built-in group calculation declines it. For compatibility, modules with value-level calculations also expose `obligation` and `certified_admitted` when the optional proof succeeds. The latter refers to those calculations and the admitted verifier.

## Reuse and limits

| Layer | Reused result | Current specialization |
| --- | --- | --- |
| Core processes | A single fold composes every instruction with its continuation. Exact traces, possible returns, all permitted paths, charged exceptional replies, and stateful joint observations have distinct interpretations of that fold. An invariant for a monotone state judgment lifts from one body to any number of iterations. Zero charge entails the all-path property when the supplied zero-cost policy excludes no permitted reply. | Connecting a concrete policy to probability mass requires its probability semantics. |
| Verifier proof | Model totality gives every pure row its typed output list. A supplied equation interprets a row independently of the walk. | The exporter and replay strategy handle straight-line, two-role G1/scalar forks with one private witness and a point or tuple of points as the first message. The walker still constructs evidence per instruction. Calls, restricted verifier computations and general loops need rules or a companion. |
| Local functions and group algebra | Ordinary admitted local functions, typed row equations, one exact-trace theorem and one group-action extraction lemma serve both examples. | The current automatic calculation covers the operations in the two examples. A different extractor, algebra or run shape can require new evidence. The concrete model exercises the two-element field and group. |
| Repeated events | Each declaration's source event and part identify its realizations. A per-definition index recovers full enclosing block keys and iteration numbers from the typed body. A missing or ambiguous address fails lookup. | Uniform loops have one static site. A stepped reduction has one physical realization per iteration. Source proof clients check this against the admitted Sumcheck and GKR reductions. |

The interactive theorem concerns a returning verifier fork. Honest-run completeness, simulation, Fiat–Shamir security, concrete curve instantiation and probability bounds require their own statements and evidence.

## World observations and the next proof boundary

The frontend preserves the oracle sender and recipients, requesting role, deferred mode, opening claims and their source operands during name resolution. The joint observer records the full typed request and reply, and allows the service to update private state. Forgetting request arguments recovers exactly the existing joint run for a fixed occurrence-indexed source. The effect view sends the request arguments to the owner and the reply to each designated listener. A declared read grant records the owner, listeners, kind, occurrence and type. Every read in a reachable network of scoped processes respects those grants, including reads by a replacement strategy. [World observations and authority](../lean/formal/Zkc/Formal/WorldObservation.lean)

The next oracle milestone is one source-issued spot check interpreted against a table fixed at send. The lowering must type opening obligations and preserve their issuers. The whole-program projection theorem must relate a joint service execution to the authorized role executions, including hidden private data. Source resolution, the effect-level listener theorem and network read authority establish distinct parts of that argument. The current source still reaches the frontend's layer-D waiting point.

For repeated rounds, the index permits reuse of existing physical addresses and clause dispatch. The two reduction clients enumerate typed instances of their common round body. Each instance retains its actual block, incoming state, result types, operation references and proof of verifier correspondence. The source check ties both exchange addresses to those same instances. Inferring this body and its parameters from a previously unseen family remains an exporter task. The GKR example has an ordinary outer loop and an inner stepped Gate reduction. Physical key sharing requires attachment lookup by full place and interpretation clauses selected by realization. The address index provides an independent check during that migration.

The [proof architecture](proof-architecture.md) records the ownership of generated views, the optional calculations, the oracle service and the probability bridge.

## Regression evidence

`just test-written-knowledge` checks the two source-issued certificates, reordered Chaum–Pedersen guards and an extra scalar guard, with an axiom allowlist of `propext`, `Classical.choice` and `Quot.sound`. It checks native-only export, equal challenges, changed statement bindings and concrete counterexamples for changed source functions. A separate mutation keeps all three emitted bodies fixed and corrupts only the short extractor calculation. The correspondence proof must fail. An independent client consumes each final result against the role and function meanings of three successful admissions. Replacing the public theorem with `True` must fail at this client. The suite replays the logical declarations in both baseline modules and their project dependencies through the kernel.

After removing the second Chaum–Pedersen guard, both permitted branches return for public inputs `(1,1,1,0)`, commitment `(0,0)`, and challenge/response pairs `(0,0)` and `(1,1)`. No scalar satisfies the compiled two-equation relation. The suite proves the negation of `compiledObligation` for those three actual admissions. `just test-interactive` also checks physical round addresses, oracle name resolution, payload-sensitive service state, private-source grants and the interactive library audit.
