# Formal baseline to compiler implementation

The maintained formal library supplies meanings, laws and concrete clients.
It does not determine the best mutable compiler representation. Before expanding
the native implementation, review the MLIR abstractions against this map and
its actual source examples. [Support](../SUPPORT.md) owns theorem scope;
[the roadmap](../../docs/roadmap.md) owns implementation order.
The [normative specification](../../docs/spec/README.md) and
integration review now reconcile
these contracts with their actual Formal premises. Concrete representation
choices remain open to the next compiler design; the current MLIR is not a
compatibility constraint.
The [assurance policy](../../docs/assurance.md#6-implementation-correspondence-policy)
uses differential testing as the default native connection, with optional
implementation proofs. Existing mathematical obligations remain unchanged.

## 1. Preserve useful distinctions

There is one common execution vocabulary and several source/interpretation
abstractions. They are not all consecutive compiler stages:

```text
structured protocol + logical objects + bound inputs
    ├─ interaction construction: Fresh / specified framed interpretation
    ├─ supplied role programs and available local inputs
    └─ logical algorithm choice: recomputation / materialization / checked rewrite
                ↓ chosen, justified composition
        contracted executable plan and explicit effects
                ↓ value/state/codec relation
        native storage, kernels, provider and execution controller
```

`Proc` is the common denotation used to compare these paths. It is not an IR to
which everything must be flattened before optimization. A protocol can retain
rounds, messages, a fixed polynomial and verifier relations while a child
arithmetic region is lowered. Construction selection can change the required
provider and security premises without changing that child arithmetic proof.

An MLIR level is useful when it retains information needed for a distinct
analysis, transformation or verification. Do not introduce a dialect for every
Lean namespace. Conversely, do not erase logical objects, interaction order or
role information before the passes that need them have run.

## 2. Contracts for each abstraction

| Abstraction and formal basis | Retained information and useful transformations | Lowering/runtime obligation and discriminating checks |
|---|---|---|
| Typed protocol source: `Source.Program`, `Context`, `Elaboration`, `InputBinding` | Sorts/domains, ordered context, explicit captures, regions, public branches/repetition, stops. Renaming, substitution and public specialization have meaning | Actual exported operands and region results denote the retained source. Reject mixed domains, future/foreign inputs, wrong capture order and hidden host callbacks |
| Interaction and construction: `AlgebraicRounds.Source`, `Construction`, `Fresh`, `Framed`; `Sumcheck.Framed` | Messages/checks/challenge sites, initial statement root, typed frame order and selected interpretation. Keep construction choice explicit; apply only lawful interpretation/reorder steps | Preserve attempted queries, post-state and events on failure. Concrete codecs must bind the same domain/count/claim/polynomial. Test missing absorption, changed root, reused draw and failure after a state change |
| Role-local execution: `Source.LocalInputs`, `LocalExecution`; `Sumcheck.Endpoints.Composition` | Role ownership, currently available inputs, explicit local state/captures and values delivered between programs | Execute actual bound endpoints and consume their returned values; do not insert defaults. The current proof is synchronous supplied composition. Queues, generated projection or hostile host callbacks need additional laws |
| Logical mathematical objects: `Polynomial.Quadratic`, `Coordinates`, `Encoding`, `Modules.PolynomialPreparation` | Fixed polynomial, ordered axes, prefix restriction, degree per coordinate and terminal point. Choose recomputation/materialization without changing that object | Relate native table/buffer handles to the same polynomial and axes. Keep failed allocation/overwrite and cache invalidation visible. Nonzero square terms distinguish degree-per-coordinate from multilinearity |
| Stateful analysis/optimization: `FactorState`, `FactorContract`, `Compiler.Analysis.FactorReuse`, `FactorOptimization` | Meaning of facts, operation read/write frames, readiness, immutable binding identity and demanded exports. Reuse prepared data under source-produced facts | Validate the actual changed candidate and premise producers. Preserve refusal and failed-write state. Native CFG analysis may use a compact post-fixpoint certificate; the finite reference's branch duplication is not a required implementation algorithm |
| Local arithmetic and block realization: `Compiler.Arithmetic.Horner`, `Compiler.Blocks`, `Compiler.Readback` | Domain laws, ordered input/output positions, source occurrences, lazy choices, contracted calls and selected observer | Check source and target independently. Horner needs algebraic laws; structural readback establishes representation, not arbitrary algebra. Whole-call embedding needs frames and live-outs. Wrong source anchors and reordered effects must fail |
| Logical execution plan: `Compiler.Plan`, `Realization.Simulation`, `InstructionSequence` | Complete outcome, final state, ordered events and operation requirements; distinct value/state representations are permitted | Relate actual plan dispatch to its denotation. Primitive incomplete halt differs from falling off an instruction list; compilation cannot turn a stop into a successful continuation |
| Physical runtime/backend: `Modules.Allocation`, `BoundedCache`, `Semantics.OperationContract`, scalar endpoint/supplier clients | Native layout, aliasing, ownership/generation, capacities, backend identity, provider consumption and progress assumptions | Prove or explicitly trust the concrete implementation of each common contract. Check stale handles, cross-session use, failed writes, capacity refusal, changed event order and provider substitution. No existing theorem verifies Rust or Arkworks internals |
| Property and artifact consumer: `Properties`, `Semantics.Disclosure`, `AuthorizedContinuation`, source-bound checker and security clients | Requested relation/observer, allowed assumptions, original source, actual candidate, provider law, statement/terminal relation and joint released information | A checked local rewrite is not a new security theorem until the experiment and adversary/observer maps compose. Artifact code, diagnostics, evidence and history are a joint observation; separate marginal checks do not prove privacy |

## Adopted contracts and compiler obligations

Semantic adoption adds the following obligations to this map. These contracts do
not choose the final dialect boundaries.

| Adopted contract | Compiler consequence | Reference and required control |
|---|---|---|
| Component connection and contextual replacement | Keep actual component inputs and boundary values available until every connected constraint is formed. Use relations between layouts; a shared physical tuple is unnecessary. Check removal must have a non-circular premise producer | `RelationComposition`, `Examples.ComponentConnections`; mismatched key, missing representation coverage and circular check removal |
| Acceptance with exposed outputs | A verifier-relation target binds the actual input, output and all satisfying assignments. Returning a deferred obligation does not discharge it; a consumer sees that same output | `Realization.Acceptance`, `Sumcheck.Connection`, `Examples.Acceptance`; free output wire, changed original polynomial and swapped point |
| Input coverage and retained consumers | Export an actual input/binding map for the advertised profile. A forward map alone does not exclude extra accepted target inputs. Before routes split, retain the information needed by every remaining consumer | `Compiler.InputBinding`, observation/locality laws; empty input relation, invalid target input and erased configuration |
| Exact observations versus sound summaries | An analysis may conservatively forget a fact and decline a rewrite. It cannot remove a required protocol obligation. Cache analysis results against their actual source/binding/interpretation dependencies | `Analysis.Observation`; unknown summary remains sound but fails exact recovery |
| Construction sequencing | Preserve residual provider and transcript state across regions/calls. Separate lowering is lawful through binding; resetting state or exchanging constructions needs its own checked condition | `Proc.run_interpret_bind`, `interpret_interchange`, `Execution.follow_rebase`; framed reset changes `(4,6)` to `(4,3)` |
| Immutable preparation in context | Represent pure key/value dependencies separately from stateful effects. Retain the selected provider and cost model in their actual scope. A hit may skip pure work, not an external call. Scheduling and allocation need their own contracts | `Semantics.Preparation`, prepared Sumcheck, word and correlated-service clients; stopped query keeps post-state, repeated request parameter still consumes two coins |

These responsibilities are compatible with mixed-level IR and selective
lowering. C++/MLIR can keep connected symbols, regions, captures, typed results
and effectful calls while lowering a pure arithmetic child. The subsequent
compiler design must choose their concrete carriers and analysis interfaces;
Lean's product cache/state and higher-order continuations are reference
semantics, not mandated runtime layouts. Rust/backend adapters implement their
selected call, storage and provider contracts. Differential tests should compare
the actual bound source, complete outcome, ordered events and exposed residuals;
performance measurements separately compare work, memory and compile/check cost.

Before implementing a verifier-relation target for a transcript-derived
verifier, supply its own `Acceptance` instance. Bind each challenge to the actual
frames, codec and selected query derivation; `Sumcheck.Framed.reference` supplies
the existing execution correspondence. The fresh-tape instance does not satisfy
this obligation. An arithmetic target must also represent proof messages and
constrain all auxiliary assignments. FS security remains a separate theorem.

The first concrete lowering must supply an `InputBinding` client across its
actual different source/target contexts, and demonstrate that any shared erasure
serves every remaining consumer before the native/relation target split. Choose
cache placement, store/bypass policy, charged costs and heterogeneous value
representation with their first native consumers. These decisions have semantic
contracts already; their concrete encodings are not selected by this handoff.

## 3. Three end-to-end paths already available in Lean

**Ordinary interactive Sumcheck.** A fixed degree-at-most-two-per-coordinate
polynomial and claim enter the typed source. `Polynomial.Multilinear`,
`TableExpression` and `Sumcheck.TableSource` now connect actual ordered table
cells, extension/product meaning and repeated factors to that polynomial and
its original-statement premise. Actual prover callbacks choose each
message before its challenge. The verifier retains the original polynomial and
evaluates it at the complete delivered point. `Security.source_soundness` bounds
false acceptance by `2*n/card F` under independent uniform tapes.
`Optimization.soundness` transports this through the actual checked Horner child
plan. `Endpoints.Composition` connects supplied local programs; `Framed` separately
connects statement-bound transcript execution. None of these equalities supplies
a random-oracle or FS security reduction.

**Stateful factor reuse.** Source module calls produce facts about actual residual
coefficients. Outcome-sensitive frames preserve or invalidate them. The checker
replaces a query with reuse only when those facts justify it and preserves the
original readiness guard and terminal operand. The polynomial client supplies
the contracts; a correlated service exercises the same immutable-cache and
transformation framework while retaining one coin per response. This checks a
shared infrastructure claim without equating the two protocols.

**Source-selected backend readback.** An independent source anchor fixes the
profile, operands, exports and actual body. Structural readback and JSON-array
representation identify a supported logical plan. Concrete scalar/FRI/alias
consumers use the admitted module, and bytecode clients embed it in real prefixes
and continuations. This closes the represented-data join, not an arbitrary raw
JSON parser, native loader or backend implementation proof.

The library also carries contrasting typed Sigma and Merkle sources, independent
nested-allocation executions and source-region sequencing. Use these alongside
the three paths above when reviewing MLIR. The Merkle logical operation's interpreted expansion
has a proved meaning; a compiler that wants to analyze its internal path steps
must also retain an actual inspectable lower representation. Interpretation
composition alone does not synthesize that representation.

The [virtual-product example](../Examples/OpeningReduction/README.md) adds a
source that returns a scalar and point, followed by three explicit opening
obligations. Its exact controls prohibit flattening the product into its Boolean
value table: that preserves the initial sum while changing the queried
polynomial. Retain factor provenance, per-phase degree, ordered axes and pending
claims before arithmetic/storage lowering. A claim bundle is not an accepted
proof.

## 4. Engineering ownership

Keep mutable SSA/region data, analyses, invariant search, costs, rewrite selection
and MLIR conversion together in C++/MLIR. Lean owns the semantic definitions,
functional checking rules and proved conclusions. Rust owns artifact/job tooling,
runtime custody, storage and ecosystem backend integration. Exchange complete
source/candidate/evidence artifacts and admitted execution plans; do not split
individual compiler analyses across a C++–Rust service loop.

A shared schema can reduce accidental representation drift. The checked object
must still be the object actually exported and executed. Consumer-retained source
and policy prevent a producer from validating a correct transformation of the
wrong program. Distinguish conditional checked conclusions from admission that
has discharged or explicitly accepted their remaining requirements.

Protocol-level, algebraic and physical passes can coexist in one MLIR module.
Dialect conversion legality must reflect which semantic information has been
resolved. A legal-looking generic side-effect annotation does not prove that
transcript queries commute or correlated randomness can be reused. Supply the
specific semantic law used by the pass. The existing native finite-source route
is an integration experiment; its thin operation set is not the final PIR design.

## 5. Theory and tooling at the next decisions

| Decision | Established theory/tool to use | Required result before accepting the decision |
|---|---|---|
| Region/binding and dialect boundaries | Intrinsic typing, substitution, algebraic effects; MLIR regions/interfaces; the recorded Lean-MLIR carrier trial | Represent a full protocol with logical objects and a selectively lowered child, then show exported-source adequacy and a rejected unavailable capture |
| Fact propagation and preparation placement | Abstract interpretation, outcome-sensitive Hoare/frame reasoning, dependency-sensitive memoization | Actual invariant producer/checker, failed-write invalidation and a profitable versus unprofitable case; correctness does not imply profitability |
| Lowering and native storage | Relational/data refinement, ownership/separation reasoning; differential testing | Executable Lean reference and explicit native relation; actual storage/alias/failure cases, generated coverage, replay and retained trust. Extraction is an optional proof route |
| Construction/security adapter | Conditional probability, game reductions, strategy/query correspondence; optional ArkLib/VCVio | Matching statement, adversary, oracle, codec and failure experiment plus supplied hypotheses; no use of an upstream theorem with a proof hole |
| Compile-time search | Translation validation, proof reconstruction, optional e-graph/SMT proposals | Source-bound checked candidate; measure search, checking, certificate size and execution separately |

Primary references and prior comparisons are in
[the source ledger](sources.md) and [the research agenda](research-agenda.md).
These are decision-specific obligations; they do not require another general
survey before every implementation step.

Encoding adequacy connects constraints to machine behavior; protocol security
connects acceptance to the encoded relation. The existing direct-terminal
Sumcheck and single-path Merkle clients do not validate those joins.

General Fiat–Shamir, zero-knowledge and extraction security, asynchronous
projection and every-backend verification are research extensions with separate
acceptance criteria. A newly discovered counterexample reopens its affected law;
it does not automatically reopen every completed abstraction.
