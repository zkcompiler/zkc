# zkc formal library

Lean definitions and proofs for the finite atomic PIR kernel, structured
sources, outer iteration, checked transformations and protocol applications.
[docs](../docs/README.md) owns the prose semantics. Its
[specification](../docs/spec/README.md) owns the selected model's normative
contracts. Reviewed correspondence maps cover
[execution](../docs/spec/correspondence/core.md),
[programs](../docs/spec/correspondence/programs.md),
[domains](../docs/spec/correspondence/domains.md),
[transformations](../docs/spec/correspondence/transformations.md),
[realization](../docs/spec/correspondence/realization.md) and
[properties/release](../docs/spec/correspondence/properties.md),
with exact declarations, premises and validation;
[DESIGN](DESIGN.md) owns library architecture.

Start with [capability support](SUPPORT.md) for actual statements, premises and
clients. [The verification map](design/verification-map.md) distinguishes
semantic laws, compiler refinement, checker soundness, realization and protocol
security. [The implementation requirements](design/implementation-handoff.md)
state what these results require of the MLIR/C++ and Rust implementations.

The independent [artifact identity consumer](Tools/Artifact/Identity.lean)
implements normalized construction identity, the default policy. Run
`formal/.lake/build/bin/artifact-reference identity SOURCE DESCRIPTOR [CONFIGURATION]`
from the repository root to inspect admitted source and normalized identity.
The [typed laws](Tools/Artifact/Identity/Laws.lean) reuse region renaming under an
explicit shared interpretation and environment correspondence; representation
laws preserve operation contracts and encoded occurrence structure. These are
not raw-normalizer adequacy, native correctness or Fiat–Shamir security proofs.
Ordinary `Zkc` library clients do not need to import the tool implementation.

## Use

The main Lake package depends on pinned Mathlib. External protocol proofs live
in the separate optional [ArkLib integration](integrations/arklib/README.md).
Main-library imports never require ArkLib, VCVio, integration objects or tests.
`import Zkc` exposes the small execution/interaction/contract foundation; use
narrow imports for other capabilities. There is no compatibility aggregate.

| Import | Use |
|---|---|
| `Zkc` | Complete finite executions, outer finite-step iteration, interaction, contracts and observations |
| `Zkc.Semantics.Iteration` | Coherent prefixes, stable completion, admission and interpretation transport, explicit deployment caps |
| `Zkc.Source.Requirements` | Proof-producing static requirement replay, including ordered pure application congruence; no constructor injectivity or native elaborator theorem |
| `Zkc.Source.ProjectResolution` | Exact owner/alias lookup, injective name allocation and typed definition transport under actual keyed body-meaning hypotheses; not a native resolver proof |
| `Zkc.Source.ArgumentBinding` | Typed port permutations preserve operand occurrences and authored effect/stop order; public-label resolution and native elaboration remain adapter obligations |
| `Zkc.Source.Family` | Actual ingress, selected-member execution, fixed embedding and constructive role knowledge |
| `Zkc.Source.Protocol.Family` | Compact symbolic counts; source and both participant projections commute with instantiation |
| `Zkc.Probability.Iteration` | Complete finite transition mass, conditional retry tails and accepted-publication accounting |
| `Zkc.Semantics.Interpretation` | Program-producing interpretations, composition, execution fusion and complete execution related across representations under per-operation premises |
| `Zkc.Semantics.Preparation` | Immutable preparation within arbitrary stateful external calls; contextual preservation and resolution to the reference |
| `Zkc.Semantics.Preparation.Emission` | Event-only reference embedding and exact preparation accounting |
| `Zkc.Source.Program` | Typed finite source, explicit contexts, structured control and denotation |
| `Zkc.Source.FiniteControl` | Admitted runtime-bound families of existing typed branches/finite iterations, zero/index/count laws and uniform semantic call bounds; [portable adapter scope](design/local-control.md) |
| `Zkc.Source.Composition` | Sequence independently authored typed regions with proved capture/substitution behavior |
| `Zkc.Source.Region` | Compact computation binding with one shared suffix and proved agreement with tree source |
| `Zkc.Source.Definitions` | Shared acyclic source bodies, typed callee references and complete call/stop execution |
| `Zkc.Source.LocatedExecution` | Run resolved bodies at one role, preserve peer state and complete stop origins; classify local effects through existing conformance |
| `Zkc.Source.ControlAgreement` | Check separately bound shared guards/counts and connect accepted choices to actual local branches |
| `Zkc.Source.Protocol.Execution` | Execute typed common protocols with role-owned ports, stored protocol calls, separate message endpoints and fixed public loops |
| `Zkc.Compiler.Participant.Execution` | Lower common source into scheduled local/send/receive instructions and prove complete joint execution equality for shared definitions and loops |
| `Zkc.Source.Protocol.Role` | Direct open meaning of every common-source constructor and stored protocol table, with only one role's values and arbitrary typed incoming replies |
| `Zkc.Compiler.Role.Execution` | Distinct role syntax/interpreter, mechanical extraction, generic direct-source-role equality, actual local libraries, and resumable polling; [scope and native joins](design/role-execution.md) |
| `Zkc.Compiler.Role.Simulation` | Alignment through actual stored definitions, source-derived successful-prefix simulation and local/message failure-cut laws; no whole heterogeneous controller or native refinement theorem |
| `Zkc.Semantics.ResourceView` | Restricted heterogeneous state, exact returned/stopped effects and preservation of every outside cell |
| `Zkc.Compiler.Role.Resources` | Instantiate the resource laws on actual stored source-role programs and projected runtimes |
| `Zkc.Protocols.Sumcheck.Committed.Security` | Fixed-original, honestly committed adaptive Sumcheck with joint opening-loss bound; [precise security scope](design/committed-sumcheck.md) |
| `Zkc.Compiler.DefinitionInlining` | Optional capture-safe inlining with separate definition-reference renaming and complete execution equality |
| `Zkc.Source.RegionBounds` | Compositional semantic call bounds without expanding shared suffixes |
| `Zkc.Compiler.RegionArtifact` | Typed erasure and consumer-bound direct checking for `region-source-1`; [native connection](../docs/compiler/regions.md) |
| `Zkc.Compiler.RegionFolding` | Checked alias substitution through compact regions under total procedure laws; [logical-to-physical table instance](Examples/TableProtocol/Optimization.lean) |
| `Zkc.Source.LocalInputs` | Available inputs/captures and permitted-view locality |
| `Zkc.Source.PhaseAdmissionInterpretation` | Checked summaries under lawful interpretation |
| `Zkc.Compiler.Transformation` | Actual source/candidate checking under a selected refinement |
| `Zkc.Compiler.InputBinding` | Actual source-to-target input selection and coverage of an advertised refinement domain |
| `Zkc.Compiler.Analysis.Observation` | Sound observation summaries, weakening and justified use; distinct from exact recovery |
| `Zkc.Compiler.Analysis.Sampling` / `SamplingLocality` | Monotone sampling provenance and direct-channel locality with sampled results fixed; no statistical-independence or native-extraction theorem |
| `Zkc.Compiler.FactorOptimization` | Stateful factor reuse with source-produced facts and unchanged guards |
| `Zkc.Realization.Simulation` | Different value/state representations, retaining stops and events |
| `Zkc.Realization.Framing` | Exact length-framed payload decoding and suffix preservation; list-byte laws, not a proof of native codecs |
| `Zkc.Realization.RegionSimulation` | Lift local heterogeneous execution and immutable alias laws through compact regions; [checked physical-table client](Examples/TablePhysical/README.md) |
| `Zkc.Semantics.RelationComposition` | Heterogeneous component connections, contextual replacement and boundary representation changes |
| `Zkc.Semantics.Obligations` | Finite ordered derivations with independently supplied requirements, reusable facts and conditional rule/terminal soundness |
| `Zkc.Relation.Encoding` | Two-direction source/target adequacy with statement maps and arbitrary target witnesses; composition and terminal transport |
| `Zkc.Relation.Sparse`, `Zkc.Relation.SparsePolynomial` | Sparse matrix products, contractions, normalization laws and ordered multilinear evaluation |
| `Zkc.Relation.RankOne`, `Zkc.Relation.Padding`, `Zkc.Relation.Reference` | ONE/public/witness layouts, arbitrary-assignment reconstruction, zero padding and executable sparse relation checking |
| `Zkc.Relation.AIR` | Finite noncyclic trace constraints, derived read locality and polynomial degree; no quotient, lookup or STARK security theorem |
| `Zkc.Relation.AIR.Polynomial` | Exact active-row vanishing/divisibility bridge, multiplicative read adequacy and quotient degree under explicit interpolation/window premises; no native adapter or FRI/BCS security theorem |
| `Zkc.Relation.AIR.Embedding` | Injective ring embeddings preserve finite constraints, read footprints, degree and refusal windows for the same embedded statement and trace |
| `Zkc.Algebra.MultisetFingerprint`, `Zkc.Relation.AIR.ProductConnection` | Exact multiset fingerprints, prefix recurrences, collision-root counts and their connection to finite auxiliary AIR constraints; challenge independence and proof-system soundness remain protocol premises |
| `Zkc.Realization.Acceptance` | Input/output-indexed acceptance adequacy for arbitrary satisfying witnesses and actual following consumers |
| `Zkc.Protocols.Sumcheck.Acceptance` | Actual staged source to full-domain direct residual evaluation, using the maintained source completeness theorem |
| `Zkc.Protocols.Sumcheck.Connection` | Separate round producer and direct evaluator connected at the actual ordered point and value |
| `Zkc.Protocols.Sumcheck.Preparation` | Prepared values drive the actual source's next claim while construction/provider effects remain external |
| `Zkc.Polynomial.EvenOdd`, `Zkc.Polynomial.DegreeAdjustment` | Even/odd reconstruction, coefficient and degree laws, antipodal evaluation, arbitrary-word two-correction degree bounds, honest correction completeness and exceptional-challenge uniqueness; no FRI soundness claim |
| `Zkc.Polynomial.Table` | Immutable tables and all-ring ordered restriction/evaluation laws; [executable native client](Examples/TableProtocol/README.md) |
| `Zkc.Algebra.LinearCombination` | Finite module contraction, matrix pullback, diagonal and ordered product laws; mathematical basis of the shared compiler analysis |
| `Zkc.Compiler.Storage` | Dead discardable local storage erasure preserves exact abstract local outputs/failures, logical accounting and observations; native/admission correspondence remains separate |
| `Zkc.Algebra.BatchVerification` | Exact accepting-fiber count for fixed residuals and independent uniform field coefficients; no native RNG or protocol-security theorem |
| `Zkc.Protocols.LinearRelation` | Completeness and distinct-challenge extraction for a fixed linear map, with actual MSM/matrix product-map bridge; no probabilistic knowledge or native theorem |
| `Zkc.Algebra.BoundedResidues` | Recover integer conservation and word addition from field equations under bounds on complete expressions |
| `Zkc.Semantics.Obligations` | Finite multi-premise closure over independent requirements; soundness needs actual terminal truth and admitted rule laws |
| `Zkc.Protocols.Pedersen`, `Zkc.Protocols.Schnorr` | Actual-opening excess identity and two-response extraction; algebraic laws, not joint knowledge or Fiat–Shamir security |
| `Zkc.Protocols.InnerProduct.Folding`, `Zkc.Protocols.InnerProduct.Weights` | A round's commitment identity and repeated folding as one ordered contraction; algebraic results, not extraction or Fiat–Shamir security |
| `Zkc.Protocols.RangeProof.Relations`, `Zkc.Protocols.RangeProof.Bits` | Preserve the non-bit residual, connect parent commitments, and bound canonical integer reconstruction under explicit premises |
| `Zkc.Protocols.Sumcheck.CubicRound` | Four-coefficient cubic identity including false-constraint residuals |
| [`Examples.BufferStorage`](Examples/BufferStorage.lean) | Packed offsets refine complete immutable buffers through arbitrary publication sequences; reference model, not native allocator verification |
| `Zkc.Polynomial.TableExpression` | Actual ordered table cells and occurrence-list semantics with a proved partial degree-two compiler |
| `Zkc.Protocols.Sumcheck.TableSource` | Original table expression to checked verifier execution and interactive property premises |
| `Zkc.Probability.Disclosure` | Exact normalized release distributions and support-sensitive joint coupling laws |
| `Zkc.Protocols.Sumcheck.Security` | Source-bound ordinary interactive completeness and soundness |
| `Zkc.Protocols.Sumcheck.Optimization` | Checked verifier evaluation and its property transport |
| `Zkc.Protocols.Sumcheck.Framed` | Typed statement binding and transcript execution correspondence |
| `Zkc.Protocols.Sumcheck.Endpoints.Composition` | Actual supplied local programs and complete composition |

[Downstream clients](clients/) show ordinary theorem use from a separate Lake
package. A generic contract states an obligation; a proved law and its supplied
premises establish an instance. Typed framing does not establish FS security,
and a logical backend contract does not verify native backend code.

## Build and validate

The [toolchain](lean-toolchain) pins Lean 4.33.1; the [manifest](lake-manifest.json)
pins the main dependency closure.
The [Nix environment](../docs/development/README.md) supplies that exact toolchain and
can build both packages from source in a network-isolated build phase:

```sh
nix build .#formal
nix build '.#formal^library'  # sources and compiled library objects
nix build .#arklib          # optional package and standalone consumer checks
```

For interactive development inside `nix develop`, use the ordinary Lake recipes:

```sh
just build-lean          # lake build: every library and executable the package declares
just test-lean           # the structural, tool and consumer checks over it
just test-lean-integration   # the optional ArkLib package and its consumers
```

What `lake build` builds is `lakefile.toml`'s default targets, and
`test_checks.py` fails if a declared library or executable is not one of them,
so neither this page nor a workflow keeps its own list. What `just test-lean`
runs is discovered by [the shared test driver](../tests/run.py) from
`checks/*.py` and `consumers/*/check.py`; just forwards the command.

Build the optional library separately from `formal/integrations/arklib` with
`lake build`. The main build checks every maintained library/test/example module;
public root imports do not determine audit coverage. The declaration audit
inspects types and proof/definition bodies, including private and generated
versions, and permits only `propext`, `Classical.choice` and `Quot.sound`.
The independent `Tools.Interactive` and `Tools.Artifact` consumers, including their
`Tools.Crypto` dependencies, are included explicitly in the declaration audit and
compiled as `interactive-protocol` and `artifact-reference`. The crypto modules
provide the bounded, independent Keccak/Merkle reference used by oracle tests.
The importable [requirement-certificate transport](Tools/RequirementChecker/Transport.lean)
is also audited; its separate `requirement-checker` wrapper owns the process entry.
Other tool IO wrappers
are compiled separately. These checks do not certify Lean's
kernel, its native code generator or the adequacy of a theorem's statement.
The maintained tool controls include isolated forbidden-axiom, import-header,
input-capacity and executable-selection regressions. The
[build workflow](../.github/workflows/ci.yml) runs documentation and source/harness
checks automatically on pull requests and pushes to main. Its manual `main`
scope runs main builds, exhaustive audits, standalone consumers, enforcement
controls, compiled tool controls and design experiments. Manual `optional` and
`fresh` scopes additionally run ArkLib and reproduce both formal packages without
a restored project cache. These scopes need the
[documented runner capacity](../docs/development/maintenance.md#workflow-scopes-and-runner-requirements).
Passing quick checks does not establish any of these formal results, and a
workflow definition is not evidence of a hosted run.

For fresh builds, choose new output directories:

```sh
python3 checks/check_foundation.py --output /tmp/zkc-foundation
python3 reproduce.py --dependency-cache .lake/packages --output /tmp/zkc-main
python3 reproduce.py --with-arklib --dependency-cache .lake/packages \
  --integration-dependency-cache integrations/arklib/.lake/packages \
  --output /tmp/zkc-with-arklib
```

The copied foundation builds without external package imports or prior objects.
The command first parses headers in the configured root Lake environment, so
the invoking checkout still needs its declared package resolution. The full
reproducer copies current build inputs and materializes exact Git sources
without their Lean objects. It builds declared targets, audits
dependencies/axioms, and builds standalone clients.
Omit cache options to fetch the manifest URLs. The installed Lean/Std toolchain
remains trusted. Source drift causes failure; historical snapshots are not inputs.

The [original-source artifact reference](design/artifact-reference.md) explains
`Tools.Artifact`, its public cryptographic service and its independent native
comparisons. Executable consumers and framing lemmas have separate assurance
scopes; neither imports an implicit Fiat–Shamir security theorem.

## Scope and development

The [research agenda](design/research-agenda.md) separates future theory work,
upstream proof gaps and native realization from implemented formal claims.
The [virtual-product example](Examples/OpeningReduction/README.md) adds actual
cubic rounds returning opening obligations and a conditional terminal-error bound.

The common `Proc` denotation does not prescribe a flat compiler IR. Protocol
structure, construction choice, role availability, logical algorithms and physical
representation have distinct retained information and transformation obligations.
Native expansion remains subject to the renewed MLIR design review in the handoff.
