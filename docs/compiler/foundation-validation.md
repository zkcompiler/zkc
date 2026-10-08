# Foundation validation

The selected IR foundation is implemented and stabilized at the scope of the
[completion contract](ir-foundation.md#completion-tests-and-limits). This page
maps that scope to maintained checks and their limits. [Status](../status.md)
owns current support; the [test guide](../../tests/README.md#selecting-checks)
explains how to select and run checks.

The implementation uses one mathematical SSA program, the
`protocol → participant → exec → physical` profiles and a shared interpreter.
Composed clients use ordinary operations and installed primitives. Full consumer
migration, native Lean correspondence and cryptographic security have separate
completion conditions in the [roadmap](../roadmap.md).

## Completion evidence

| Requirement | Owning mechanism and maintained evidence | Boundary |
|---|---|---|
| Generic composition and realization | Mathematical/participant verification, transparent local bodies, recipe lowering, physical bindings; native mathematical and mixed-domain clients | Installed operations and explicit executable profiles |
| Structured relations | [Relation bindings](relation-bindings.md); R1CS/AIR configuration, public assignment, witness and actual acceptance controls | A declaration binds meaning; authored equations decide satisfaction |
| Domains and randomness | `native_domains.py` and its Rust API client execute BN254 G1/G2/scalar messages, typed random draws, KoalaBear/ext8 and Ristretto equations; malformed suite/query-origin controls run in C++ and independent Rust admission | No BN254 challenge suite; typing/transport/wiring evidence supplies no sampling-distribution theorem |
| Setup authority | `native_setups.py` and its Rust API client execute two authorized KZG setups; swapped public/prover keys, terminal key operands and wrong input authority refuse | Original-port authority; no path-specific mixed-setup input selector |
| Bulk mathematics and capacity | [QAP/AIR/GT clients](mathematical-composition.md): independent numerical references, all rows, exact terminals, dynamic sizes and all three lowering modes | Executed ranges and simultaneous count/byte/work limits are explicit |
| Early completion and custody | [Entry completion](entry-completion.md), runtime frame-failure controls, joint scheduling, native attempts, early setup-backed acceptance/rejection and proof exhaustion | Owner-local completion; separate resources retain exact roots |
| Retry effects and budgets | Native attempts preserve RNG/service successors, consumed work and discarded prefixes; an invocation ceiling cannot be raised by attempt policy | Completion predicates do not supply a retry-probability theorem |
| Proof/transcript boundaries | Actual producer/validator execution, canonical observation, reordered transcript and stale state controls, input/context/setup binding and trailing-data refusal | One-shot output can be a prefix; independent validation decides acceptance |
| Observation inputs | Resource-origin, relation-composition, native service and verifier-view controls retain actual source operands, draws, receives, roots, ordered stops and disclosures | Actual operand/substitution checks cover the recognized preservation relation. Honest delivery and sampling laws remain separate premises; no affine analyzer or general correspondence theorem |
| Growth and structured control | Composed-state and nested-data clients, empty/zero-trip cases, nested calls/loops and role-count disagreement; compact carriers as runtime lengths grow | Finite bounds and formation budgets remain enforced |
| Source/candidate and independent admission | [Adjacent preservation checks](preservation.md), direct comparison of serialized programs with physical SSA, source-bound schedules/deployment maps, independent Rust mutations and C++/Rust/Lean signature conformance | Bounded checks compare actual adjacent subjects; unsupported equal rewrites can refuse. Old-reader refusals supply no native Lean execution semantics |
| Installed consumers and coexistence | Fresh static/shared component consumers, service-extension build/link and help smoke checks, contributed-domain/base installations and independent restored execution; broad compiler/Rust/cross-language checks | Same-version extension API; standalone service-extension execution is not exercised, only build/link and help smoke checks. No stable plugin ABI or automatic Rust/Lean implementation for a contributed primitive |

The [Groth16 structural row](ir-foundation.md#protocol-corpus-and-structural-requirements) is covered by the QAP/coset/MSM/GT composition together
with BN254 G1/G2 messages and actual random draws in the domain client. Authorized
KZG setup composition independently exercises key custody. This is not a complete
randomized Groth16 prover, a Groth16 proving-key format, or a succinct verifier.
The AIR/oracle and shrinking inner-product clients likewise exercise required
mechanisms without claiming full FRI, zkVM or BP+ library implementations.

## Source-to-artifact checks

Compiler publication uses the following checks:

1. Formation establishes admitted syntax, types, ownership and operation contracts.
2. Bounded adjacent checks compare actual preparation, projection, construction,
   recipe and physical operands/control against retained subjects. The internal
   materialization validator checks complete local bodies and bindings; the
   public Exec-to-Physical projection query covers participant flow and metadata.
   Separate same-profile executable API checks require whole-unit identity.
3. Emission checks decoded program instructions against retained physical SSA,
   the joint schedule against prepared source order, and deployment role/port maps
   against original source coordinates. The exact published bytes are checked.
4. Independent runtime admission, direct equation/transcript references,
   adversarial controls and installed-consumer execution test the selected
   realization and host contracts.

These layers compose implementation evidence, not a general refinement proof.
The checkers recognize a bounded relation; an equal but unrecognized rewrite may
refuse. Descriptor/source admission, primitive arithmetic and codec libraries,
compiler/runtime implementations and the toolchain remain explicit premises.
Native Lean meaning and source/artifact differential correspondence remain open.

Runtime `admit_supplied` checks structure and installation. General
`admit_physical` refuses native source correspondence; proof hosts require an
application-authenticated deployment. Shared C++/Rust/Lean signature checks and
[formal support](../../formal/SUPPORT.md) retain their declared subjects. Neither
source inspection nor an earlier installed build verifies a changed public API.

## Regression coverage

The compiler and Rust workspace suites cover formation, preservation, admission,
execution and host lifecycle. Cross-language controls check shared signatures,
retained source/Lean routes and explicit native-reader refusals. The
[CLI walkthroughs](../runtime/bundles.md) are executed from documentation, including
wrong pins, truncated proofs and trailing bytes. Static/shared
[installed consumers](../../tests/consumer/package-components.cmake) compile public headers and
run NativeCompiler-to-runtime journeys. Contributed domains exercise acceptance,
refusal and restored composite execution against independent modular arithmetic.

Mutation controls must change actual operands and bindings while preserving
formation where possible. The maintained cases include:

| Case | Required result |
|---|---|
| Same-typed send, guard, query/call argument, finish value or yield substitution | Candidate can remain well formed; the relevant correspondence check refuses with the intended cause |
| Receiver input substituted for actual receive; second draw replaced with first | Refused even when honest execution happens to produce equal values |
| Swapped captures, carried roots, helper/application arguments or nested loop results | Refused at the owning preparation/projection/recipe boundary |
| SSA renaming, generated symbols selected by checked interface maps, repeated helpers, rebuilt captures, legal Boolean and field/group select folds, and dead total work | Accepted under the stated mathematical relation, with original formation checks and realization-capacity obligations preserved |
| Equal but unrecognized rewrite, such as field commutation without a checker rule | Unsupported by the checker; refusal is not proof of inequivalence |
| Induction value confused with trip count; previous iteration's carried value substituted for a fresh receive/draw | Refused even if values happen to agree on the first iteration |
| Same-typed role entry ports, ordered outputs or multi-role result coordinates swapped | Refused against the source's actual positional binding |
| Projection metadata removed or added; supplied exec and older source inputs | Preserve existing metadata obligations, never infer provenance from added metadata, and apply exec-to-physical participant comparison independently of it |
| IR mutated after an earlier check, including local bodies during storage release | Revalidate the changed subject before publication; earlier results cannot certify it |
| Zero-trip/nested loops, conditional completion and unused action results | Correct returned/stopped prefix and successor obligations remain, including relevant finite failures |
| Long SSA chains and checker work boundaries | Iterative bounded checking; unsupported/limit refusal is distinct from success and source invalidity |
| Wrong polynomial weight/table/factor or generated-kernel operand | Refused without reusing the producer recipe as its own oracle |
| Mutated challenge absorption/order, setup port or validator acceptance mapping | Refused by the corresponding construction/authority check |
| Same-typed operand swap in actual serialized candidate; wrong bundle entry/schedule | Refused against the retained checked subject, including after storage release |
| Existing direct, unsimplified and optimized corpus | Maintained advertised behavior; any narrowed check scope is explicit and reviewed |

These controls provide bounded implementation evidence. Numerical and transcript
references are independently written but reuse upstream arithmetic and transcript
libraries. Signature agreement and old-reader refusals supply no native Lean
execution semantics. Optional integration, sanitizer and benchmark checks have
their own commands and prerequisites; passing the core suites does not imply they
were run.

## Deliberate boundaries

The transcript suite allow-lists are profile admission rules. A new domain in the
catalog does not automatically extend a proof version. Independently written
reader checks remain useful; they are not consolidated across languages.
Canonical leaf encoders remain shared with existing consumers. Replacing them
with another encoder merely to avoid a scan would add an unvalidated owner.

Pairing preparation has a scratch-memory allowance separate from the retained
GT output. The 32 KiB check is active under reduced value capacity; boundary tests
cover 32,767 and 32,768 bytes. It is not a subgroup CPU-work counter.

Two optional combined fault controls remain open: a returned-frame custody
refusal injected through the real native backend, and a proof-host aggregate
containing openings from two setups followed by a wrong-key terminal. Existing
generic failure-injection, positive native custody, recursive codec and separate
wrong-key terminal tests cover their constituent contracts. They are not evidence
that those exact combined fault scenarios have been executed.
The older observation host also conservatively reserves the full wire ceiling for
a matrix observation, so lowering its live-byte budget below that ceiling can
refuse even a small matrix. This remains a prepared-host migration consideration.

Loading and execution have separate ledgers. Per-value decode preflight runs
before aggregate loading admission. The 16 MiB JSON envelope counts duplicated
hexadecimal public/data entries; raising the numeric count ceiling alone does not
raise that capacity. Whole-process memory, cumulative subgroup CPU metering and
reference-based input preparation require a separately designed host package.

`protocol.finish_if` is an ordered control action. The total public-coin analysis
refuses it under `public-coin-dependence`; native proof construction supports it.
Generic transforms that assume the suffix executes need their own preservation
argument. Aggregate capability flow, private-match histories, dynamic composition
and new commitment schemes retain their explicit formation restrictions. No
required reviewed composition depends on weakening those restrictions.

## Migration and removal

The [migration inventory](migration.md) names remaining frontend, source/Lean,
table, prepared-host and public-tool consumers and their removal conditions.
The obsolete service-only carrier and native participant/run tags are refused.
Proof policies `/1`–`/4` still have distinct supported clients; they are not the
consolidated Program and Run formats.

A new representation counterexample reopens its owning foundation contract.
Writing another protocol from supported mechanisms is library work. Each migration
moves required behavior and evidence, then removes the replaced path when its
last consumer moves.
