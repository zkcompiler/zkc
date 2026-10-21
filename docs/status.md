# What the implementation supports

The supported implementation is `.zkc` frontend → Protocol IR (PIR)
(`protocol`, `participant`, `exec`, `physical`) → `zkc.program/0` → the Rust VM and
interpreter with Entry/proof/joint Hosts. Direct MLIR enters the same compiler.
[Specification](spec/README.md) defines contracts; this page records support.
Links identify maintained checks, not a claim that they ran for this revision.

## Current public interfaces

Artifacts use one current schema with exact tags, record shapes and unknown-field
validation. Boundary versions remain `0` during development; equal versions do
not guarantee compatibility across builds. Their specification owners define the
accepted contents; the [maintenance policy](development/maintenance.md#format-versions)
defines when versions change.

| Interface | Contract |
|---|---|
| Executable program | [`zkc.program/0`](spec/formats/program.md), a physical participant program |
| Source Entry | [`zkc.entry/0` and `zkc.language-interface/0`](spec/formats/entry.md#published-entry-package), authenticated source, input/result schemas and selected artifact |
| Joint execution | [`zkc.run/0`](spec/runtime/joint.md), participants, schedule and invocation policy |
| Native proof | [Policy, descriptor, deployment, construction map and invocation binding](spec/formats/proof.md), with `zkc.native-origin/0` occurrences |
| Installed declarations | [`zkc.contract-declarations/0`](compiler/operation-contracts.md), declaration inventory; the language catalog contributes an opaque compiler fingerprint |

Use `zkc run`, `prove` and `verify` for named Entries, and `bundle run`,
`bundle prove` and `bundle verify` for lower-level artifacts. In the C++ SDK,
`Zkc::Compiler` owns compilation and packaging;
`Zkc::Driver` separately owns CLI parsing. Request `Tools` for installed commands.
See the [SDK reference](../compiler/README.md#components-and-ownership).
Rust package, run and deployment admission take trusted 32-byte SHA-256 pins;
CLI adapters own hexadecimal spelling. Backend service installation uses
`service_support` returning a named `ServiceSupport` signature and reply bound.

## Execution foundation

`zkc_runtime::vm::Program` owns structurally admitted code independently of a
backend. Loading links one owned backend before entering frames. The internal
VM instance owns complete invocation admission, frame identity and nesting,
installed calls, retained values and budgets. Participant loop frames reuse
typed input layouts retained during admission. Return handoffs carry owned
values and their backing obligation; VM recording snapshots retain preparation
accounting. Primitive value checks also reside in the VM;
`zkc_runtime::interpreter::Runner` owns control evaluation and pending actions.
Hosts use that interpreter for Entry, proof and joint execution. The
[VM contract](spec/runtime/vm.md) defines authority, failure and accounting.

Logical [Kernel IR](spec/ir/kernel.md) owns total numerical closures and their
ordered Local invocations. Preparation and participant demand lowering form
units; the physical plan retains those units alongside the selected Local
candidate until independent numerical and physical checks permit publication.
Export receives the resulting physical program without Kernel operations.
Normalization and numerical recipe checking consume Kernel-owned standard
functions directly, with separate structural facts and call-specific selection
restrictions.
Existing installed backends execute the resulting operations. The checked physical
schedule records optional binding releases, including conversion temporaries;
materialization performs no lifetime selection. Private numerical schedules use
standard SCF loops and are independently checked before Local lowering.
Native [numerical calls](spec/runtime/numerical.md) have typed immutable storage
views, private initialized destinations and scoped construction/work limits for
dense vector arithmetic and reductions, matvec/split, BLS table fold and
KoalaBear opening quotient and a weighted sum of selected off-domain column
quotients on BN254 Fr and the three KoalaBear fields. Compiler-generated pointwise expressions pass
borrowed columns and scalar captures through ordinary installed bindings.
Compiler buffer lowering, target-specific vectorization and JIT/AOT engines remain
unimplemented. These execution boundaries do not establish formal native
correspondence.

## Source and application boundary

`run` and `proof` explicitly select joint execution or proving/verification.
`zkc.toml` supplies the module/asset map; the CLI discovers the nearest manifest.
Explicit local workspace catalogs select leaf packages alongside path
dependencies, preserve capture identity, and report selected-edge provenance in
`inspect --view=api`. The installed package includes the catalog and library sources.
Batch coset extension is installed on BN254 Fr, KoalaBear and its quartic/octic
extensions. It constructs one private column-major output and retains non-base
shifts; shrinking checks each column's actual normalized degree. Compiler,
runtime admission and native signatures independently declare the operation.
The single-word domain analysis does not yet transfer flattened batch facts.
Batched coefficient evaluation is installed on the same four fields. It shares
one ordered output domain and constructs one private column-major vector;
coefficient blocks may have zero or non-power-of-two height. Shrinking admits
only zero discarded tails. AIR quotient splitting retains source interpolation,
capacity and padding checks before invoking the batch operation once.
Direct coset point evaluation is installed on the same four fields, sharing
weights across columns without reconstructing coefficients. It handles on-domain
points and arbitrary evaluation words; neither path proves a degree bound or
authentication. Source controls check independent integer expectations and refusals.

Polynomial opening APIs bind canonical cosets, column batches, descriptors and
accumulators in private checked views; row evaluation derives its point from
the admitted query index. These are mathematical context checks. Column reduction uses one private weighted
quotient result with reusable call-local denominator/prefix arrays. AIR witness
reads select the same core reduction in read order; known reads consume no weights.
Commands accept unique short or qualified Entry names. Execution filters omitted
names by run/proof kind; inspection and compilation require a single Entry.
`new` and `init` create separate protocol and Entry files with input templates;
`prepare` creates missing maps while preserving existing values. Manifest-relative
paths supply omitted inputs, proof files and run results. Runs obtain a fresh
session unless supplied explicitly. `run --dry-run`, `prove --dry-run` and
`verify --dry-run` share native input validation without execution. Source
execution compiles in memory; pinned package mode is explicit.
The public Rust `project` API owns project/compiler access, path layout and
preparation plans. Commands print human summaries; automation uses `--json`.
`zkc check` reports canonical Entry names and checks definitions without selection; a positional Entry selector also checks closure
and mathematical correspondence. `zkc check` and `compile` accept explicit
[project manifests](language/README.md#project-inputs) or module/asset maps.
Language resolves explicit modules and R1CS/AIR Assets, checks generic libraries
and closes selected Entries. It supports scalar mathematics, Boolean formulas,
nominal products/variants, static parameters, unified file/inline/external modules,
explicit interface conformance, capabilities and
permissions, lexical scopes and patterns, mutable bindings with inferred region
state/captures, statement-scoped participant inference, nested ordered calls,
helper result inference, expression-wide structural type constraints, partial
static arguments with positional or named binding, named value/service arguments,
Unicode 17 NFC names, scoped mathematical operators and paired-delimiter calls
with import activation, explicit fixity and local module bindings, catalog-checked
primitive definitions and an embedded scalar prelude,
local short-circuit Boolean operators and total Boolean formulas, inferred usage, catalog
and natural preconditions with explicit contract checking, derived boundary admission, unified data/service arguments,
source rejection with `require`, formal polynomial intrinsics, checked
pointwise `map` of scalar helpers over vectors, general finite reductions,
statically bound scoped Math/Local callbacks with generic apply/forward and
module wrappers, local control,
messages, services, static protocol composition, bounded repetition and conditional completion.
Independent source comparison checks emitted MLIR against checked definitions;
[source semantics](spec/language/README.md) owns exact limits.

An authenticated `zkc.entry/0` package retains the original, source interface,
compilation choices, selected artifact and the expression assets the artifact
references. The Host binds named logical inputs and results to the independently
admitted program and checks every reachable asset reference before any
invocation. It trusts compiler publication
for source correspondence; it does not interpret retained MLIR. Maintained
[Schnorr and Sumcheck projects](../examples/projects/README.md) exercise this path.

Fixed source arrays use static numeric indexing. Private ingress without an
admitted validator, member-generic conformance and zero-leaf messages refuse.
Abstract callable signatures with member generics can be checked and inspected,
but modules implementing them are not supported. Associated types cannot
introduce member-specific static parameters.
Implicit role remapping, natural equation solving
and inversion of associated types are outside the source profile.
[Scoped computations](spec/language/definitions.md#scoped-computations) use the
ordinary checked Body and type solver. Projection-aware Copy+Drop captures,
mutable snapshots, static scoped captures and lexical module resolution close
to ordinary private helpers with explicit environment inputs. Independent
capture and specialization checks reject mapping and coverage mutations before
source-to-MLIR comparison. Compiler and native tests cover fixed modes, effects,
owner inference, forwarding, aggregate captures and authored evaluation order.
Runtime function values, escaping computations, outer writes and captured
services are unsupported.
[Finite domains](spec/language/definitions.md#finite-domains) support registered
constructors, composed factories, module selection, static helper arguments,
callback captures and nested local/protocol control. Joint closure retains
immutable operand aliases and independent witnesses check closed recipes and
capture layouts. Source checking and native tests cover forwarding, zero trips,
participant availability and specialization mutations. Registered finite folds
and collects now reach retained finite IR through independently checked adapters.
Native source tests cover ordered and Unit state, mixed state dependencies,
filtered stops, strict zip admission, packed record sequences, repeated calls,
dependent inner ranges and mutable capture snapshots. Fixed source arrays now
adapt through independently checked sequence construction, including records,
empty arrays and Unit items. Source item-provenance checks
now cover callback-local `where item_from(input, domain)`, optional input labels,
arbitrary slots, multiple independent origins, generic restricted forwarding,
named argument order, nested captures and invariant local-region inputs. Native
controls include exact normalized module conformance, independent authored
selector reconstruction and mutation refusal. Inner conditions preserve outer
catalog/natural inference. Labels and canonical maps are exposed separately in
declaration inspection; they add no runtime closure or finite IR attributes.
Retained witnesses also check formal callback slots and authored invocation
identities through nested regions. Total index literals, static natural index construction and comparisons now
support mathematical ranges and filters through ordinary realization. Total
access now uses exact item/container bounds, declared Math input conditions and
callee-first closure requirements. Native checks independently discharge each
call and finite callback, including equal-extent captures. Closed source checks
cover all retained zip/matrix-view formation and exact fixed collection sizes;
sequence constructor evidence preserves fixed-array lengths across adapters.
Source fact extraction follows aliases, full projections, literal indices,
declared input conditions and results of concrete checked Math helpers. Exact
forwarding preserves identity; unfiltered collection construction preserves
shape through wrappers and record projections without identifying new values.
Result dependency walks are iterative and memoized. Unfiltered finite
collections retain their domain's known count
and leaf extent; filtered collections provide upper counts, with zero also exact.
Direct Math calls to finite definitions remain finite computations at their
call occurrence during specialization, preserving actual range endpoints and
container evidence. The independent specialization reader checks the domain,
callback and capture substitutions. Local declaration formation and ordinary
domain-parameter helper boundaries retain their generic formation requirements.
Collection cardinality can cross those boundaries; successful Local guards,
arbitrary computed scalar results, control-flow joins and loop invariants do
not acquire source summaries.
Fixed field-array output follows the installed BLS12-381.Fr contracts; other
field backends may lack that realization. The [shared libraries](../libraries/core/README.md#finite-computations)
now expose ordered and total folds, collection, explicit combiner modules,
field/group accumulation, filters and materialized vector reducers. Ordinary
collection arguments share one checked conversion at scoped-domain parameters;
matrices require explicit views. Source/native tests exercise records, group
commitments, nonassociative order, nested domains, skipped inverse failures and
reducer failure order. [Finite binders](spec/language/definitions.md#finite-reduction-binders)
now use that same path: Local and total Math targets, filters, independent products,
dependent nesting, aggregate captures and direct protocol/module use. One
lexical binding is selected before body/result inference. Shared source/domain/
scoped witnesses replace the old ring-only extraction checker. Library-owned indexing now uses the same typed callable selection and retained
binding checks. Standard vector, matrix, group, sequence, index and field-array
modules expose total access; checked Local access requires explicit rebinding.
Static source-array projections retain their existing capture paths.
The staged parser resolves
notation environments after imports and before bodies. Callable notation uses
ordinary signature constraints and authored evaluation order, with descriptor
arity and scope checked by the independent binding witness. No formal
elaboration-correctness theorem is claimed.

Local effect contracts use `effects(...)` before `where`. Open helper bodies
retain bounded callback dependencies, including forwarding and literal captures;
closure and independent witnesses reconstruct selected effects. Callback ceiling
omission allows the tracked Local universe, while truly abstract Local outputs
require an explicit contract. Local finite admission remains stopping and finite
callbacks remain stop-only. This is compiler effect checking, not a totality or
protocol-security result.

Source/native boundaries retain exact source/public JSON names while encoding
symbols as UTF-8 segment hex and role/setup/case labels as roster ordinals for
ASCII and Unicode alike. Both Entry setup authority and material keys are
translated. Generated Rust bindings use injective UTF-8 escapes and allocated
names, preserving source keys. Artifact and transcript bytes therefore change
even for ASCII source; version `0` retains one current schema and no legacy
readers. The [source/native contract](spec/language/translation.md#source-and-native-names)
and [SDK dependencies](../compiler/README.md#installed-package-discovery) own the
encoding and pinned Unicode/NFC boundary.

Checked public API inspection is available through `inspectPublicAPI` and
`zkc inspect --view=api`. Its compact export graph covers aliases, types and notation
routes; captured source references retain the selected provider and canonical
target. Private field names and associated representations are omitted from
public type contracts. The bounded diagnostic view supplies no linking authority
and changes no source or executable identity. The
[language specification](spec/language/definitions.md) owns its format and limits.

Checked notation inspection is available through
`inspectNotations` with `NotationInspectionOptions.includePrivate` and
`includeInstallation`, and `zkc inspect --view=notations` with `--notation-private` and
`--notation-installation`. The version-0 diagnostic view covers descriptors,
bindings, scopes and occurrences, with private/local data hidden by default and
installation data opt-in. [Notation limits](spec/language/notation.md#bounds)
set 4096 descriptor keys per environment including fixed Boolean descriptors,
64 delimiter holes and 8 MiB output; lowered SDK limits are rechecked on retained
projects. This does not supply an LSP server or formatter.

Relation and target/input/output/continuation clauses state intent; declarations
alone add no runtime guard, satisfaction fact or security theorem.
Original PIR retains all closed declaration contracts and exact relation
formula references. Native verification checks ownership, complete Math ABI,
port types and roles, clause shapes and agreement of an entry statement with
retained targets. Source proof statements retain the exact selected target name;
its owned clause supplies the decision role. The logical source interface
independently checks that selection against the verifier, and native proof
deployment checks the recovered decision role against its validator.
The version-0 [structured export](spec/formats/structured-source.md)
includes formula links and one contract-table row for every protocol, regardless
of the selected Entry. Application expansion retains declaration metadata;
participant projection erases contracts, formula links and selected-target
references explicitly. This adds
no runtime predicate evaluation or proof transport through those transforms.

## Foundation capability map

| Capability | Support and boundary |
|---|---|
| Numerical scheduling | [Kernel](spec/ir/kernel.md) retains the mathematical subject and checks a private standard SCF loop schedule before Local execution. Explicit collect–fold fusion supports total field-vector/field-sequence producers and element or same-position indexed consumers; unsupported observations retain materialization. Nominal values, domain admission and ordered state are checked independently. No vectorized schedule, writable-buffer ABI or new VM instruction is implied. |
| Scalar, collection and polynomial mathematics | Nominal Algebra field/group vectors, indices, field matrices and field arrays, with ordered `algebra.array_from_elements` packing. A shared collection interface reports structure without granting finite, mathematical, Copy/Drop or wire admission; shape evidence retains the logical family. Source syntax, logical binding spellings and native codecs retain their meanings; builtin tensors have no compatibility alias. Total expressions and checked realization recipes; [structured mathematics](compiler/mathematics.md). Kernel installation alone does not supply a mathematical recipe. |
| Group identity | Total `intrinsic<G>("curve.identity")`, Algebra identity and independently checked native recipe. Dalek Ristretto255 and prime-order Edwards25519; arkworks BLS12-381 G1/G2/GT and BN254 G1/G2/GT, including multiplicative-one GT. Empty MSM identity is checked for the six installed dense group families; [contract](spec/domains/values.md#group-identity). No native proof claim. |
| Shared expression evaluation | Captured [Ring and Bundle terms](spec/language/definitions.md#asset-domains-and-projections), derived static dimensions, retained Entry assets and independent Host preflight. [Checked structural sharing](spec/domains/ring-expressions.md#structural-sharing) preserves ordered substitution and read obligations. The [generic Sumcheck library](../libraries/protocols/polynomial/sumcheck/README.md) derives its width and degree from its Ring parameter; it remains a public-table client without a PCS or native security theorem. |
| Source clients of imported AIR | The [imported AIR client](../common/tests/fixtures/projects/imported-air/README.md) checks actual trace, configuration and public inputs. The [AIR STARK client](../common/tests/fixtures/projects/air-stark/README.md) adds base-field trace commitments, scoped extension-field quotient chunks, OOD/DEEP equations and FRI through ordinary source libraries and separate proof Hosts. The single-table profile covers one present table's assertions; the three-table profile adds whole-Bundle Boolean multisets and signed field balance through LogUp. Security reductions for both remain separate work. |
| Pointwise vector maps | Source `map` applies one static scalar `math fn` over installed field vectors through [checked numerical realization](spec/ir/protocols.md#checked-pointwise-maps): shapes first and O(formula) code. A common semantic reader independently interprets source and candidate payloads, admitting sharing and commuted field arithmetic; helper calls are interpreted from the original source and installed contract laws remain a shared foundation. Shape mismatches are backend failures (`rejected:require`); field constants, addition, subtraction and multiplication are limited to Ring depth 1,024. The [KoalaBear/Ext8/Ext4 comparison](../common/tests/kernels/test_pointwise_polynomials.py) checks maps, Ring rows and coefficients, and coset kernels against integer arithmetic, including the off-domain interpolation distinction. Installed numerical expression calls support map, sum and product over borrowed columns and scalar captures; bulk vector alternatives remain available. No first-class function value or foreign memory ABI is introduced. |
| Finite vector reductions | [Source binders](spec/language/definitions.md#finite-reduction-binders) use general scoped consumers and finite IR. Arbitrary vector reducers collect first and call once. Native `vector.product` has empty identity one across the installed field families, with independent C++/Rust admission and normal resource charges. Default-false [fusion](spec/ir/protocols.md#optional-vector-reduction-fusion) handles adjacent single-use map/native-sum through a dot product or supported numerical expression, with every original row guard retained. Its relation is values and ordered shape refusals under sufficient resources, not equal exhaustion or a memory bound. The scalar Lean bridge does not cover vector-map/reduction correctness. |
| Mathematical shape and bounds | A shared MLIR-free [fact kernel](spec/domains/mathematical-facts.md) supplies exact origin/axis equality, strict bounds and exact/upper cardinalities. Independent source and SSA adapters replace duplicate closure rules. Helper observations are scoped to immutable symbol closures, with explicit rebuild and pass-manager invalidation controls. Nested work is cumulative and distinguishes absence from capacity. Source symbolic naturals retain their interpretation; guards and nominal types remain unchanged. Core scope intersection is available, while production reached-guard and loop-invariant propagation remain unsupported. |
| General finite IR | [Typed domains and total/Local fold and collect](spec/ir/finite.md) retain static helpers, complete entry admission, exact bound provenance and state dependency closure. Declaration-owned laws, structural SSA views, separate transient equation matches and shared producer emission support checked loop fallback, native sum/product/dot/MSM, elementwise fields and sum/product reductions of accumulator-independent pointwise field expressions. Selected matrix rows and columns use scalar contractions; admitted nested collections use one whole matvec, preserving empty-outer admission. Total callbacks expose ordinary helper calls and fixed pack/projection pairs remaining after canonicalization before optional bulk selection, while retaining the source of that selection for comparison. Nested indexed helpers preserve callback extent/bound premises and exact positional argument identities, including selected matrix axes. Independent readers check actual candidates, including checked original-helper normalization for total finite recipes and `local.realize`. Bounded DAG sizing and a per-callback structural ceiling preserve later small opportunities without refunding spent work. Optional lane or payload-comparison capacity retains checked ordered fallback; required-reader exhaustion is diagnosed separately. Checked candidate publication is shared. Opt-in decision records distinguish missing evidence, actual capacity, policy and recipe restrictions, ordered retries and nested publication boundaries; preparation and total Math lowering also expose remarks and IR dumps. These observations supply no checking evidence. Generic canonicalization/CSE preserve domain admission. [Handwritten controls](../compiler/test/fixtures/finite/README.md) cover mutations, failures and 2^17 field workloads. Full fixed-array/matrix fallback additionally requires the native checked-access contracts; the source frontend now uses checked adapters into this IR. No Lean-to-native bridge is claimed. |
| Calls, roles and control | Static application, role projection, structured local control, nested repetition and [conditional completion](compiler/control.md). General dynamic protocol composition remains open. |
| Structured values | Products, alternatives, extents, checked indexing and [nested immutable data](compiler/mathematics.md), including independently shaped matrices; source sequence elements include contextually packed records, tuples, source arrays and empty products, with explicit packing/unpacking and source comparison; affine and non-Drop elements are excluded. Persistent sequence storage and retained validation support default-budget Local collection of 16,384 indices and 8,192 two-index records in maintained controls. Whole-value encoding has a separate peak-storage limit; a collection that executes locally can exceed it when exported. |
| Affine resources and services | Exact-origin analysis, state successors, resource custody, entry service aliases and failure cleanup; [resource origins](compiler/resource-origins.md). Equal roots do not prove equal state or independent randomness. |
| FRI source library | [Binary FRI](../examples/projects/fri/README.md) over natural-order two-adic cosets, with commitment/fold/query/terminal checks and independent-reference tests. The library retains a checked coset word across folds; the AIR library consumes the authenticated positions and values. An independent Lean model of its verifier with ideal commitments is [complete on codewords and has a round-by-round soundness theorem](../lean/docs/spec/fri-security.md), with interactive bounds in the unique-decoding regime and up to the cube-root proximity radius `1 - (ρ + η)^(1/3)`, also stated over the verifier's residual processes, and transferred to a Fiat–Shamir bound for adaptively chosen initial words with one key for the query block, with [commitments read in the clear](../lean/docs/spec/fri-security.md#fiatshamir-transfer) and with [words committed](../lean/docs/spec/fri-security.md#committed-words) by Merkle trees with one field element per hashed leaf, in one random oracle with the hash calls. The committed bound covers acceptance together with the initial word being far from the code for the extraction at a verifier checkpoint, completed with zero at the entries the extraction misses. The model is a transcription of the library verifier, not the compiled library; the implication from an application's bad event to that checkpoint event, the installed schemes' leaf encoding (tag, codec, width and height), the source's sequential position draws and the compiled verifier remain separate obligations. |
| Pairing groups | BN254 and BLS12-381 each install G1, G2 and a prime-order target with group arithmetic, `pairing.check`, `pairing.apply`, canonical compressed codecs and native frames; [contract](spec/domains/values.md#pairing-field-capabilities). BLS12-381 G2 uses the 96-byte compressed encoding of the Ethereum consensus specifications. Independent arkworks comparisons and Ethereum ceremony points check arithmetic and encodings; no native adequacy proof. |
| General numerical composition | Installed field/group/vector/matrix, polynomial, pairing and oracle kernels with [composed clients](compiler/mathematics.md) and [changing numeric state](compiler/mathematics.md). The [linear-expression library](../libraries/core/README.md#linear-group-expressions) composes ordered scalar/point terms and evaluates one equation through an ordinary MSM; authors combine shared-basis coefficients explicitly. Complete Groth16 applications remain separate work. The [weighted inner-product argument](../libraries/arguments/bulletproofs/README.md) supplies reusable rounds, and the [Monero Bulletproofs+ construction](../libraries/constructions/monero/bulletproofs_plus/README.md) implements 64-bit aggregated range proofs for 1..16 commitments; pinned upstream controls compare exact bytes at every count. Full transaction integration, batch verification and security proofs remain outside this library. The [KZG library](../libraries/commitments/kzg/README.md) provides checked evaluation domains, evaluations and opening equations. The [Ethereum EIP-4844 construction](../libraries/constructions/ethereum/eip4844/README.md) supplies commitment, proof, challenge, batch-verification and precompile functions. Its constructions reproduce c-kzg-4844's explicit challenge hash inputs, tagged `FSBLOBVERIFY_V1_` and `RCKZGBATCH___V1_`, and all 262 c-kzg-4844 v2.1.8 vectors and 57 derived reference cases agree; no Fiat–Shamir security theorem covers these constructions. The source bound permits 1..64 blobs; admissible execution also depends on the selected capacity. Bit-reversed evaluation domains use a checked two-adic constructor without pairwise root validation. Earlier measured execution limits do not characterize this implementation. Asset formats carry relation data only, so the prover receives the setup's G1 Lagrange points as an ordinary input that the library admits only with their pinned SHA-256, and the verifier key is a library constant. The batch transcript construction recomputes each blob's evaluation point and value from the statement, because a construction observes only messages and start inputs. No KZG security proof is claimed. |
| GKR source library | The [GKR library](../libraries/protocols/polynomial/gkr/README.md) verifies layered arithmetic circuits of uniform width with public stacked add and mul wiring: degree-two Sumcheck rounds per layer, a line restriction to the next layer and the input check, with an honest prover in the same unit. Lean proves [Fiat–Shamir soundness](../lean/docs/spec/fiat-shamir-security.md#the-compiled-gkr-proof-entry) of the plain verifier and of the compiled example Entry for fixed well-formed statements. Non-uniform widths, succinct or private wiring and commitments to the inputs are outside the library. |
| Sigma source library | The [Sigma library](../libraries/protocols/sigma/compositions/README.md) composes the Schnorr pattern into an AND of two discrete-logarithm statements with one shared challenge and a Chaum–Pedersen proof of one discrete logarithm at two bases; the [example project](../examples/projects/sigma/README.md) selects BLS12-381 G1 and the Merlin suite. Maintained checks cover declaration checking, native SSA/Lean replay of the Interactive Entries and construction checking of the compiled proof Entries; no maintained test runs, proves or verifies its Entries through the Host or refuses a wrong witness or proof. Formal results are in [support](../lean/docs/support.md#sigma-compositions). |
| Checked element access | `matrix.get` preserves BLS12-381 Fr, BN254 Fr, Ristretto255 scalar, KoalaBear, KoalaBear Ext8 and KoalaBear Ext4; missing in-range sparse cells yield zero. `field_array.get` accepts a dynamic index over native BLS12-381 Fr arrays; static `field_array.at` remains available. Both check bounds, including empty shapes and huge indices. The libraries also expose total `at` access under checked input conditions; finite domain indices and matrix views can discharge these bounds. |
| Relations | Bounded R1CS/AIR data import and Assets, exact [relation bindings](compiler/relations.md), a [native R1CS reduction adapter](compiler/relations.md), and an isolated [Plonky3 AIR adapter](../compiler/adapters/plonky3/README.md) checked differentially against its pinned upstream. Import does not prove upstream source adequacy. |
| Multi-table relations | [Relation bundles](spec/domains/relation-bundles.md) have independent C++ and Rust admission and evaluation of deterministic data and challenge-dependent staged predicates. Captured Bundles retain an explicit source relation ABI, table/public/channel counts, polynomial facts, interaction descriptors and simultaneous record substitution. The external [accumulator-machine adapter](../compiler/adapters/accumulator-machine/README.md) supplies a CPU/program/memory relation and independent staged LogUp/grand-product references. The [source machine proof](../common/tests/fixtures/projects/accumulator-machine/README.md) commits base, auxiliary and quotient columns, checks OOD identities and composes one FRI instance. Its selected profile has three tables with independent two-adic heights, optional presence, global all-row Boolean multisets, and signed field balance through LogUp. Native immutable table-width metadata is independent of height and presence; polynomial references admit table/carrier structure, and reached height-taking operations retain actual domain and window checks. Source admission uses these widths for absent configuration and reserves polynomial shape checks for present tables. Complete proof controls cover absent fixed/configured heights 1, 3 and beyond the active profile, exact configuration lengths, and present-table refusal. Arbitrary table counts and other interaction profiles remain library work; relation adequacy and cryptographic soundness are not established by these executions. |
| OpenVM relation comparison | The optional [OpenVM adapter](../compiler/adapters/openvm/README.md) captures five upstream AIRs for a KoalaBear RV32 branch slice. Upstream recorder/DAG/debug checks, the adapter evaluator and both native Bundle evaluators agree on selected traces and mutations. Its memory-bus test partner permits inconsistent reads, so these checks establish neither execution nor termination under VM semantics, nor authentication of initial memory. Deployed BabyBear, persistent memory, full ISA and OpenVM proof compatibility are outside this selection. Its five-table layout is outside the current three-table source argument; admitting signed field balance alone does not supply the missing execution semantics. |
| Clean export comparison | A [pinned Clean flat AIR export](../lean/integrations/clean/README.md) is compared with native finite-AIR evaluation and the KoalaBear/Ext8 ring provider on fixed honest, invalid and mutated rows. This checks native agreement on those rows; it does not prove the native decoders correct. |
| Native proofs | Separate producer/validator execution, derived or authored transcripts, structured framing and authorized setups; [proof contract](compiler/construction.md). One policy covers flat, iterated, PCS and structured programs in `zkc.program/0`. |
| Native hash-chain suites | [`hash-chain.keccak256.bls12-381.fr64be/0` and `hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0`](spec/ir/construction.md#native-hash-chain-suites): Keccak-256 chains with full-digest states, framed events, counter-expanded requests and the decoders of the Merlin suites over the same challenge fields; the octic instance has UniformIndex transitions. States are host-owned affine capabilities, as for the other suites, implemented by the field backends. Known-answer vectors from an [independent Python reference](../common/tests/support/hash_chain_reference.py), whose Keccak-f[1600] is checked against published Keccak-256 answers and Python's SHA3-256, fix the backend's states, request answers and decoded challenges. Independent replays of compiled native proofs (Schnorr, DLEQ and Sumcheck families, octic index rounds), the maintained Schnorr, Sumcheck and FRI examples and managed transcript methods prove and verify under them. No quartic-extension or base-field KoalaBear instance exists, because those fields have no random service. Lean proves the reduction of the suites' chain to the history oracle, with the byte hash as a random oracle and loss `(q + V)² / \|S\|` for `q` adversary and `V` verifier calls ([provider simulations](../lean/docs/spec/fiat-shamir-security.md#provider-simulations)). The hash-chain theorem is about the construction's byte-level chain model; that the compiled transcript handlers and the installed Keccak-256 kernels implement that model, and that the suites' decoders are modelled ones, remain obligations. |
| Programmable constructions | [Labelled messages and queries](spec/language/entries.md) select ordinary typed Local handlers, one inherited base and whole-rule overrides. Checked plans preserve state, actual payloads and loop order through participant lowering and independent runtime admission. Providers use private copyable data or an authorized managed transcript with explicit byte-labelled methods. Finite authority sets retain each query's actual service contract; unselected verifier services remain private, with checked dependencies and explicit budgets. Whole-call delegation preserves one live root, actual child-start inputs and root codec coverage across nested, repeated and empty children. Iterated Sumcheck and Schnorr exercise execution and malformed-input order; record codecs support sequential and disjoint round chunks, original-byte observations and conditional completion. |
| Structured participant comparison | The optional [source-bound native probe](../lean/bridges/structured/participant.md) compares both actual Interactive Schnorr endpoints and generic service fixtures with original-SSA and Lean replay. It checks sampled generator-multiple G1 values, independent inputs/receives, pending prefixes, canonical codec failures and provider residual state. Native cleanup and failure adapters are explicit additional observations; this is bounded evidence, not Rust refinement or arbitrary-point decoding correctness. |
| Attempts and retained work | [Persistent attempts](runtime/attempts.md) retain provider state, failed work and unpublished buffers under explicit application policy. |
| Retained storage and work | [Runtime ledgers](spec/runtime/capacity.md#retained-values-and-logical-work) count each shared immutable allocation once while retained and once when produced, with a separate logical-work ceiling charged at every kernel use. 65,536 extension-field rows committed once and opened 64 times complete within default budgets. Only row openings, accessors and length queries declare partial read extents. These are retained-payload charges, not peak-memory measurements. |
| Authored transcripts | Explicit external initialization, trial/live checks and snapshots under [authored transcript contracts](compiler/construction.md). Source libraries have bounded `Bytes`, repetition and fragment joining, private copyable SHAKE128 snapshots and shortest unsigned LEB128 index encoding, scalar/collection BLS12-381 Fr/G1/G2 and Edwards/scalar byte codecs, whole-vector big-endian BLS12-381 Fr decoding, plus raw Keccak-256 and SHA-256. A format-only construction selects native framing or one raw `Bytes` message. Pinned Spongefish Schnorr tests cover both directions, the fixed 80-byte vector and ordered decoder failures; they do not establish complete parser equivalence or soundness. Admission does not prove transcript completeness or snapshot reachability. |
| KoalaBear quartic extension | [`koala-bear.ext4-binomial3`](spec/domains/values.md#nominal-field-extensions), `F_p[X]/(X^4 - 3)`, is installed alongside the octic extension: field, vector, polynomial, round and sparse-matrix kernels, base embedding, coset evaluation, interpolation and folding on base-field subgroups, Ring and relation-bundle carriers, canonical wire frames (field 21, vector 22, matrix 28) and the word codecs. The extension-field, matrix, checked-access, numerical and pointwise kernel families run on it against degree-parametrized [integer arithmetic](../common/tests/support/binomial_reference.py), and C++, Rust admission and backend signatures agree in the contract conformance probes. Its rows are committed by the [Poseidon2 row instance](spec/domains/oracles.md#poseidon2-instances); it has no random service, transcript suite, `IndexRandomness` or Keccak row-commitment scheme; the [parameterized STARK configuration](../libraries/arguments/stark/README.md#configurations) derives quartic challenges in source from the first four coordinates of octic Merlin draws. |
| Binary fields | [`gf2-64.pentanomial-4-3-1`](spec/domains/values.md#binary-fields), `F_2[x]/(x^64 + x^4 + x^3 + x + 1)`, and its cubic extension `gf2-64.pentanomial-4-3-1.ext3-trinomial1` by `y^3 + y + 1` are installed through Plonky3 0.8.0's `Poly64` and `Poly192`: field, vector, polynomial, round and sparse-matrix kernels, the base embedding, [bit-pattern literals](spec/domains/values.md#bit-pattern-literals) for `field.constant` and `vector.constant`, canonical wire frames (field 73 and 76, vector 74 and 77, matrix 75 and 78), a hexadecimal readable form and the little-endian [bit-pattern byte codecs](spec/realization/external-constructions.md#binary-bit-patterns). Backend tests compare Plonky3 with an independent shift-and-add reference that also checks the field orders, and run every installed binary kernel to confirm that none reaches Plonky3's halving, which panics in characteristic two; a [`.zkc` Entry test](../common/tests/kernels/test_binary_fields.py) compares kernel results, constants and codecs with the same arithmetic in Python and checks compile-time refusal of two-adic domains, folding, Montgomery codecs and decimal constants above one. Relation bundles over these fields refuse in both readers, the Ring bulk kernels are not installed for them, and pointwise maps over them run. C++, Rust admission and backend signatures agree in the contract conformance probes. There is no random service, transcript suite, row-commitment scheme or Lean admission for these fields. |
| Hash-based proof primitives | KoalaBear [coordinate-word codecs](spec/realization/external-constructions.md#four-byte-coordinate-words): canonical and Montgomery little-endian encodings for `koala-bear` and its installed extensions, with whole-element vector decoders that reject words at or above the modulus. The [word-codec kernel test](../common/tests/kernels/test_field_words.py) compares them with integer arithmetic through `.zkc` Entries; backend tests compare Montgomery words with Plonky3 0.8.0's serializer. [Bit-reversal permutations](spec/domains/vectors.md) of elements and of whole rows of flat row-major tables are installed for every field family and [checked through `.zkc` Entries](../common/tests/kernels/test_bit_reversal.py) against independent digit reversal. The batched [width-16 Poseidon2 permutation](spec/domains/permutations.md) over KoalaBear uses Plonky3 0.8.0's default parameters with external-work accounting; backend tests compare it with the upstream known answer, p3-poseidon2's generic round functions and an integer implementation, and a [`.zkc` test](../common/tests/kernels/test_poseidon2.py) checks batching and refusal. [Digest-generic Merkle schemes](spec/domains/oracles.md#digest-generic-merkle-schemes) carry fixed-width digest bytes, so another leaf hash and compression is an instance rather than new carriers; the installed Poseidon2 instances over `koala-bear` rows and quartic-extension rows add `MultiOpening`: `oracle.open_many`/`oracle.check_many` with Plonky3's pruned proofs. Backend tests compare roots, rows and pruned proofs with Plonky3 0.8.0's `MerkleTreeMmcs` (and `ExtensionMmcs` for quartic rows) and with a reference model that makes every permutation call explicit, including short, long, altered, duplicate and wrong-root proofs, and a [native proof test](../common/tests/protocol/test_merkle_multi_opening.py) opens positions of both instances through a Fiat–Shamir proof. Each tree commits one table, so tables of different heights cannot share a tree; Merkle commitment, opening and checking charge no permutation work; and no operation exposes a root's digest words as field elements, so a challenger cannot absorb a root as field data. A quartic table and its flattened base table have the same root and proof, so a transcript that absorbs a root must also bind its scheme. Poseidon2 parameters are installed only for `koala-bear`, and the octic extension has no Poseidon2 row instance. |
| Parameterized STARK library | [`stark::single_table::TableArgument`](../libraries/arguments/stark/README.md#parameterized-single-table-argument) proves one present table of a relation Bundle, generic over a `Configuration` module that fixes the base and extension fields, the challenge derivation, the row-commitment instances and the data layout. Its order is trace commitment, constraint-composition challenge, quotient commitment, one out-of-domain point, evaluation claims and identity check, DEEP batching, FRI commitments and final polynomial, every query position, and then all openings: one pruned multi-opening of the trace rows, of the quotient rows and of each FRI layer, whose leaves hold both fold siblings and whose own values the verifier reconstructs. The installed configuration uses KoalaBear, the quartic extension, Poseidon2 Merkle trees, natural row order and the octic Merlin suite. [Tests](../common/tests/protocol/test_stark_library.py) prove Clean and Plonky3 AIRs, a configuration column, generated recurrences up to 256 rows and 100 queries, and two further configurations (bit-reversed rows; one FRI value per leaf), and refuse altered messages, changed statements, wrong openings and two dishonest provers; the `stark` benchmark family measures the `air` family's shapes. One table without interactions; no proof-of-work grinding; query positions are separate index draws; no soundness theorem for the composition, its sampling or its Fiat–Shamir transform. The older octic Keccak profile remains as a regression fixture and for the three-table argument. |
| Host applications | Named Entry inputs/results, joint bundles, proof jobs, explicit immutable data/prover-material reuse and generated Rust data bindings through the common Hosts; [Entry guide](runtime/entries.md). |

Setup input associations and authorized incoming PCS values follow the
[setup contract](spec/formats/messages.md#application-authorized-setups).
The protocol retains an explicit verifier-key-consuming terminal check.

Registered services cover four RNG distributions/providers. Each offers field
`draw`; the KoalaBear octic service also offers [UniformIndex](spec/runtime/services.md#uniformindex-realization)
sampling over a static power-of-two domain (`coins.index<N>()`), interactively and
as a typed [derived transcript transition](spec/ir/construction.md#uniformindex-transitions)
under its Merlin and hash-chain suites. Explicit query handlers support other positive static
u64 bounds; `zkc::sampling` supplies bounded rejection over ordinary word
providers. The installed interactive and native transcript samplers retain
their power-of-two restriction. Runtime query bounds and other service fields
remain unsupported. Tests check
prover/verifier agreement and an independent replay of the framing; they make no
uniformity or Fiat–Shamir security claim. Arbitrary user-defined
request/reply service families remain an extension. Domain and kernel contributions
require their own implementation and installation. Constant-time MSM and diagonal
contractions are supported; automatic contraction selection is an explicit
[optimizer/planner option](compiler/representation.md#checked-physical-decisions),
disabled by the Entry compile path.

Compiler admission has explicit [limits](spec/ir/limits.md), distinct from
[runtime capacity](spec/runtime/capacity.md). Larger bulk-kernel clients do
not enlarge the scalar relation adapter's envelope.

## Checking and evidence

[Preservation](compiler/verification.md) compares adjacent compiler subjects,
including actual receives, ordered action operands, region interfaces, physical
materialization and emitted program content. Rust independently admits the
executable and Host envelope. Bounded tests exercise source/IR mutations, native
execution, framing, failures, capacity and installed consumers. The
[validation map](../common/tests/native.md) records those scopes.

Optional polynomial checks cover `boolean-sum-to-point/0` and relation-pinned
`r1cs-sum-to-point/0`. [Public-coin analysis](compiler/public-coin.md) checks a
selected verifier's dependencies against bound public context, challenges and
receives. Neither establishes a Fiat–Shamir reduction or arbitrary polynomial
or protocol equivalence.

The [transcript-construction bridge](../lean/bridges/construction/README.md)
exports the checked validators of the compiled proof Entries of the Schnorr,
Sumcheck, composed Sumcheck, Sigma and GKR examples and of a guessing fixture
([format](spec/formats/constructed-participant.md)). Lean checks their transcript
construction and their [participant projection](../lean/docs/spec/participant-projection.md)
against the original exports and proves that each compiled verifier's ideal
meaning, with helper calls read by the original's helpers, is the Fiat–Shamir
transform of its original verifier; other Entries, suites and programmable
constructions have no such check. The composed Sumcheck Entry has this
transform equation only; no security theorem covers it. The compiled Sigma proof
Entries (Chaum–Pedersen, two-proof AND, Okamoto) also have fixed-statement
knowledge soundness through the registered endpoints. The
exporter repeats the native proof check before printing the validator; it is
reviewed native code, not a proved component. For Schnorr it proves
fixed-statement Fiat–Shamir knowledge soundness in the random-oracle model, under
the [named assumptions](../lean/docs/spec/fiat-shamir.md#named-assumptions). Lean also
proves [Fiat–Shamir soundness](../lean/docs/spec/fiat-shamir-security.md) of the
transform of any validator over the common participant actions with a
round-by-round soundness certificate, and of the imported Sumcheck verifier's
transform. These are instances of a theorem over typed query sites: any
validator signature with a transcript interface whose sites decode
key-dependent raw answers, possibly refusing, with an error per site. Realized
sampling laws (exact decodings, masking with refusal, low-bit masking of
KoalaBear elements, reduction modulo the BLS12-381 scalar order as in EIP-4844),
grinding-gated sites, compound sites and role separation at one key are proved
for it. No compiled verifier has typed, gated or compound query sites yet: the
native construction and the participant model draw field challenges only, so
these results apply to compiled verifiers only through the participant instance. Composed with the Sumcheck Entry's checked transform equation, this
bounds the compiled Sumcheck verifier's ideal interpretation in the random-oracle
model: a false claim is accepted with probability at most `(Q + n) / |F|` for a
fixed well-formed statement with `n` rounds (the Entry admits at most two), and
at most `(Q + 2) (1 / |F| + loss)` for adaptively chosen well-formed statements,
`loss` being the challenge decoding's excess, when the initial
transcript determines the statement. The adaptive premise is discharged by one
typed public-value binding event whose row holds the table values as a vector,
the claim as a scalar and the round count as a count. The typed public-value
binding establishes statement determination only; that the native transcript
absorbs the encoded rows, in order, remains assumed.
For the GKR Entry, Lean proves that the
admitted original validator, through its generated normal form (an instance of
the participant normalizer's soundness theorem,
`Zkc.Source.Structured.NormalForm.normalize_sound`, checked by kernel
evaluation), is the plain GKR verifier on well-formed statements within the Entry's maxima, and bounds the
compiled verifier's acceptance of claimed outputs other than the circuit's for a
fixed statement through the composed check's transform of that original, with a
charge per phase: against a weighted adversary budget whose oracle keys are
charged their challenge site's error, and by
`(Q + width + layers (2 width + 1)) max 2 width / |F|` against `Q` queries.
The [executable bridge](../lean/bridges/executable/README.md) reads the validators
of the `zkc.program/0` candidates of the Schnorr and Sumcheck Entries and of a
deferred-rounds fixture, which the runtime admits. Lean checks each against its constructed validator with a
[lowering rule](../lean/docs/spec/executable.md) whose meaning covers proof
framing, decoding failures, instruction budgets, loops, local calls with frames,
helper calls and transcript custody. The rule compares instructions up to checked
normalization of pure total calculations, so a schedule that computes values
before their first consumer, as the compiler's calculation batching does, is
accepted when its anchors and their operand terms agree with the export's. The
compiled Schnorr and Sumcheck programs equal their exports; the two-round
deferred-rounds fixture, whose program defers the first round's product past
the second draw, is accepted through normalization, and compiled with `--no-calculation-batching`, which
computes values where the source defines them, by equality. That fixture's
theorems stop at the constructed validator, since the participant projection
rule is not applied to it. For Sumcheck the program's helper functions are proved to
implement the source's checked helpers: the empty point and the point extension
by the general helper rule, whose soundness is proved once, and the terminal
check, whose body iterates and is outside the rule's recipes, by a proof of its
own. Honest-prover completeness of the executable holds for every round count up
to the Entry's static maximum, at every budget of at least `68 + 59 · rounds`
instructions, a charge derived from the program's reading, which at two rounds
is the runtime's acceptance threshold; the proofs are the Sumcheck family's and
do not depend on the value of the maximum. A current limitation: the compiler
accepts a Sumcheck Entry with any static maximum, but the library's terminal
check bounds the point at 64 coordinates, so honest proofs of 64 or more rounds
are rejected, and the executable theorems require a maximum below 64.
The security bounds
transfer to provers of proof bytes through the general construction, projection
and lowering rules, with no equation specific to an Entry about the compiled
program: Schnorr knowledge soundness for a fixed statement, and Sumcheck soundness
for fixed and adaptively chosen statements, the latter from the typed
public-value binding of the transcript model, one event whose row holds the
table values as a vector, the claim as a scalar and the round count as a count,
and determines the statement. The typed public-value binding establishes
statement determination only; that the native transcript absorbs the encoded
rows of the invocation root, in order, remains assumed. The bridge compares the
runtime's stops and observations with that meaning, at every budget up to the
acceptance threshold and on mutated proofs, and checks that the runtime executes
the program a verification receipt names, with the acceptance output and public
inputs of the Lean statement. The runtime's execution, kernels and codec, the
program renderer and the structured exporter remain trusted; the runtime refuses
some inputs the meaning classifies differently, listed in
[support](../lean/docs/support.md).

The [construction obligations](spec/ir/construction-obligations.md) specify
query identities, construction classes, realized laws, observation classes with
certified openings, blocks, gates, cryptographic effects, binding, provider and
explicit-input obligations, equivalence notions and the model of claims. The
native construction implements the profile that absorbs every message, over the
installed Merlin, spongefish and hash-chain suites, and its request operands are `index`
bounds defined by `data.index` constants, which meets operand provenance
statically. Programmable handlers may ignore values, and nothing checks the
omission classes for them. No gate, block request, declared role of hash calls,
challenge-input coverage, configuration provenance check or interaction-pattern
digest is implemented, and the salt kind is not admitted natively. Lean states
formal readings of the obligations, refutes each with a model counterexample
([support](../lean/docs/support.md#construction-obligation-counterexamples)),
fixes the type of provider simulations and proves one for the hash-chain
suites' byte-level chain model (the duplex providers' simulations remain
named), and states the joint experiment of a committed opening with its
extraction checkpoint convention and proves its bound for a total straight-line
extractor; a general bound for verifiers with committed tables, read in one
random oracle with their hash calls, also applies to it. The committed opening
is a model protocol, not a compiled Entry. It also states law records with their five constructors and the gated
accepted-value decoder, per-key charges in the typed Fiat–Shamir theorems,
raw answer types by the last event and the lifting of uniform-sort certificates,
binding codecs over typed public-value binding events, and the data shape of the
interaction pattern with the reserved salt kind. The construction model carries
typed draw requests on its challenge occurrences and a typed public-value
binding event, from which the compiled and executable Sumcheck theorems derive
their statement binding; the exported query key and the native occurrence
template keep their draw spelling until the first method with operands. ArkLib's
worst-case round-by-round soundness imports into the typed engine for verifiers
with a guarded verdict, each challenge round charged its own error, and a
process-form certificate transports to a participant validator that realizes the
process form: a worst-case round-by-round proof stated in ArkLib's framework
(written for the example) bounds the compiled verifier of a guessing fixture
Entry, and the bound is attained at zero queries. The import of ArkLib's
interaction-stack soundness is outstanding adapter and instance work: the
attempted implementation met its execution prefixes in `Type 1`, its challenge
models that sample arbitrary distributions and its private Sumcheck instance,
and a restricted route through a propositional realization relation is proposed
but unchecked
([imports](../lean/docs/spec/fiat-shamir-security.md#imports-from-arklibs-round-by-round-soundness)).

The security results share one probabilistic endpoint and one composition rule.
Lean states keyed bad-event certificates over any key space of the lazily
sampled oracle, with an all-table resampling and a trace obligation, and its
soundness theorem is the endpoint that typed certificates and the commitment
bridge reach through transformers; charged reductions compose sub-validators
whose returned values satisfy a postcondition
([composing certificates](../lean/docs/spec/fiat-shamir-security.md#composing-certificates)).
Renamings of oracle cells transport executions, query bounds and weighted costs
between key forms, including the commitment bridge's joint keys and history
keys. [Stage relations](../lean/docs/spec/fiat-shamir-security.md#stage-relations)
compose with budget transport, bounding against the worst adversary in a
translation's support; the construction, projection and pruning equalities, the
typed theorem, provider simulations and the commitment bridge are stages. The
[joint stage](../lean/docs/spec/fiat-shamir-security.md#the-joint-stage-of-a-commitment-and-a-provider)
of a commitment and a transcript provider that share one primitive is a
contract with jointly injective namespaces, a checkpoint extraction, the
checkpoint event and an implication from the intended event, and its frame
records a provider simulation with namespace, hash-answer, state-separation and
joint-loss obligations; the contract composes, and a frame is constructed for a
provider whose primitive inputs are the joint oracle's own tagged keys. The
[hash-chain frame](../lean/docs/spec/fiat-shamir-security.md#the-hash-chain-frame)
passes the commitment's tagged row calls through to their own cells while the
chain realizes the transcript on the same byte hash; every frame obligation and
the provider's budget map are proved, and the abstract committed-opening
verifier over the Keccak-256 hash chain is bounded by the collision and
prediction loss over the joint trace, `(q + depth + 4)² / 2^256`, plus the
commitment stage's loss at `q`. The bound is about the model's deployed reading:
its event encoding is a model encoding rather than the native frames, its index
is one digest modulo `2^depth` rather than the installed index request, and no
compiled Entry, native transcript reading or executable is connected. Statement
bindings relate policy statements to model statements, with the coverage of the
application's false statements and the rejection of unmapped statements as
separate registered obligations.
[Registered endpoints](../lean/docs/spec/fiat-shamir-security.md#endpoints-over-artifact-indexed-evidence)
state ordinary soundness, for fixed and adaptive statements, of a compiled
verifier's ideal meaning and of host validation of program bytes, and
fixed-statement knowledge soundness through a generic Sigma bridge, for evidence
indexed by a compiled Entry's artifacts and by the claim its retained contract
states. The subject driver generates each claim as the registered endpoint
applied to a subject's evidence: knowledge soundness of the compiled Schnorr
(ideal meaning and program bytes), Chaum–Pedersen, two-proof AND and Okamoto
proof Entries, and ordinary soundness of the guessing Entry (ideal meaning) and
of the Sumcheck proof Entry (ideal meaning and program bytes, fixed and adaptive
statements, every round count up to the static maximum, malformed vectors
included). A records run given the subject pipeline's evidence establishes the
assurance reports of Schnorr, Chaum–Pedersen, AND, Okamoto, the guessing Entry
and Sumcheck; the composed Sumcheck and GKR Entries
retain no target clause to state a claim at, and composed Sumcheck has no
certificate composition yet.

The [scalar Lean bridge](../lean/bridges/common/README.md) imports actual retained
PIR programs, proves open-process contracts, and applies selected ArkLib/VCVio
security results. Its named DSL target path also checks an authored relation body.
Native SSA/Lean differential tests cover the admitted finite scalar profile.
The separate [structured import](spec/formats/structured-source.md) exports
original protocol-stage units: shared helpers, protocol roots, retained contracts
and formula links, checked primitives, maps and realizations, protocol
applications and repeats, with the native catalogue rows of every domain
identity and random service they use. The native exporter and an independent C++ SSA
reference check this profile, including the 4096-instruction admission budget,
reference depth 64 and effective-site collisions. The
[structured bridge](../lean/bridges/structured/README.md) compares native SSA
evaluation, Lean replay and selected Runner cases; it does not prove native
transformations. Native affine resources, conditional entry completion and
construction-start selection are outside this profile.

Lean independently checks each structured export's metadata, signatures, helper
linking, role scopes, service provenance and computational availability, and
proves its process equations on the shared Region carrier: each generated
participant normal form is an instance of one soundness theorem of a verified
normalizer (`Zkc.Source.Structured.NormalForm.normalize_sound`), checked by
kernel evaluation. It resolves every
domain identity against the exported catalogue rows and admits the rows that
agree with its environment: the BLS12-381 scalar field, its pairing groups and
its random service, at field, vector, G1 and service types. Other installed
identities export their rows and are refused by Lean admission.
[Formal support](../lean/docs/support.md) states exact experiments and premises,
including: the Interactive Schnorr verifier contracts, an honest prover derived
from the checked source's sends and the Sigma properties; the Schnorr AND and
Chaum–Pedersen compositions with their Sigma properties and fixed-statement
random-oracle knowledge soundness of the Fiat–Shamir transforms of their
imported interactive verifiers (not of the compiled proof Entries); two inlining pairs checked
against actual prepared exports; `n / |F|` Sumcheck bounds on the actual
admitted roots under a uniform query service; and honest-prover completeness of
both imported Sumcheck pairs with the prover's per-round fold invariant. No general
availability-soundness or native execution-correspondence theorem is claimed.
Full DSL/compiler/runtime correspondence, production arithmetic/sampling,
backend correctness and complete protocol security remain open.
[Assurance](assurance.md) distinguishes these evidence boundaries.

## Scope of the supported package

Default build and execution checks cover C++/Rust. Formal builds and checks are
optional standalone work; LLZK remains a generic optional relation adapter.
Use [development](development/README.md) and the [test guide](../common/tests/README.md)
for current commands. [Roadmap](roadmap.md) records further work.

The optional [Clean adapter](../compiler/adapters/clean/README.md) exports finite
inductive-table constraints, explicit public boundaries, indexed immutable
lookups and signed channels from one flat component to native Bundles. The
[Fibonacci and FemtoCairo examples](../examples/projects/README.md) execute through
ordinary STARK libraries. LogUp admits signed field balance as well as Boolean
multisets; grand product remains restricted to the latter. Native controls and
complete proof runs cover this path; the existing Lean flat-fragment theorem
does not cover the native adapter. Full Clean ensembles remain outside it.

## Compiler tooling

Root build profiles, shared CLI/SDK requests, structured diagnostics, optional
phase/pass/decision reports, LLVM time traces, feature-gated runtime counts,
manifest consumer tests and bounded captured-input compilation reuse are
implemented. The optional MLIR LSP uses the upstream server with installed zkc
dialects. Source editing, persistent query caching and automatic policy search
remain separate work. See [tooling](compiler/tooling.md) for supported boundaries.
