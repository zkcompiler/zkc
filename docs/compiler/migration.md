# Native migration

This inventory records supported behavior, remaining consumers and their removal
conditions. [Status](../status.md) owns current coverage; the [roadmap](../roadmap.md)
owns sequencing. Before replacing a capability, capture its affected ranges and
fixtures and update its row with replacement evidence.

The target is one native mathematical compiler path and one interpreter with
installed primitives. Full migration preserves supported behavior at its declared
boundary while allowing internal carriers and code organization to change.
Native foundation completion and full migration have different exit conditions.
The foundation requires general IR capabilities and their composed execution.
The inventory below retains complete protocol and external compatibility
obligations for migration; an open library row alone is not an IR gap.

## Evidence and comparison rules

Use the existing [source preservation baseline](../../tests/fixtures/preservation-baseline.json)
for its frozen source and three constructed-artifact hashes. It covers only its
named fixtures. The [contract inventory](../../compiler/test/fixtures/contracts/base-inventory.sha256)
and [conformance coverage](../../tests/fixtures/contracts/coverage.json) separately
track logical operations/types and deferred readers. None is a complete migration
ledger or a proof of current behavior.

Each row below gives representative owner/tests; the whole maintained family
behind that owner remains in scope. Before replacing it, capture its exact range,
consumer commands and affected fixtures from that revision. Do not replace the
existing conformance and test inventories with a new requirement that every file
have exactly one migration row: shared fixtures and checkers have several users.

| Comparison | Use |
|---|---|
| Exact external bytes | snarkjs/Groth16 proof coordinates, canonical serialization/calldata under controlled randomness; pinned Monero/OpenVM transcript boundary vectors |
| Exact artifact policy | Existing internal artifact reader/writer and direct-reference comparisons within the same source/identity/suite policy; retained while those consumers live |
| Normalized identity | Only the transformations defined by the existing normalized source policy; no claim that native MLIR formatting has that identity |
| Execution with correspondence | Actual per-role receives, ordered messages/draws/guards/stops, returned values, consumed resources, failed prefixes and declared observer/continuation |
| Operational contract | Admission/refusal identifiers and documented disagreements, budgets, installed APIs/components, CLI exit/report behavior and supported ranges |

Old/new internal artifacts may use different versioned roots and need not be
byte-identical. A new policy requires its own independently authored vectors and
execution comparison; it cannot silently reuse the old suite/root identity.
Historical proof lengths are measurements, not padding requirements. External
byte obligations in the first row remain exact.

Record evidence by kind: executable independent reference, proved proposition,
external implementation comparison, trusted compiler postcondition, Rust
admission, or bounded differential test. Moving to C++/Rust-only admission does
not preserve an existing Lean-checking capability. Keep the old consumer until
its replacement exists. [Formal support](../../formal/SUPPORT.md) owns exact
propositions and premises; a module's name is not an evidence transfer.

Record compilation work and execution/storage bounds alongside results. A new
budget refusal for a required previously supported client leaves its migration
open. Compare complete failure prefixes and consumed resources as well as success.
Map guards, local stops, backend failures, wire refusals and source stop reasons
before replacing an execution path. Independent external proof/wire comparisons
remain required at their stated boundary.

## Research and redesign for each capability

Each migration package starts from the behavior and semantic contract to preserve.
Select its implementation in the new architecture through the following steps:

1. Capture supported inputs/ranges, actual consumers, results, ordered effects,
   failures, resource consumption, public formats and checking obligations.
2. Assign the capability to its new owner: mathematical operation, local program,
   protocol library, backend primitive, host boundary or independent checker.
3. Compare reuse, redesign and removal of the old internal mechanisms. Prefer the
   simplest faithful design using the native IR and common interpreter. Reuse
   existing code only after checking its assumptions and dependencies.
4. Test the proposed contract against contrasting uses and a discriminating
   counterexample. Review unresolved semantic or representation choices before
   implementation; record decisions and reopening conditions with their owner.
5. Implement and move consumers with their required comparisons. Rebind checking
   evidence to the actual new artifacts, remove replaced code when its last
   consumer moves, and update this inventory and current status.

Preservation applies to required meaning, behavior and external contracts. Internal
data structures, compiler organization and carriers may change with their users.
Do not introduce a whole-protocol runtime callback or a branch on a protocol name
to make an old client pass. A required general mechanism exposed during migration
reopens the owning foundation boundary. Defer an external compatibility task only
with its consumer and remaining obligation explicitly tracked.

## Capability owners

“Open” means full native migration is not closed, even if some shared code or
native clients already work. Reuse preserves the stated contract; redesign changes
representation with an explicit comparison. No row authorizes deleting a live
consumer merely because an alternative program runs.

### Authoring, composition and analysis

| Capability and baseline boundary | Target and decision | Consumers/evidence; closure condition |
|---|---|---|
| `.pir` parsing, projects/imports/captures, names/visibility/reexports, source diagnostics and inspection; documented project/source/selector budgets | Reuse frontend checks; redesign lowering to native `protocol`/`local`/`data`. Open. | [Projects](../language/projects.md), [frontend project checks](../../compiler/test/frontend_projects.py), [preservation checks](../../compiler/test/frontend_preservation.py). Preserve supported source behavior and tooling; retain portable source export until its checking consumers move. |
| Generic domains/types/naturals, nominal identity, component requirements, constructor authority, static configuration/link/select/seal | Reuse contract/requirement infrastructure, adapt elaboration and static application. Open. | [Checked-library checks](../../compiler/test/checked_libraries.py), [project libraries](../../examples/projects/README.md), [requirement checker](../../formal/Tools/RequirementChecker.lean). Move actual certificates and independent replay together; no structural name-based authority. |
| Local products/sums/unit, map/fold, finite indices, branches, captures, affine values and zero-storage behavior | Shared `local`/`data`, native aggregate ABI; retain ordered body effects. Open. | [Local control](local-control.md), [zero-storage checks](../../compiler/test/frontend_zero_storage.py), [variants](../../compiler/test/frontend_variants.py). Preserve active-arm behavior, result custody, limits and stopped prefixes. |
| Static protocol composition, role substitution, distributed results and relation bindings | Native `protocol.apply` already expands selected clients; migrate remaining source callers. Open. | [Native composition](../spec/profiles/compiler/protocol-composition.md), [relation composition](relation-composition.md). Preserve actual callee/role/port maps and terminal obligations. |
| Input-selected root families, compact symbolic counts and failed ingress | Redesign older family entry metadata through native count/entry contracts; reuse bounded controls. Open. | [Iteration checks](../../tests/execution/test_iteration.py), [input families](../../tests/fixtures/input-families/), [Lean iteration](../../formal/Tools/Iteration.lean). Native loops already accept logical counts; family selection/ingress parity and independent-host count requirements still need comparison. |
| Public-coin verifier views and polynomial requirement checking | Retain current native analyses and source/candidate binding. Already native at their stated scope. | [Verifier views](public-coin.md), [public-coin controls](../../compiler/test/public_coin.py), [native mathematics](structured-mathematics.md). Recheck after construction changes; neither report is an affine observation analyzer or security theorem. |
| Execution-bound claims, oracle provenance and caller requirements | Retain `claim` and analysis owners; adapt subject/call/guard correspondence. Open. | [Claim composition](claim-composition.md), [claim checks](../../compiler/test/execution_bound_claims.py), [oracle provenance](../../compiler/test/oracle_provenance.py). Preserve verifier-owned requirements and explicit body-law/authentication premises. |
| Checked interpolation, linear contraction and factor/preparation transformations | Reuse mathematical laws; implement/check applicable rewrites on native operands and selected physical realization. Open. | [Linear contractions](../../compiler/test/linear_contractions.py), [table simplification](../../compiler/test/table_simplification.py), [factor model](../../formal/Zkc/Compiler/FactorOptimization.lean). Preserve supported transforms, refusals and measurement baselines; do not relabel executable functionality as reference-only. |

### Execution, proof construction and resources

| Capability and baseline boundary | Target and decision | Consumers/evidence; closure condition |
|---|---|---|
| Separate role execution, generic interpreter, installed operation effects, retained values and nested frame cleanup | Reuse `Runner`, registries and native backends. Native subset exists; full consumer migration open. | [Interactive execution](interactive-execution.md), [runner controls](../../crates/zkc-tools/tests/run.rs), [generated native example consumers](../../crates/zkc-tools/examples/). Preserve local work, aliasing, actual received values, stop reasons and cleanup order. |
| Joint native scheduling and nested compact iteration | Keep as one interactive/test host alongside proof deployment. Already native. | [Structured iteration](../spec/profiles/compiler/structured-iteration.md), [joint checks](../../compiler/test/native_joint.py). Keep per-role counts, coverage, mismatch and zero-trip behavior; binary proof policy must not narrow arbitrary-role IR. |
| Independent proof artifacts, entry admission, framing, canonical decoding, complete consumption and atomic publication | Redesign source-dependent admission/construction; reuse generic host components. Flat, iterated and committed native slices are implemented in [native proofs](native-proofs.md). Native attempts, selected [structured messages](structured-proofs.md) and [composed numeric state](composed-state.md) are implemented. Runtime-count [nested data](nested-data.md) and selected [authored transcripts](authored-transcripts.md) now use the native boundary; [conditional entry completion](entry-completion.md) supports early participant abandonment. | [Artifact execution](artifact-execution.md), [host tests](../../crates/zkc-tools/tests/artifact_host.py), [proof exchange](../../tests/artifact/test_artifact_proof_exchange.py). The pinned-deployment adapter admits proof policies `zkc.native-proof-policy/1`–`/4` and checks input-constructor coverage. Move remaining resource/control and consumer cases before retiring the old adapter. |
| Exact/normalized identities, selectors/origins, source closure, generic configuration selection and result mappings | Native exact-source policy first; native normalized identity and general selector/provenance support later. Open. | [Identity contract](../runtime/artifact-identity.md), [identity tests](../../crates/zkc-tools/tests/artifact_identity.py), [construction checks](../../compiler/test/construction.cpp). Old normalized identity remains supported through its old route until native policy and consumers are ready. |
| Merlin BLS/Ristretto/KoalaBear and Spongefish BLS constructions; scalar/index draws; public recipes; local RNG provenance | Reuse kernels, redesign construction on participant math. Native construction covers the two BLS suites and selected Ristretto/ext8 suites with typed structured observations and multiple authorized multilinear PCS setups. Existing source mapping and refusal contracts still require consumer-by-consumer migration. | [Installed artifact contracts](artifact-format.md), [construction locals](../../compiler/test/construction_locals.py), [artifact references](../../crates/zkc-tools/tests/artifact_reference.py). Preserve all existing selected-suite/mapping/refusal contracts during full migration. |
| Managed service roots/aliases, affine RNG/nonce/transcript custody, budgets and consuming failures | Reuse native registry and explicit affine locals; proof policy admits exact internal resources. Native services, compact proof loops and explicit loop-carried transcript state exist; native attempts preserve actual RNG/service providers; broader affine control remains open. | [Service contract](../spec/profiles/compiler/native-services.md), [service tests](../../compiler/test/native_services.py). No dummy source RNG in native construction; no inferred independence from distinct roots. |
| Whole-attempt buffering, resumable controllers, retry classification and persistent grinding | [Native attempts](native-attempts.md) use the common controller, including selected [authored transcript](authored-transcripts.md) trial/live-check clients. [Conditional entry completion](entry-completion.md) preserves reached effects and actual resource successors during early abandonment. | [Attempt driver](../../crates/zkc-tools/src/artifact/attempt.rs), [grinding checks](../../crates/zkc-tools/tests/grinding.rs). Preserve cumulative work/randomness, unpublished failed buffers and fatal versus retryable outcomes. |
| Host preparation, material caches, installation epoch, per-invocation binding and input limits | Reuse implementation where source-independent; isolate source adapter. Open. | [Prepared artifacts](../../crates/zkc-tools/src/artifact/prepared.rs), [artifact limits](../../crates/zkc-tools/tests/artifact_limits.py). Fresh invocation authority/state, expected setup identities and checks apply on cache hits too. |
| Multiple verifier keys, source-port/receive-site setup selection, proving material persistence and caller requirements | Shared entry/material policy with explicit native maps. The native structured profile implements multiple independently authorized setups, public VKs, pinned private PKs and per-input key maps. Prepared host/source selectors and full consumer migration remain open. | [Artifact inputs](../../crates/zkc-tools/src/artifact/inputs.rs), [requirements](../../crates/zkc-tools/src/artifact/requirements.rs), [setup selection](../../crates/zkc-tools/src/protocol/host/setups.rs). Proof-selected self-authorization or a single-key shortcut does not preserve this row. |

### Mathematics, applications and external boundaries

| Capability and baseline boundary | Target and decision | Consumers/evidence; closure condition |
|---|---|---|
| Scalar/group/vector/matrix algebra, MSM, polynomial domains/DFT/cosets, extension fields, pairing and checked inverses | Reuse installed kernels; expose native math/lowering at required domains and sizes. BLS numeric state/attempts and [BN254 QAP/MSM/GT plus KoalaBear extension/oracle clients](mathematical-composition.md) compose through the native host. Full protocol consumers remain separate migration work. | [Contract coverage](../../tests/fixtures/contracts/coverage.json), [domain artifact tests](../../tests/artifact/test_domain_artifact.py), [matrix artifact tests](../../tests/artifact/test_matrix_artifact.py). Existing bound kernels are not evidence that every native total operation lowers to them. |
| Public and committed Sumcheck, repeated openings, PCS/key/index binding | Preserve typed polynomial structure and explicit reductions/terminal checks. Native public product/cubic Sumcheck and committed-original terminals execute independently. The committed profile uses the selected BLS multilinear PCS and one authorized setup; broader PCS/key selection and remaining consumers stay open. | [Polynomial recipes](../spec/profiles/compiler/polynomial-recipes.md), [committed fixture](../../crates/zkc-tools/tests/fixtures/artifact/committed-two-factor.json), [PCS project](../../examples/projects/pcs/). Original-point opening and actual received coefficients remain authoritative. |
| R1CS/AIR relation import and external LLZK adapter | Keep ingress adapters separate; native `relation` owns declared relation meaning. Open. | [Relation ingress](relation-ingress.md), [LLZK adapter/pins](../../compiler/adapters/llzk/README.md). Preserve Circom/BLS Halo2 imported relations and independent binding checks; LLZK syntax need not become a protocol language. |
| Explicit Groth16 algorithm and BN254/snarkjs interoperability at depths 2 and 16 | Native QAP/MSM/pairing plus authored proof deployment; reuse host ingress and pinned external tools. Open protocol migration; generic bulk-math, key and message capabilities belong to the foundation, while full execution and external comparisons close this row later. | [Groth16 pins](../../tests/groth16/SOURCE_PINS.json), [native tool checks](../../crates/zkc-tools/tests/groth16.rs), [Groth16 project](../../examples/projects/groth16/). Controlled randomness preserves proof coordinates/bytes and external acceptance. Public test trapdoors and key-derivation premises stay explicit. |
| Bounded R1CS machine proof, arithmetic trace and application acceptance | Native relation/reduction/proof composition; preserve verifier-owned program/input contract. Open. | [Execution proof](../../examples/protocols/execution-proof.pir), [arithmetic trace](../../examples/protocols/arithmetic-trace.pir). Current native R1CS envelope is 8 rows/128 columns/1024 nonzeros; complete old clients and limits need actual comparison. |
| Range/IPA, confidential transaction, group and view clients | Migrate explicit libraries and native group/vector operations. Open. | [Aggregated range](../../examples/protocols/aggregated-range.pir), [transaction](../../examples/protocols/confidential-transaction.pir), [project corpus](../../examples/projects/README.md). Existing Bulletproofs/IPA is preserved independently of the new BP+ requirement. |
| Two-AIR permutation proof, affine-table proof, auxiliary traces, quotients, FRI and authenticated queries | Native `relation`/`poly`/`oracle`, bulk extensions and proof codecs. Open. | [AIR clients](../../examples/protocols/air-oracle/), [AIR project](../../examples/projects/air/), [oracle checks](../../tests/kernels/). Keep actual authentication and final decision; current height-8192 element-limit failure is recorded, not a successful run. |
| Monero BP+ and OpenVM transcript boundaries, archived proof metadata, Edwards/subgroup/choice adapters | Exact primitives and selected [native authored clients](authored-transcripts.md) cover state/byte/trial/attempt boundaries. External container/Edwards adapters and remaining legacy consumers still require migration. | [External contract](../spec/realization/external-constructions.md), [fixtures/pins](../../tests/external-transcripts/README.md). Keep exact grouping/sampling, torsion/axis controls, optional data and live grinding checks. These are not full upstream provers/verifiers. |

### Checking, tables and public tooling

| Capability and baseline boundary | Target and decision | Consumers/evidence; closure condition |
|---|---|---|
| Portable source, `protocol_exec` lowering and `zkc.participants/1` explicit/generic projection | Transitional source adapter; native profiles become the common target. Open. | [Source model](source-model.md), [carrier consolidation](carrier-consolidation.md), [Lean interactive tools](../../formal/Tools/Interactive/). Keep source emission/import and old carriers until actual source/reference/candidate consumers migrate. |
| Old service participant format, executable programs and joint bundles | Remove old service adapter after last client. The mathematical path uses one `zkc.program/1` format and one `zkc.run/1` host bundle; superseded `zkc.native-participants/1`–`/3` and `zkc.native-run/*` tags are refused. | [Programs](../spec/profiles/compiler/program.md), [compiler API](../../compiler/include/zkc/Compiler/Run.h). C++, Rust, proof hosts and installed consumers move together; unsupported Lean readers retain explicit refusals. Proof-policy versions and the older source/table consumers have separate migration obligations. |
| Executable Lean source/artifact/reference readers, candidate checks and requirement replay | Native semantics/checking is a later dedicated consumer migration. Open. | [Formal support](../../formal/SUPPORT.md), [artifact tools](../../formal/Tools/Artifact/), [native refusal controls](../../tests/protocol/test_native_mathematical.py). New C++ construction checking cannot replace this evidence by relabelling it. |
| Finite field/table source, direct plans, storage layouts, ordered residuals, physical/phase/endpoint certificates | Retain mathematical models/checkers; migrate executable consumers and supported optimizations before retiring the duplicate compiler route. Open. | [Table execution](table-execution.md), [direct table controls](../../tests/execution/test_direct_tables.py), [table admission](../../formal/Tools/TableAdmission.lean), [phase checks](../../tests/admission/test_phase_admission.py), [endpoint checks](../../tests/admission/test_endpoint_admission.py). Compare F₂/F₇, capacity/refused/stopped outcomes, storage and actual candidates. |
| C++ package components, direct MLIR/API entry, contribution assembly and fresh domain installation | Retain public capability; simplify dependencies as consumers move. Open. | [Installed component map](../../tests/consumer/package-components.cmake), [extensions](../development/extensions.md), [dependency tests](../../compiler/test/component_dependencies.py). Changed component/API boundaries require installed consumers, including optional/shared linkage when affected. |
| CLI commands/binaries, diagnostics, developer queries, report/exit behavior and optional integrations | Adapt tools to shared compiler/host APIs, then switch defaults. Open. | [Test scopes](../../tests/README.md), [harness](../../tests/harness/), [compiler CLI](../../compiler/lib/Driver/Compiler.cpp). Keep relation/snarkjs/artifact tools and optional LLZK/ArkLib checks in the inventory; commands may change only with documented replacements. |

Documented reader disagreements and capacity refusals remain explicit through
migration; see [checking coverage](../status.md#3-what-is-checked-and-how). Do not
turn host capacity failure into malformed-source refusal, or hide newly lower
limits behind unchanged success fixtures. A required old client that exceeds a
new bound keeps its row open. Independent models need not execute at production
sizes to retain their stated finite propositions.

## Additional capabilities and reuse

The [foundation corpus](ir-foundation.md#protocol-corpus-and-structural-requirements)
adds structural requirements from BP+, AIR lookup and OpenVM, checked by compiled
generic components and their compositions. New heterogeneous proof codecs and
native observation-input preservation support this scope. These are new
requirements, not claims about old-route execution. Full bounded BP+ and lookup
libraries are later protocol additions; their implementation is not required to
close the IR foundation. BP+ paper/group/parameters are selected for its library
package; OpenVM's exact pin is owned by the external contract. A full upstream
OpenVM stack remains outside this milestone.

Frontend syntax, static checking, service declarations and formal fragments
outside the supported baseline require explicit adoption decisions. Reuse parser
tests, bounded-ingress code, diagnostics and semantic examples only after checking
their contracts. Adapt selected capabilities to the native MLIR model and rebind
their evidence to the actual implementation. This inventory does not authorize
retiring a live consumer before its replacement is validated.

## Live paths and removal gates

The following source-backed inventory groups the paths still reachable in the
current implementation. It complements the capability rows above; it does not
replace their supported ranges, external comparisons or formal obligations.
Tests are consumers of a contract, but an isolated compatibility fixture alone
is not a permanent reason to retain a format.

| Path | Concrete producers/consumers | Removal or consolidation gate |
|---|---|---|
| Frontend/common source and `protocol_exec` | [Frontend lowering](../../compiler/lib/Frontend/Lowering/PIR.cpp), [protocol import](../../compiler/lib/Translation/ProtocolImport.cpp), [compilation](../../compiler/lib/Compiler/Compilation.cpp), [source libraries](../../examples/projects/) | Move required authoring, construction and checking clients to mathematical IR with their failure/identity contracts. Deleting `Source/` wholesale would also remove the shared native participant records. |
| Older explicit participants and source correspondence | [C++ source codec](../../compiler/lib/Source/Decode.cpp), [Rust decoder](../../crates/zkc-runtime/src/interactive/decode.rs), [Lean explicit reader](../../formal/Tools/Interactive/Explicit.lean) | Move the actual source/candidate checking, generic/parameterized and role-execution consumers together; new native execution alone does not replace their checking evidence. |
| Proof policies `/1`–`/4` | [Policy parser/constructor](../../compiler/lib/Compiler/NativeProof.cpp), [host admission](../../crates/zkc-tools/src/artifact/native.rs), [native corpus](../../tests/protocol/test_native_mathematical.py) | Compare admitted grammar, suite and transcript identity plus actual flat/iterated/committed/structured clients before consolidation. These policies are not the superseded participant formats. |
| Source-bound prepared artifacts, identity and selectors | [Prepared host](../../crates/zkc-tools/src/artifact/prepared.rs), [prepared controls](../../crates/zkc-tools/src/artifact/prepared/tests.rs), [identity](../../crates/zkc-tools/src/artifact/identity/), [requirements](../../crates/zkc-tools/src/artifact/requirements.rs) | Preserve cache-hit checking, installation/invocation identity, source selectors, key authority and independent checking while moving source-dependent adapters. Keep source-independent framing/custody where its contract fits. |
| Finite table execution and transformations | [Table pipeline](../../compiler/lib/Compiler/Pipelines.cpp), [runtime table executor](../../crates/zkc-runtime/src/table/), [direct table controls](../../tests/execution/test_direct_tables.py), [Lean table admission](../../formal/Tools/TableAdmission.lean) | Move the actual execution, storage/optimization and checker consumers. Retain useful mathematical models independently of retiring their old native route. |
| Installed/public defaults and host inputs | [Compiler driver](../../compiler/lib/Driver/Compiler.cpp), [runtime inputs](../runtime/inputs.md), [SDK consumers](../../tests/consumer/), [walkthrough](../getting-started.md) | Move actual public commands, reports and installed clients with documented replacements. The source-host `zkc.run/2` input array is distinct from the native `zkc.run/1` joint bundle. |
| Superseded native participant/run formats | [Carrier consolidation](carrier-consolidation.md), [retired-tag refusals](../../compiler/test/protocol_profiles.py) | Already refused; keep useful negative controls. Do not add conversion wrappers merely to preserve an obsolete spelling. |

No whole compiler route is proven unreferenced by this inventory. Cleanup stages
must inspect callers and public contracts at their working revision. Remove dead
helpers immediately when verified; move ready consumers and delete their old
implementation in the same package. A larger frontend or Lean dependency keeps
its named migration obligation open, not a permanent compatibility architecture.

## Retained host contracts

The native run bundle and older source-cut joint driver share the interpreter,
but their host contracts differ. Their codec traits are separate for this reason:

| Boundary | Native bundle/proof hosts | Older source-cut host | Migration obligation |
|---|---|---|---|
| Schedule authority | `RunHost` and native proof deployment require application-supplied exact digests. Supplied bundle admission checks structure; compiler publication separately checks source order. | Source/candidate correspondence retains source authority and checked maps. | Preserve source/Lean evidence before moving those consumers. Hashing incoming bytes is not authentication. |
| Input preparation | Bundle and proof inputs are planned before execution entropy. The bundle host uses positional typed ports. | `run-protocol` validates declarations and decodes every role before issuance; development setup still precedes key-dependent decoding. | Move source-relative declarations only with their frontend and checker consumers. No rollback claim after issuance begins. |
| Execution reporting | Complete native run/proof outcomes retain custody and cleanup. | `zkc.run-result/2` retains phase, failed-load usage, partial issuance, outputs and independent diagnostic failures. The older artifact CLI uses the prepared-artifact lifecycle. | Preserve changed-outcome controls for partial initialization and post-execution diagnostics. |
| Receive failure and authority | Native accepted receives record decode/limit stops. Setup headers select from application-authorized keys. | Older decode/delivery faults remain host failures with cancellation; each PCS receive uses its selected setup. | Preserve the per-site key policy and pin intentional outcome changes before moving a consumer. The wire traits remain separate. |
| Capacity | Effective native admission, kernel/value/work, dispatch and wire budgets are explicit. | Configurable source traversal, per-message and cumulative transport limits are reported. Original and transferred payloads are separately charged. | Keep different units and budgets distinct; equal values do not imply equal capacity boundaries. |

The common bounded input parsing, key-material admission/cache, setup predicates
and native capacity records now live under Tools' private `host` module. Their
previous artifact-local implementations were moved, not retained as fallback
paths. The older proof CLI delegates to `PreparedArtifact`; its duplicate runner
lifecycle was removed. Native and source hosts still use the same interpreter.
The source schedule and Lean checking, parameterized/composed programs, source
identity/selectors, Groth16 policy and table consumers retain their named gates.
A coherent supplied schedule permutation can change whether a second draw
precedes another role's stop; it is not a preserved source execution.

The shared admission owner now plans data operands and typed resource inputs
for artifact, native proof and bundle hosts. Every data occurrence and unissued
capability reserves its input charge before loading and issuance. Native proof
loading includes nonce/RNG inputs and the selected transcript slot. Sequential
attempts reserve one live transcript slot; execution retains cumulative attempt
work and allocation accounting. The bundle host retains one decoded pool through
preparation, then releases it after issuing role inputs. Registry keys authorized
only for receives still count toward loading.

Source declarations retain their validated schedule through execution instead of
rebuilding it. Resource issuance uses typed declarations decoded at the input
boundary. Schedule work is still charged by the execution cursor; reusing the
schedule does not turn its constructor into a charged source parser.

Shared JSON tests depend on parser-independent test data. Each consumer tests
its own parser and refusal codes. Stable `artifact-*` and `native-proof-*` error
codes used by shared helpers remain part of their existing external diagnostic
contract; the prefixes do not imply module ownership. Renaming them would change
reports and independent controls without simplifying the implementation.

The obsolete `zkc.service-participants/1` grammar, selector and API variants are
removed. Neither compiler route produces it, and no retained Lean reader accepts
it. Its direct model control now uses physical Program. Its public-runner control
executes the same service query under Program and checks the returned field value,
consumed draw state and released lease. C++ and Rust reject the retired tag.
Migrate direct callers to Program and rebuild against the updated public headers;
there is no format alias or compatibility decoder.

The source/Lean, table, identity, generic/family and per-site setup obligations
above remain open. Resource finalization stays with each host because observation,
returned-resource custody and error precedence differ. Independent checkers and
these authority boundaries are intentional; merging them is not cleanup.

## Retirement conditions

The [roadmap](../roadmap.md#foundation-completion-and-later-migration) owns the
sequence. Each migration moves the actual execution, checking and public consumers
together, then removes superseded private helpers and adapters. Independently
useful mathematical models retain their own owners.

No new native pilot closes a retirement condition on its own. No permanent
compatibility architecture is selected: each remaining adapter has the named
consumers above and leaves when those consumers have moved.

Full migration closes when retained consumers and required checking capabilities
use the native model, default commands and installed users pass their replacement
checks, and no active dependency requires a superseded internal compiler path,
carrier or adapter. Track each temporary adapter by its named users and removal
condition. Postponing a compatibility consumer leaves that condition open.
Independent external integrations and useful formal models retain explicit owners;
repository cleanup removes superseded implementation paths.
