# Roadmap

Development extends one supported model: `.zkc` Language → Protocol IR →
`zkc.program/0` → VM programs, the Rust interpreter and Entry/proof/joint Hosts.
[Status](status.md) records existing support; this page orders further work.

## Strengthen the maintained path

Keep Schnorr and Sumcheck libraries, their source Entries, relation data import
and installed C++/Rust consumers representative of the public workflow. New
capabilities should use the common semantic profiles and checked target contracts, with explicit
formation, transformation, admission, execution and failure contracts.

Preserve general algebra, relation Assets, native kernels, structured messages,
resource custody, iteration, completion and attempts. Broader source syntax and
new protocol libraries are additions to this model. Independently formalized
Lean models and native consumers share explicit interfaces; common terminology
does not itself establish source-to-execution correspondence.

## Make numerical realization explicit

Build on the checked physical plan, which retains original computation bodies and
selected scoped realizations together, with checked binding lifetimes in the
physical schedule. Extend the checked SCF loop schedule with target-specific
numerical kernels, preserving domains, indexing, reductions and failure obligations.
Compare numerical variants through the same checked transaction and installed
operation contracts. Establish field representations,
layouts, aliasing and work bounds before adding generated arithmetic. VM control
retains participant order and authority.

Validate realization refinements across representative operations and protocol
families. Keep alternate interpreters, JIT and AOT dependent on evidence and the
same execution contract; the VM separation itself makes no performance claim.

## Deliver the IR architecture in dependency order

The [IR ownership design](compiler/ir-design.md) defines the target boundaries.
The maintained path already has checked Tensor/Linalg computation, separate IR
interpretation and transformation production, and one Computation owner. The
foundation uses one typed executable invocation, structured native types and
attributes, explicit stage admission, shared pipeline builders and owner-scoped
analyses. Native installation and physical selection use complete native
signatures; byte conversion belongs to publication and interchange. The
[native MLIR foundation](spec/ir/native-foundation.md) specifies these boundaries.
Further optimization must preserve the admitted profile and independently
checked source/candidate relation.

Each unit below is one substantial pull request: research alternatives and
consumers, specify concrete semantics/refusals, implement the complete unit,
independently review it, validate and fix it, then revise the next unit against
what actually landed. The completion criteria below belong inside those units.

| Unit | Current position and required outcome |
|---|---|
| Catalog and MLIR execution foundation | Landed native baseline: typed invocation, structured types, shared catalog, explicit admission and one default route. Preserve its contract and invalidation controls |
| Virtual batching and FRI | Landed supported native profile: shared interaction analyses, checked dynamic virtual query blocks and one logical FRI component used by maintained STARK callers. Formal realization closure remains separate |
| STARK reduction and checked construction | Next PR: settle the caller's DEEP degree claim, expose source proof policy through the existing construction path, complete the selected native binding checks and exercise the quartic Keccak STARK client |
| Represented execution | Next substantial PR: canonical logical collection ownership across Data/Algebra, represented modular arithmetic and codec semantics, private buffer contracts and admitted Arith/Vector/Bufferization lowering |
| Constraints and semantic consumers | Following substantial PR: complete assignment-level redesign and consumer migration, with Clean ensembles and LLZK as acceptance clients, exact statement/witness maps, lookup/multiset and chronological-memory meaning, and actual commitment/terminal connections |

The remaining units each contain their research, contract changes, implementation,
review and final validation. Do not reopen the completed foundation or shared FRI
as separate implementation projects. Preserve their restrictions: current dynamic
discovery is answer-free, multi-holder routing is unsupported, and FRI refuses
zero rounds. New profiles need their own specified observations and consumers.

Extend compiler analyses with concrete consumers inside those units. The
interaction view and participant-relative scalar observations now serve oracle
scheduling, capacity and source association. Further successful-return summaries
need an explicit relation for Local results and stops; induction bounds need
zero-trip and backedge rules; adaptive oracle queries need an observation relation
that permits their answer dependencies. Add these with independent negative
controls. Do not infer them from ordinary provenance or register generic control
interfaces before their participant semantics are defined. Current
successful-point bounds remain a query API, not a license for batching to erase
source guards.

The STARK reduction's degree claim remains distinct from FRI's bound. The
parameterized single-table caller uses a fresh linear degree adjustment and
explicit coverage of otherwise unread committed witness columns. Its
[reduction contract](spec/domains/stark.md) fixes the transcript order and the
verifier's adjusted query equation. A degree-n source polynomial can produce a
degree-(n-1) opening quotient; the adjustment addresses that exact-membership
boundary without changing generic FRI's absolute strict-degree meaning.
Proximity, extraction and complete composition security remain separate obligations. The octic and
bundle callers already have explicit adjustments, with separate aggregate-bound
limitations described in the [STARK library](../libraries/arguments/stark/README.md).

### Next STARK and construction unit

Proceed through these phases inside one PR:

1. **Reduction and statement.** Fix the exact column, quotient and DEEP degree
   bounds, public/witness layouts and challenge order before changing code.
   Use a fresh caller-owned linear adjustment `(1 + delta * X)` on the DEEP
   word and on its verifier-side query equation. Keep generic FRI's absolute
   strict-degree contract. Check the full ordered term inventory, including
   the treatment of committed but unread columns. Record coefficient,
   cancellation and sampling assumptions. Separate exact polynomial membership,
   proximity and the complete reduction's security statement; execution controls
   do not prove the latter. Multiplication by `X` alone can wrap a high-degree
   interpolant modulo the evaluation domain, and changing only a terminal bound
   loses the strict boundary during binary folding.
2. **Source policy and actual construction.** Carry the selected transcript,
   block/gate parameters and witness framing from the frontend checked program
   through construction and independent record consumption. Reuse the installed
   block/grinding wire and kernels. Source proof declarations now select gates through that path, with scalar,
   block, zero-bit and positive-gate quartic Keccak STARK controls. The structured
   verifier analysis and complete selected binding judgments remain in this unit.
   Select gates by authored query labels and labelled application paths, with
   independent source-to-selected-occurrence comparison. Separate FRI's common
   folding/opening implementation from query acquisition: the flagship selects
   one explicit product request after the terminal coefficients. Existing scalar
   suites retain an explicit scalar sampling policy, not an implicit fallback;
   blocks require their own installed capability and change transcript bytes.
   Inspect actual binding, omission and authentication-before-use conditions for
   supported ordinary, programmable and explicit-input profiles. Unsupported
   interpretations must refuse the requested judgment, not inherit a native
   hash-chain security claim. Publish the closed supported handler/encoding
   forms; data dependence by itself does not establish cryptographic binding.
3. **Selected complete client.** Use KoalaBear with its quartic extension,
   quartic Keccak rows and the selected direct quartic transcript. Preserve
   field/basis, setup, row order, request length and actual final acceptance.
   Keep the existing shared FRI realization matrix distinct from a complete
   STARK realization claim. Exercise both gated and ungated source deployments.
4. **Analysis and cost.** Measure the unchanged 256-row/100-query client and
   growth in queries, nested repeats and reused helpers. Its native execution
   now passes; this does not enlarge the separate public-coin report profile.
   That profile currently selects at most 64 scalar draw/index sites on an
   expanded entry, excludes block draws and refuses verifier-local calls.
   Define the required structured judgment before extending it; reuse shared
   interaction extraction with bounded summaries, checked substitutions and
   invalidation. Do not solve a refusal by merely raising limits. Optimize
   measured work inside the existing checked path; do not make represented execution or AOT
   prerequisites for this PR.
5. **Review and completion.** Include degree-boundary and cancellation controls,
   wrong policy/root/setup, altered witness and codec slots, zero difficulty,
   search exhaustion, request-window overlap and failed terminal checks. Run
   the affected complete native matrix on the final base; report formal
   interpretation and security closure independently. Remove superseded forms
   and revise represented execution from the measured result.

### Constraint redesign and complete migration

The third remaining PR redesigns the whole assignment/constraint boundary. It
is not an adapter-only addition to the present AIR representation. Clean and
LLZK exercise complementary requirements; neither becomes the protocol owner.

- **One meaning.** Relation retains declaration, asset and public-interface
  identity. Constraint owns predicates over arbitrary assignments, including
  row scopes, rotations, exact multiplicity and chronological memory. Keep
  witness generation as a separate fallible computation: success is neither the
  definition nor a proof of the adversarial relation.
- **Complete Clean profile.** Specify and support an executable ensemble profile
  with its tables, public inputs, fixed cells, hints, witness blocks, dynamic
  sizing/padding rules, interactions and public verifier contributions. Preserve
  balance bounds and the distinction between assignment validity and the source
  theorem's assumptions/specification. Do not silently flatten an ensemble into
  independent tables or treat arbitrary Lean propositions as executable IR.
- **Complete LLZK profile.** Reevaluate the current upstream dialect and backend
  at implementation time, including the augmented computation and complete wire
  map. Preserve mutable object identity, reads, assignments and public outputs.
  Decide external-dialect versus boundary-adapter ownership using exact semantic
  correspondence and the current toolchain; the old LLVM pin is not the decision.
- **Adequacy and connections.** Record public, fixed, witness and auxiliary
  projections explicitly. Check the reduced predicate on arbitrary auxiliary
  assignments and connect it to the actual commitments and final acceptance.
  Compare lookup reductions, including characteristic, denominator, multiplicity
  and transcript conditions; memory additionally retains address, time,
  initialization and final state.
- **Single cutover.** Migrate every existing relation consumer, emitter, codec,
  fixture and native adapter to the selected owner. Remove replaced assignment
  implementations and compatibility readers in this PR. Native completion and
  independently maintained formal adequacy remain distinct outcomes.

Freeze supported/refused profiles before implementation and test both external
clients end to end within them. This is complete support of explicit executable
profiles, not a promise to compile every upstream language or proposition.
CirC remains a comparison point, not an extra mandatory integration.

The first PR publishes logical term and statement/witness maps; represented
execution preserves them; Constraint reads them before physical lowering.
Consequently this delivery order does not require rebuilding relations from
buffers or bytes. If representation work needs assignment meaning, it must
preserve the existing logical subject instead of inventing a temporary owner.

### Shared interfaces before implementation

Publish each cross-layer interface against landed sources, including its
accepted profile, actual input/output subjects, observations, schema changes
and remaining assumptions. The [foundation interface inventory](spec/formats/foundation-interfaces.md)
specifies structured source, program bytes, realization records, application
maps, outcomes and budgets, and the catalog. Independent consumers adapt from
these repository specifications, not another session's unlanded implementation:

| Connection | Compiler deliverable | Formal consumer |
|---|---|---|
| Written source to admitted original IR | Syntax retained before desugaring, elaboration associations and independent source/interface comparison | Named frontend trust boundary for the paper; stronger source correspondence remains separate |
| Ideal oracle to realized protocol | Original oracle program, deterministic realization record and actual realized candidate | Realization bridge and scheme-specific security interpretation |
| Emitted bytes to executable meaning | Exact byte grammar, canonical rules, complete layouts and malformed/canonical fixtures | Byte-to-Lean rendering is a named trust boundary; a formal byte reader is not a delivery gate |

The [contract register](spec/contracts.md) owns this inventory and its current
producer/consumer gaps. Frontend owns source spelling, companions and source-AST
contracts; the checked program belongs to frontend, its lowering and the catalog
to IR. The foundation migration is complete. Subsequent shared changes use the
landed interfaces and publish their producer/consumer changes together; the
temporary foundation-wide ownership freeze is over. Lean remains the sole
writer of `lean/`. These native units neither patch Lean nor use its pipeline
as a landing gate. Its independent interpretation does not delay native work
or become established by catalog generation.

Restricted logical aggregates retain typed field paths, actual handles and role
components for claim records. They require explicit native frontend/IR admission;
ordinary native data aggregates and codecs continue to exclude oracle handles.
Companion and declaration-interface proposals must reuse the existing request,
subject, declaration and assurance pipeline rather than create a parallel one.

Track native implementation completion and formal closure separately. Record
whether a link is independently interpreted, checked by regeneration, proved,
or still trusted. Regeneration checks consistency with a producer; it does not
independently establish that producer's semantics. Do not report the complete
source-to-bytes claim while one of its required formal links remains open.

Runtime owns target installation, checked compound runtime realization and
native Merkle/grinding kernels. Reuse the landed CPU installation and block/gate
implementation. The compiler owns request layout, emitted behavior
and propagation of the selected installation through its own choices and
validation. Common target ingress stays before native resident handles; no
separately published typed-program view is required. Generated shared files
are regenerated from the agreed current schema.

### Preserve the landed foundation

Build each unit from landed main, not another session's worktree. Keep ordinary,
numerical, oracle and repeated-helper clients in the regression boundary. Check
typed invocation, structural admission and native execution separately, including
resource operations and target restrictions. Generated signatures and the
catalog's formal-consumer data do not prove mathematical laws.

Retain checked u64 index semantics, including zero-size, overflow, bounds and
pairing order. Preserve the absence of executable wrappers, inner string-schema
verification and fallback readers. Re-admit changed subjects rather than
extending an old completion receipt to a new program.

Preserve the foundation's direct/textual/production parity as later units extend
it. Its regression boundaries include fresh-context direct APIs, textual and
nested pipelines, nondefault policy/target parity, dormant invalid bodies,
sibling-callee mutation and concurrent pass execution. No cached fact or profile
marker substitutes for re-admission after mutation. New consumers must use the
same stage builders and declare the analyses and source associations they
preserve.

The initial application-map edge is unsimplified preparation. Downstream work
must read its actual source/candidate associations before adding transformation
rules. Folding/CSE, polynomial realization and construction-start insertion need
bounded independent derivations for introduced instructions and eliminated or
reused results; they cannot be accepted by assigning auxiliary labels. Extend
whole-value associations to component paths or checked frontend written links
only with the owning source/layout contract and corresponding mutation controls.
The catalog's fixed consumer profile similarly gains new operations through
explicit owner-reviewed signature and parameter data plus an independent
interpretation; contribution registration does not enroll operations by itself.

Widen MLIR transformation features only after those boundaries exist. Use local
patterns and conversion legality where they describe a real transformation.
Dataflow, finer effects, Transform/PDL and bufferization enter with a concrete
consumer and a checked semantic contract, not an API adoption quota. Header/file
splits follow semantic owners during these cuts rather than creating new library
targets without a dependency need.

### Block requests and gating

Construction owns the generated request layout and witness slot; runtime owns
the kernel and bounded search; Lean owns the primitive-query interpretation.
The [native index-block contract](spec/formats/native-index-block.md) fixes
metadata order, final request length, nonoverlapping gate/index windows, occurrence
coordinates, zero-difficulty elision, verifier rejection successor and accepted
search/replay work. Native construction and CPU consumers implement that contract
with independent byte controls. Source proof configuration and Lean interpretation
remain separate work. Scalar index support grants no implicit block/gated capability.

The common acceptance configuration is KoalaBear with its quartic extension
and Keccak Merkle rows. Runtime supplies that exact row instance. Lean must
interpret its installed vocabulary and register the realization stage/link
before an assurance report can claim the full path. All sessions use the same
frontend FRI/STARK source and report their remaining obligations separately.

### Completion criteria for the ordered units

**Oracle realization.** Settle shape provenance, answer-use dominance, batching
barriers, dynamic occurrence identity, setup binding and the observation
boundary before emission. Initial shapes are static or initially bound by the
statement/configuration under a maximum; challenge-adaptive shapes require a
separate extension. Keep logical queries, unique openings, semantic attempts,
primitive-oracle queries, digest evaluations and permutation work distinct.
Whole-table transport establishes neither oracle privacy nor extraction.
Retain one shared anchor interpretation across all clauses and residuals, with
holder data, receiver representations and role observations kept distinct.
Native target transport must fix the public root/shape bindings and witness
scope explicitly; a fresh witness per clause or a renamed relation does not
preserve the original logical predicate.
Bind acceptance to the actual authenticated root, setup, domain, query and answer;
an obligation inventory or ignored verification result is insufficient. Keep the
present proof-profile refusals until the relevant consumer interprets that link.

The foundation preserves source/application associations and existing occurrence
encodings. Shared interaction analyses now derive source structure for scheduling,
capacity and source associations. Keep multiplicity, dependencies, role views
and dynamic coordinates distinct. Recheck the candidate schedule rather than
persisting another authored protocol graph.
Physical opening reuse does not remove logical queries, charges or failures.

Fix the exact statement/root/witness encodings, frame order, occurrence/domain
binding, final request length, gate/index coordinates and failure/successor
state in the owning construction contracts now. The later Codec unit migrates
those meanings rather than inventing another encoding. Check byte-exact
multi-block, failed/successful-witness and zero-difficulty cases jointly with
runtime/formal consumers. A prefix preview must bind the final request length.
Provide the source export, byte fixtures and realization subjects required by
the formal connections above, with their actual remaining assumptions.

Application-correspondence proposals retain actual callee boundaries, role maps,
source paths and argument/result mappings across expansion and projection.
Offsets/spans are checked compression, not assumed to fit every application.
Interned identities keep exact readback and unchanged transcript bytes. Proposals
remain outside semantic bodies, bound to the original and actual candidate, and
require independent validation before they support a correspondence claim.

**MLIR execution foundation.** Preserve typed callable bindings, one ordered
invocation, structural types and explicit admission. Compiler
analyses inspect actual SSA and control, with dependency-aware invalidation at
the enclosing isolated scope. The catalog describes typed contracts; selected
consumer profiles and independent meanings remain distinct responsibilities.
Review profile membership, unsupported operations and payload schemas before
extending a consumer. Publish each schema change before its producer/reader
migration. Preserve the single typed route without executable wrappers or inner
string-schema verification as represented execution develops.

**STARK support.** Retain the shared FRI commit/query component and its explicit
first-layer association and final-degree conditions. Authentication, query
alignment, transcript order and DEEP binding must survive each extension;
realization layouts stay explicit. Do not restore specialized FRI packets or
treat a successful FRI check as the caller's complete degree argument.
The formal flagship target is the realized compiled verifier;
native compilation still reaches bytes and execution. Fiat–Shamir and commitment
realization require their full independent Lean checks. Neither formal STARK
operation lowering nor a formal byte reader is a gate for these IR units.

Settle AIR asset ownership before introducing encodings;
consume one definition throughout the later Constraint migration. Preserve
extension basis, row/leaf ordering, public layout, block draws and actual
acceptance dependence. Exercise one oracle-level argument under ideal,
Poseidon2-Merkle and Keccak-Merkle realizations with different supported leaf
layouts without changing protocol logic. Include virtual dependencies,
repeated queries, explicit zero-round refusal, wrong-root/setup failures, use
before authentication and the declared stop observation. Existing kernels are
dependencies, not duplicate compiler implementations.

**Represented execution.** Start with a migration inventory: current owner,
final owner, types/operations/schemas, source/formal/runtime consumers and
replaced forms to delete. Separate genuine mathematical distinctions from
collection representation duplicates. Cover exact field and quotient-ring
work, a resident group/MSM path, value-aware conversions and an opaque
alternative. Preserve modulus, ranges, integer lifts, widths, bases and exact
wire semantics. Fix private-scratch aliasing, extent, lifetime, custody,
allocation/refusal and publication before bufferization; validate stale
evidence, failed-output withholding and the declared resource relation.

Define the admitted standard-MLIR transformations, required effect/shape/index/
range interfaces, analysis invalidation and independent reader coverage before
enabling them. Check the actual default path and installed consumers, then
remove replaced collection/representation forms and unresolved conversion
placeholders. Measure conversion, preparation, checking, kernel and whole-run
costs separately. Evaluate HEIR at an exact polynomial/modular adapter with
conversion laws and measured dependency/maintenance cost.

**Constraints.** Move assignment-level AIR/R1CS definitions and consumers to
one owner while retaining Relation's statement/declaration interface. Apply
the same migration inventory and removal criterion. Connect exact lookup,
chronological memory and polynomial/commitment terminals to actual acceptance.
Check arbitrary auxiliary assignments, public/witness projections, multiplicity
wrapping, invalid masks, inactive rows, relevant zero denominators, missing
initial/final conditions and reordered accesses. State the supported direction
of encoding adequacy and remaining formal obligations. Evaluate LLZK/CirC on
complete representative assets, preserving unsupported predicates as opaque.

### Acceptance across units

- For every new operation or record, name its semantic owner, producer,
  consumers, mutation/invalidation rule and last consumer before lowering.
  Check these dependencies on the actual program, including unused inventory;
  no copied origin or approval marker substitutes for a relation.
- Classify each affected check's independence and shared assumptions. Include
  admitted controls and malformed candidates, source-relative identity/layout
  mutations, zero-trip and stopped/unreached cases. A relevant mutation after
  checking must require a fresh read. Exercise the default route and preserve
  ordinary numerical and interactive clients outside oracle/Fiat-Shamir paths.
- Before expanding generic rewrites, specify deletion, duplication, motion and
  speculation conditions, index/overflow laws and analysis invalidation. State
  the observation and budget relation for ordered refusals and residual state;
  sufficient-capacity value equality is not equal exhaustion at arbitrary caps.
- Preserve the landed CPU installation contract and review each additional
  target jointly with runtime. Restricted installations must constrain defaults,
  explicit choices, fallback, conversions, table relayout, aggregate children,
  codecs and final validation. Candidate preference never grants installation
  authority. The runtime package owns installation; the compiler integration
  belongs with that package and is rechecked by represented execution.
- Run affected checks during iteration and broad relevant native checks at
  landing. Formal owners validate their independent consumers separately; that
  work is not an IR landing gate. Record evidence scope and the revision,
  remove replaced owners and compatibility readers, then update support and
  the next unit's premises.
  Compare compile/check time, artifact size, memory and execution on matched
  workloads; passing integration tests supply no cryptographic or speedup claim.

### Extensions with separate entry conditions

Transform/PDL adoption depends on a useful admitted schedule and reader coverage;
shipping a dialect is not itself a completion criterion. Before admitting
generic CFG simplification of Host or scoped execution, preserve complete
semantic binding ports independently of removable edge transport, including
unused and repeated captures and their storage charges. Extend bounded readers
to edge-dependent SSA environments and shared continuations, then check source
occurrences, payload identities, custody, first-stop behavior and budget
boundaries independently. Correct BranchOpInterface mutation alone does not
establish that correspondence. The current execution profile deliberately
retains common source captures and its explicit scope/charge skeleton.

General privacy
analysis, adaptive oracle profiles, further folding and lattice algorithms need
named consumers. A complete Falcon verifier and AOT backend remain separate
projects. Before admitting hashing relations or internal verifiers that share
primitives with construction, define per-relation primitive dependencies,
realization primitive identities and their formal interpretation; derive them
for transparent relations and state registry assumptions for opaque ones.
Do not silently broaden the admitted relation profile.

## Establish native correspondence

Select one concrete `.zkc`/MLIR protocol, source semantics, observation boundary
and executable contract. Connect the actual emitted program and runtime behavior
to that subject, including received values, ordered effects, stopped prefixes,
resource successors and terminal decisions. Reuse independent Lean laws only
through an explicit interpretation with their hypotheses discharged.

Compiler postconditions and C++/Rust agreement remain useful regression evidence.
They do not replace a semantics for native execution or prove backend kernels.
[Preservation](compiler/verification.md) states the existing comparisons;
[assurance](assurance.md) identifies their remaining trust boundaries.

## Develop transcript assurance

Fix the statement, transcript encoding, sampling policy and adversarial experiment
before claiming Fiat–Shamir security. Native public-coin analysis checks selected
verifier dependencies; transcript construction checks observations and state
threading. Neither is a random-oracle reduction. Repeated attempts require a
separate treatment of retained provider state, failed work and adversarial trials.

The [public-coin profile](spec/ir/public-coin.md) and
[native proof contract](spec/formats/proof.md) remain the
contract owners. Changes to the proof policy must update compiler
production, Host admission and controls together. Setup authority remains at
Entry inputs and the Host registry, with explicit verifier-key-consuming PCS
checks in the protocol.

## Extend on demonstrated demand

The current service registry supports seven RNG distributions/providers. Arbitrary
user-defined request/reply families need a separately designed contract and
implementation when a concrete client requires them.

New relation frontends must preserve exact field, public layout and relation
identity across their adapter. LLZK remains a generic relation adapter in its
own toolchain. A successful import does not establish source encoding adequacy.

New kernels, larger capacity and optimizations need complete-result comparisons
at their supported sizes, including exhaustion where claimed. Performance
results state their workload, configuration and baseline. Add new protocol
applications when they motivate useful compiler work; an application-specific
compatibility requirement must be selected explicitly with its consumer.
