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
The consolidation establishes the checked production Tensor/Linalg path, IR
interpretation versus Transforms production, complete pass-policy forwarding
and one Computation owner. Before oracle feature work, integrate that baseline
and the landed component-contract foundation; review the actual native,
frontend and formal interfaces together. This reconciliation is entry work,
not an additional feature pull request.

Each unit below is one substantial pull request: research alternatives and
consumers, specify concrete semantics/refusals, implement the complete unit,
independently review it, validate and fix it, then revise the next unit against
what actually landed. The completion criteria below belong inside those units.

| Unit | Required outcome |
|---|---|
| Merkle query realization | Land Protocol-owned oracle kinds/anchors, named shapes, typed records between preparation and projection, independent actual-body comparisons, immediate Merkle queries and fixed base-query blocks. The byte grammar and written-source export are already separate foundations. Hand off Lean changes to its owner and publish the shared contract register |
| Virtual batching and FRI | Complete dynamic virtual query blocks, ordered domain/failure prefixes and the same-subject FRI client. Settle index-map semantics jointly with Lean before admission. Consume runtime-owned quartic Keccak installation; keep native claim publication and its formal realization connection explicit |
| Catalog and MLIR execution foundation | Start a four-face operation-family probe before implementation. Then measure admission cost, use structured ODS signatures instead of embedded schemas, generate shared declaration faces and preserve independent semantic readers |
| STARK compiler support | Complete block-draw and gated-request emission, witness codec slot and record consumption; exercise the common frontend FRI/STARK acceptance client under selected transcript/extension fields, realizations and layouts |
| Represented execution | Canonical logical collection ownership across Data/Algebra, Residue and Codec semantics, private buffer contracts and admitted Arith/Vector/Bufferization lowering; compare native kernels and transparent schedules |
| Constraints and semantic consumers | One assignment-level owner, source-to-encoding adequacy, lookup/multiset and chronological-memory consumers, exact statement/witness maps and actual commitment/terminal connections |

### Shared interfaces before implementation

Agree each cross-layer interface against the landed sources, including its
accepted profile, actual input/output subjects, observations and remaining
assumptions. The compiler supplies concrete inputs to the independent formal
consumers; those consumers retain their existing owners:

| Connection | Compiler deliverable | Formal consumer |
|---|---|---|
| Written source to admitted meaning | Syntax retained before desugaring, elaboration associations and source/interface binding | Source correspondence checker and its soundness theorem |
| Ideal oracle to realized protocol | Original oracle program, deterministic realization record and actual realized candidate | Realization bridge and scheme-specific security interpretation |
| Emitted bytes to executable meaning | Exact byte grammar, canonical rules, complete layouts and malformed/canonical fixtures | Independent program-byte reader and its executable connection |

The [contract register](spec/contracts.md) owns this inventory and its current
producer/consumer gaps. Frontend owns source spelling, companions and source-AST
contracts; Lean is the sole writer of `lean/`. Supply changes to Lean as reviewable
patches rather than maintaining a second writer. Native Common-source removal
is paired with Lean retiring its last consumer; it must not leave a redundant
producer after the structured source route replaces it.

Restricted logical aggregates retain typed field paths, actual handles and role
components for claim records. They require shared frontend/IR/Lean admission;
ordinary native data aggregates and codecs continue to exclude oracle handles.
Companion and declaration-interface proposals must reuse the existing request,
subject, declaration and assurance pipeline rather than create a parallel one.

Track native implementation completion and formal closure separately. Record
whether a link is independently interpreted, checked by regeneration, proved,
or still trusted. Regeneration checks consistency with a producer; it does not
independently establish that producer's semantics. Do not report the complete
source-to-bytes claim while one of its required formal links remains open.

Runtime owns per-target installation, checked compound realization and native
Merkle/grinding kernels. The compiler owns request layout, emitted behavior
and propagation of the selected installation through its own choices and
validation. Common target ingress stays before native resident handles; no
separately published typed-program view is required. Generated shared files
are regenerated from the agreed current schema.

### Catalog and MLIR foundation probe

Carry one operation family through four faces before implementing the catalog
redesign: frontend spelling, typed ODS signature, execution installation
(Rust registry, VM/kernels and Lean byte table), and a Lean definition with
reusable laws. FRI index maps are the first candidate. IR owns the native
contract; Lean owns its interpretation and proofs; frontend and runtime own
their adapters. The joint decision must fix bounds, unsigned widths, zero-size
and overflow behavior, and whether a map is total under a checked domain premise.
An unchecked integer remainder or an overflow flag does not discharge that premise.

Compare a library family over existing operations with a new primitive family.
Select new primitives only where they preserve useful semantics or remove
measured duplication. Probe actual frontend emission, ODS verification, native
execution, byte interpretation and one reused Lean law on honest and invalid
inputs. Generated signatures may be shared; mathematical laws, admission and
independent readers remain separately justified. Record missing consumers before
broad generation or typed-IR migration. No global admission cache or permissive
index-arithmetic vocabulary is introduced as a shortcut.

The index decision is a dependency of virtual FRI realization; the complete
foundation migration may proceed in its own substantial PR after the probe.

### Block requests and gating

Construction owns the generated request layout and witness slot; runtime owns
the kernel and bounded search; Lean owns the primitive-query interpretation.
Settle fixed-metadata order, final request length, nonoverlapping gate/index
windows, occurrence coordinates, zero-difficulty elision, verifier rejection
successor and all speculative/replayed work before installing the operation.
Publish the agreed byte contract in the repository and test independent byte
vectors against both compiler and runtime. The current scalar-index transcript
ABI grants no implicit block/gated capability.

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

**MLIR execution foundation.** Measure admission and schema-conversion cost before
selecting the refactor. The existing context-owned type cache is not a cache of
mutable-program admission. Audit all pass/export/consumer ingress before moving
whole-program checks out of verifiers; mutation invalidates prior analyses.
Choose typed per-contract operations or one installed-call form after checking
special verification, effect/outcome rules and printer-sensitive identities.
Generate from the neutral contract catalog and preserve canonical external
spellings. This precedes represented execution so new representations do not
inherit the current string-schema adapter.

**STARK support.** Settle AIR asset ownership before introducing encodings;
consume one definition throughout the later Constraint migration. Preserve
extension basis, row/leaf ordering, public layout, block draws and actual
acceptance dependence. Exercise one oracle-level argument under ideal,
Poseidon2-Merkle and Keccak-Merkle realizations with different supported leaf
layouts without changing protocol logic. Include virtual dependencies,
repeated queries, zero rounds, wrong-root/setup failures, use before
authentication and first-stop behavior. Existing kernels are dependencies,
not duplicate compiler implementations.

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
- Run affected checks during iteration and broad relevant native/formal checks
  at landing. Record evidence scope and the revision, remove replaced owners
  and compatibility readers, then update support and the next unit's premises.
  Compare compile/check time, artifact size, memory and execution on matched
  workloads; passing integration tests supply no cryptographic or speedup claim.

### Extensions with separate entry conditions

Transform/PDL adoption depends on a useful admitted schedule and reader coverage;
shipping a dialect is not itself a completion criterion. General privacy
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

The current service registry supports six RNG distributions/providers. Arbitrary
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
