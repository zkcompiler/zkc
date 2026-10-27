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
Each unit below is one substantial pull request: research alternatives and
consumers, specify concrete semantics/refusals, implement the complete unit,
independently review it, validate and fix it, then revise the next unit against
what actually landed. Keep one canonical implementation at every transition.

| Unit | Entry condition and completion criteria |
|---|---|
| Current architecture consolidation | Connect production numerical realization to its checked Tensor/Linalg profile, enforce IR interpretation versus Transforms production, preserve all numerical pass options, declare temporary dialect dependencies, remove obsolete computation APIs and update installed consumers; retain current execution semantics |
| Component-contract foundation | Reconcile the independently developed formal and native/frontend contract and relation interfaces on the landed base before adding realization features |
| Oracle realization and program bytes | Protocol-owned oracle kinds/anchors, virtual dependencies, typed realization records between preparation and projection, independent actual-body comparisons, block-draw and gated-request emission, witness codec slot, source AST/elaboration export and an exact version-0 executable byte grammar |
| STARK compiler support | Consume the landed realization records for executable queries, authentication, selected transcript/extension fields and gating; settle AIR asset ownership before adding another representation |
| Represented execution | Residue and codec semantics, private buffer contracts and admitted Arith/Vector/Bufferization lowering; compare native kernels and transparent schedules on representative exact workloads |
| Constraints and semantic consumers | One assignment-level owner, source-to-encoding adequacy, lookup/multiset and chronological-memory consumers, exact statement/witness maps and bounded external adapters |

Oracle design must settle shape provenance, answer-use dominance, logical versus
physical query accounting, dynamic occurrence identity, setup binding and the
request's actual byte/primitive interpretation before emission. An initial
static/initial-statement shape profile does not admit challenge-adaptive shapes.
Ideal realization must name its observation boundary; whole-table transport does
not establish oracle privacy or adversarial extraction. Mathematical equality,
all-assignment encoding adequacy and cryptographic reduction remain distinct
validation obligations.

Runtime work supplies per-target installation, checked compound realization,
batched Merkle hashing and the grind kernel. The compiler unit owns request
layout and emitted behavior and reviews the shared contract. Target ingress
stays before native resident handles; no extra typed-program view is required.
Formal models and realization/security proofs remain with their semantic owners.
Generated shared files are regenerated from the agreed current schema after
integration, rather than preserving competing representations.

Represented execution evaluates HEIR on precise polynomial/modular subdomains,
with conversion laws and measured build/runtime/maintenance cost. Constraint
work evaluates LLZK/CirC with complete representative assets. Transform/PDL
scheduling, general privacy analysis, adaptive oracle profiles, further folding
and lattice algorithms require concrete consumers before expanding these units.
A complete Falcon verifier and AOT backend are separate projects.

Validation at each unit includes independent malformed-candidate controls,
source-relative identity/layout checks and relevant installed/native/formal
consumers. Measure compile/check time, artifact size, memory and execution when
choosing between representations. Performance and cryptographic claims need
their own evidence; a passing integration suite supplies neither automatically.

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
