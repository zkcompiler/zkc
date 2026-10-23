# Roadmap

Development extends one supported model: `.zkc` Language → Protocol IR →
`zkc.program/0` → VM programs, the Rust interpreter and Entry/proof/joint Hosts.
[Status](status.md) records existing support; this page orders further work.

## Strengthen the maintained path

Keep Schnorr and Sumcheck libraries, their source Entries, relation data import
and installed C++/Rust consumers representative of the public workflow. New
capabilities should use the existing profiles and interpreter, with explicit
formation, transformation, admission, execution and failure contracts.

Preserve general algebra, relation Assets, native kernels, structured messages,
resource custody, iteration, completion and attempts. Broader source syntax and
new protocol libraries are additions to this model. Lean research develops
independently.

## Make numerical realization explicit

Build on the checked physical plan, which retains original Kernel bodies and
selected Local realizations together, with checked binding lifetimes in the
physical schedule. Extend the checked SCF loop schedule with target-specific
numerical kernels, preserving domains, indexing, reductions and failure obligations.
Compare numerical variants through the same checked transaction and installed
operation contracts. Establish field representations,
layouts, aliasing and work bounds before adding generated arithmetic. VM control
retains participant order and authority.

Validate realization refinements across representative operations and protocol
families. Keep alternate interpreters, JIT and AOT dependent on evidence and the
same execution contract; the VM separation itself makes no performance claim.

## Compile structured quotient arithmetic

Reuse HEIR's Polynomial and ModArith arithmetic vocabulary inside checked
compiler regions, following the [quotient-ring rationale](rationale/quotient-rings.md).
Retain compound ring and module operations until transform placement and
realization selection finish. The checked coefficient source contract remains
the observable boundary; existing field-polynomial types retain their meanings.

Build on the optional [pinned arithmetic package](../compiler/external/heir/README.md)
and its [full-NTT comparison profile](spec/realization/heir-arithmetic.md).
Extend the source and candidate reader coverage of the existing managed
integration at each new lowering boundary. The admitted integration includes
Falcon batch arithmetic and an ML-DSA-style module matrix-vector computation,
with shared transforms, charged preparation and scratch, unchanged ordered
admission, and a coefficient fallback. Dialect registration or a standalone
lowering experiment does not complete that integration.

Compare complete arithmetic regions against competent native composition,
including compilation, preparation, retained transformed storage and execution.
Use compiler work limits and runtime capacity checks when selecting a realization.

Build on the [prepared exact module-product consumer](spec/domains/quotient-matrices.md)
when extending compiler selection to RNS. Keep protocol moduli separate from
compute primes, and preserve checked centered-reconstruction capacity through
accumulation and chunking. HEIR RNS conversion needs repaired and independently
qualified lowering before it joins the admitted arithmetic profile.
Partial NTT, broader ring maps and new hardware targets need their own admitted
profiles. Native arithmetic integration proceeds independently of Lean
correspondence work.

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

The current service registry supports four RNG distributions/providers. Arbitrary
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
