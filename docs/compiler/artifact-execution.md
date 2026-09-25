# Independent proof artifacts

The compiler turns an authored interactive protocol and an explicit construction
descriptor into a proof producer and a validator that run in separate processes.
The validator receives candidate bytes, its public statement and application
configuration. It does not execute a hidden prover or receive its witness.
The [format](artifact-format.md) defines the installed construction and byte
contracts.

## Compilation boundaries

```text
Original common protocol + selected construction descriptor
    → constructed common protocol + checked origin/input/result maps
    → independent participant algorithms
    → selected physical kernels and resource operations
    → Rust Runner + selected cryptographic kernels/transcript + proof-file transport
```

Construction happens while interactions, roles, dependency bindings and source
algorithms remain visible. It emits ordinary common source containing explicit
transcript operations and required public derivations. The existing participant
projection and physical lowering then apply. A constructed program and an
interactive program can share dialect operations while having different admission
contracts. This adds a concrete construction to the
[top-down pipeline](protocol-pipeline.md), not another universal IR level.

`compiler/lib/Protocol/Construction.cpp` currently transforms the admitted,
resolved portable common representation, then imports/verifies the result through
the registered MLIR implementation. It is not yet an independently usable MLIR
rewrite pass over arbitrary mixed-level programs. Projection and physical lowering
remain explicit compiler steps; there is no direct LLVM code-generation claim.

The compiler preserves every original validator operation in order, including a
guard whose output is unused. Producer replay follows demanded operands through
admitted pure public recipes. A public input is available; a validator's successful
check is not thereby available as a producer fact. Selected challenges are derived
independently at both roles from their own affine transcript state.

P-to-V messages become framed proof payloads. V-to-P delivery is removed when its
value has a supported producer recipe; both roles still observe the original
message in their transcripts. Calls and public counted loops retain their source
instance paths and operation sites. Generated helper names and runtime session IDs
do not become transcript identity. Original selected-RNG provenance and transcript
transition counts remain separate.

## Authored examples

The [first protocol walkthrough](../getting-started.md) supplies executable
commands for development fixtures, compilation, proof production and validation.

Readable sources and construction descriptors are available in the
[example index](../../examples/protocols/README.md). The compiler accepts `.pir`
inputs directly; `protocol-source` emits the equivalent JSON still consumed by
the native host and Lean checker.

| Source | Original algorithm | Constructed execution |
|---|---|---|
| [Committed two-factor argument](../../examples/protocols/committed-two-factor.json) | Commit both originals; check expected public roots; run Sumcheck; call the same opening child twice; check the terminal product | Real arkworks multilinear PCS, independently derived challenges, original V guards and both opening checks; rank 3 proof is 1,514 bytes |
| [Repeated DLEQ](../../examples/protocols/dleq.json) | Call a two-base discrete-log equality argument twice; commit with a private nonce, challenge, respond, check both equations | Real BLS12-381 G1 operations and spent nonces; 380-byte proof, without a whole-protocol backend callback |
| [AIR and oracle protocols](../../examples/protocols/air-oracle/README.md) | Two finite AIRs connected by challenged permutation auxiliaries, quotient/OOD checks and FRI; contrasting affine-table protocol | Plonky3 field/DFT and Merkle kernels, independent query authentication, extension-field/index sampling and original-source Lean comparisons |

The committed variant deliberately adds expected-root comparisons to the older
two-factor source. It proves a claim about the application's selected commitments;
receiving two arbitrary commitment messages does not establish that association.
The old interactive example keeps its own meaning.

These examples cover different algebra, repeated child calls, compact public loops,
guards, source-bound public statements and private capabilities. They establish
bounded working clients, not support for all protocol families, Orchard or a full
zkVM.

## Executable and library responsibilities

| Component | Responsibility |
|---|---|
| C++/MLIR | Source formation and resolution, compact construction analysis/emission, source maps, participant projection, physical selection |
| `zkc-tools::artifact` | Checked invocation, public binding, bounded input/key loading, proof transport, observations and atomic publication |
| `zkc-runtime::interactive::Runner` | Independent participant control, calls/loops, suspension, affine custody, resource limits and unwind |
| `zkc-backends` / `zkc-arkworks` | Typed finite operation catalog, concrete values, key import, arkworks and Plonky3 arithmetic/commitment kernels, explicit secret resources |
| Merlin 3 | Selected labeled transcript; each installed suite defines its field/index sampling and canonical observation contracts |
| Lean `Tools.Artifact` | Independently execute the original source's validator under the selected construction, including source control, framing, arithmetic and reached observations |

The host requires all serializable original V entry inputs to be public-bound,
all V keys to be configuration-bound, and its only resource input to be the
selected RNG. This mandatory public-artifact profile is narrower than general
interactive PIR. An admitted module cannot already expose transcript resources
in its original signatures. Private P resources remain explicit.

The host supports multiple application-authorized verifier keys, with exact
source-port and executable receive-site setup selections. Persistent proving material is loaded
against its expected material fingerprint and specifically associated full key. Repeated immutable imports may
share backing, but aggregate admission still charges each entry operand. A proof
header never chooses its own statement or key.

Prepared invocations accept a host-owned `InvocationOptions.value_budget` for
live and cumulative retained-payload accounting. `Runner::new` and ordinary CLI
execution retain the default 64 MiB live / 256 MiB cumulative policy; the explicit
constructor and prepared host can select other limits. Each retained binding is
charged even if immutable backing is shared. These counters are neither peak
physical memory nor a proof parameter. Individual-value, structural, proof-wire
and backend limits remain separate. A prover-selected artifact cannot raise the
validator's host policy. Raising this budget permits more execution; it is not
an optimization or an assurance claim.

## Running the path

The [first-run walkthrough](../getting-started.md) contains the maintained
construction, production and validation commands. Use the
[artifact format](artifact-format.md) for descriptor fields, input data and
runtime limits; [authored examples](#authored-examples) above identify the
contrasting protocol sources.

Each command rechecks the supplied artifacts. The producer publishes only a
completed proof. The validator accepts only after the mapped original Boolean
result is true and every proof byte has been consumed. The producer/validator transition limit
bounds transcript transitions, including message observations; it is not a draw
count or security parameter. Development setup and known-witness fixtures are
separate examples, never implicit operations of these commands.

## What is checked, tested and proved

The host recomputes the prescribed construction using its installed trusted C++
checker. A separate Lean checker admits the supplied physical participants against
the constructed common program. This checks concrete projection; it does not
independently prove the C++ construction correct.

For construction testing, `artifact-reference` executes **original source**, not
the generated common program. Its public crypto service answers exact requests
for SHA-256, Merlin and arkworks group/PCS operations; it receives no witness or
proving key and does not implement a protocol verifier. Lean independently owns
control, source framing, field/table logic, proof cursor and event construction.
The crypto libraries and their public adapter are shared trust dependencies.

Differential tests compare outcome classes, every public event, consumed proof
bytes and selected challenge count. The finite corpus includes every truncation
of the two honest proofs and hostile substitutions. Native resource-limit tests
separately verify complete recorded transitions and unwind. Native evidence/input
budgets and Lean evaluation budgets are not claimed universally equivalent.

The [formal scope](../../formal/design/artifact-reference.md) separates existing
typed projection laws, list-byte framing laws, executable checkers and these
native tests. No native construction theorem, arbitrary-protocol FS reduction,
zero-knowledge guarantee or external-backend verification follows. The polynomial
PCS is nonhiding; keys are development setup. Constant-time secret arithmetic,
zeroization and production setup assurance remain deployment work.

## Current limits and next decisions

The selected construction handles two roles, resolved static dependencies and
public counted loops over the installed operation profiles. Private-verifier
artifact protocols, arbitrary plugins/domains, dynamic interaction, independently
keyed PCS families, recursive verifier generation and streaming services need
additional contracts and implementations.

A count-one loop result can be mathematically available yet lack a typed
pre-loop seed in the current loop carrier. Such construction refuses explicitly.
Before an optimization relies on output-producing exactly-once scopes, compare
the representations and establish source-origin/control correspondence. This is
a concrete research trigger, not a reason to invent default proofs or redesign
every working loop.

A shared optimization is chosen from measured behavior and existing theory.
Admission and key caching and interpreter overhead are engineering observations;
this path makes no protocol-optimization speedup claim.
