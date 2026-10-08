# Native proof compilation

Native proof compilation analyzes retained common mathematical source and applies
selected transcript construction to unsimplified participant mathematics.
Independent producer and validator programs run through the shared interpreter.
The [proof profile](../spec/profiles/compiler/native-proofs.md) owns exact
admission, formats and semantics; this guide explains the implementation and use.

## Pipeline and ownership

```text
immutable common mathematical source + selected deployment policy
    │ admit; resolve source occurrences and verifier dependencies
    ▼
protocol → participant                  ordinary projection, unsimplified
               │ optional selected transcript construction
               │ check actual candidate and source/result/resource maps
               │ simplify under preserved action and interface contracts
               ▼
              exec → physical          shared math lowering and binding
                           │
                     participant programs
                       /           \
               joint host      proof host
                            produce / validate
                            separate processes
```

Construction is a transformation within the existing participant profile, not a
fifth IR stage or a new dialect. Both source and constructed participant
programs retain typed mathematics. The deployment descriptor and correspondence
record are immutable inputs/results of checking, not executable transcript
graphs.

| Owner | Responsibility |
|---|---|
| `ZkcNativeCompiler` | Admit/capture source and policy; compose projection, construction checking, lowering and deployment assembly |
| Protocol transforms | Rewrite selected queries/deliveries and thread generated role-local transcript calls; retain source origins and actual operand maps |
| `protocol`, `local`, `crypto` | Existing roles/messages/services, ordered local programs/capabilities, and bound transcript kernels |
| Shared compiler pipeline | `compileRun` and `compileNativeProof` share physical participant compilation |
| `zkc-runtime` | One `Runner` and its native control/cut API; structural admission with a selected proof-entry policy |
| `zkc-tools::proof` Host | Native deployment admission, shared binding, codecs, proof framing, publication and per-invocation resource handling |
| Backends | Existing Arkworks/Dalek/Plonky3 and transcript implementations; no whole-protocol callbacks |

The native proof host uses `NativeProofEntry` and the runner's control API for
loops, yields and local completion. Its admission separates private external
inputs from host-created transcript roots. The joint schedule is not the authority
for an independently executing role. The typed `NativeProofReport` retains successful copyable original results for
both participants, indexed by their original output ports. Rejection and cleanup
failure suppress those results. Generated transcript and private successors are
retired by the same Host; CLI diagnostics do not publish application outputs.
`execute_typed` and `execute_attempts_typed` accept in-process immutable data and
explicit provider/key declarations through the same preparation. Public data
is canonically bound; private data avoids a serialization roundtrip. Source
`entry::ProofEntry` adds named inputs/results and explicit authored binding
acknowledgement over these methods. Native callers may import `ProverMaterial`
once from bytes or a regular file and supply `InputValue::ProverKey` on repeated
calls. The handle shares immutable material while each call retains its own
setup admission, quotas and runtime state. Named source setup bindings expose this constructor through the Entry Host. An outer `Ok` reports successful preparation;
check `ProofReport::is_success()` for acceptance and complete cleanup, or use
`into_result()` to branch while retaining the full report on failure.
For a complete executable CLI example, see
[separate producer and validator](../runtime/bundles.md#separate-producer-and-validator).

## Why construct after projection

A common value denotes a family of role components. A `protocol.local_call`
returns values at one owner. Therefore two transcript calls returning `cP` and
`cV` do not produce a single common challenge family under existing availability
intersection/restriction rules. Common construction would need either a new
disjoint-role assembly operation or role-specialized duplication of downstream
mathematics. Ordinary projection already performs the required specialization.

| Alternative | Decision |
|---|---|
| Rewrite the common program and add role-family assembly | Not needed for the selected constructor. Reopen only for an independently useful common-program client. |
| Pure `challenge(prefix)` expression | Useful as a mathematical interpretation of a specific construction, but not the execution primitive for affine state, ordered failure, budgets and retries. It would also require a concrete encoding and dynamic prefix representation. |
| Derive everything from already optimized participant code | Reject: source draw selection, distinct receive components and original ordered work may have been erased. |
| Analyze common source, project, then construct participant mathematics | Selected. Preserve source decisions and build actual role-local states without an additional core operation. |
| New transcript dialect, mutable graph or protocol-specific runner | No demonstrated need. Existing operation owners, SSA, regions and common runner express the selected behavior. |

Projection metadata is not sufficient by itself: retain the original source and
recompute its dependency/occurrence view when checking the candidate. The
construction changes the interface. `protocol.projection` carries a versioned
construction map alongside immutable original interfaces/actions and checked
input/result/action substitutions for the actual candidate. Ordinary projection verification
still applies when this map is absent. Constructed-profile formation verifies
both interfaces and the map; the source-relative checker validates its meaning.
The maps are frozen before participant simplification and lowering; metadata
cannot replace the source-relative check.

The construction adds only an internal transcript input/result to each
participant and removes the selected validator service. The producer host
receives all explicitly authorized public bindings for root initialization;
there are no generated participant data inputs. Shared public components must
agree with participant inputs before execution.

Derived/batched delivery or public replay recipes reopen the construction
placement decision. First compare a common-program normalization into direct
delivery using existing operations. Revealing a previously hidden challenge is
an experiment change that needs an explicit construction contract. If that does
not suffice, compare checked participant recipe emission with common role-family
assembly. Neither option resolves a private-input publication requirement.

MLIR provides [operation interfaces](https://mlir.llvm.org/docs/Interfaces/) and
[dialect conversion](https://mlir.llvm.org/docs/DialectConversion/) for the shared
mechanics. Use operation-owned effects/dependencies and ordinary SSA mappings,
region arguments and symbol references. Admission remains closed; unknown
operations or unrealized casts cannot slip through a partial conversion.

## Policy and formats

`zkc.native-proof-policy/4` is the sole proof policy for flat programs, bounded
loops, PCS, structured messages and authored execution. Deployment, descriptor,
construction metadata and invocation binding also use `/4`. Every proof embeds
`zkc.program/1`; joint execution uses `zkc.run/1`. This is one proof contract
within the four IR profiles. Other proof versions have no compatibility reader.

Generated transcripts use `transcript.native.indexed.challenge` and
`transcript.native.indexed.observe.data`, with explicit indexed origins even for
flat programs. Signature, history effect, attribute admission, physical binding
and export must agree. Authored `external.*` primitives keep their own contracts.
A catalog domain does not automatically extend the suite or codec allow-list.
Independent Lean models require their own native interpretation and correspondence.

## Construction and admission

1. **Capture source and policy.** Admission resolves original occurrences,
   effective roles, public bindings, supported control and complete coverage.
   Exact UTF-8 source bytes determine source identity.
2. **Project and construct.** Unsimplified projection precedes role-local
   transcript insertion. An independent projected-to-constructed postcondition
   checks actual observations, challenge delivery, state threading and retained
   definitions. `checkNativeProof` reconstructs under this postcondition, then
   compares the whole supplied candidate, including local bodies.
3. **Lower and emit.** Ordinary participant simplification, mathematical lowering
   and physical selection use the shared compiler pipeline. Emitted programs and
   deployment role/port maps are checked against retained subjects; see
   [preservation](preservation.md).
4. **Admit deployment and invocation.** The application authenticates the exact
   deployment digest. Rust checks captured policy, actual wire sites, observation
   operands, complete state chains and public-port maps against the admitted
   program. Invocation preparation precedes resource issuance.
5. **Run independently.** Producer and validator consume their own inputs and
   resources. The validator needs its authorized public context and proof, not
   the witness or a running producer. Framing, cleanup and atomic publication use
   the common host mechanisms.

For callers with an explicit verifier service but no source site list,
`selectNativeProofDraws` resolves ordered query/delivery occurrences through the
same preparation and admission as construction. Input `draws` must be empty;
entry, participants, public inputs, acceptance, suite and service remain explicit.
It returns a complete strict policy and preserves original IR. Existing explicit
policy callers still have to supply exact occurrence names. The fresh source
Entry compiler requests it through `NativeProofSelection` in
`NativeProofOptions::policy`. `compileNativeProof` selects occurrences inside its
owned diagnostic context and returns the complete policy with the deployment.
A string policy retains the explicit-occurrence API.

Internal hashes do not authenticate a supplied program. The host hashes and
parses one captured buffer against an application-supplied expectation. Generic
supplied-program admission establishes structure and installation, not source
correspondence. The independent constructor postcondition and runtime controls
are bounded checks, not a derivation theorem or native Lean semantics.

## Transcript and proof boundaries

Installed transcript suites use explicit affine state. Authored external
Monero/OpenVM data-state transitions retain their distinct contracts. The BLS
suites are `merlin3.bls12-381.fr64be/1` and
`spongefish0.7.4.keccak.bls12-381.fr64be/1`; Ristretto and
ext8 suites are also registered. BN254 challenges remain outside the profile.

The native root binds source and policy identity, ordered actual public values,
application context and applicable setup material. Its exact encoding and bounds
belong to the [deployment and invocation contract](../spec/profiles/compiler/native-proofs.md#deployment-and-invocation-records).
The complete canonical root enters the suite under `binding`; its SHA-256 digest
is the proof-header binding. Candidate hashes bind compilation separately.
The installed Spongefish kernel uses raw `Keccak::default()` with zkc framing;
it does not claim upstream `DomainSeparator` or I/O-pattern semantics.

[Occurrences](../spec/profiles/compiler/native-proofs.md#native-occurrence-encoding)
bind original entry/call/repeat paths and query/message sites, with explicit
induction coordinates for enclosing repeats. Generated helper names, physical
renaming and runtime diagnostic paths do not determine transcript bytes. The descriptor keeps
a flat static event list; loop ancestry and SSA control supply the structure.
A second recursive descriptor would duplicate that control.

Canonical decoding precedes observation of received values. Structured codecs
bind complete types, tags, lengths and actual payloads. External raw-byte formats
need an explicit adapter retaining the relevant bytes; a permissive internal
decoder would change transcript meaning. The `ZKCPRF01` outer frame carries the
SHA-256 digest of the canonical native invocation root.

A completed producer may return only a proof prefix. The independent validator
checks the actual final decision and proof exhaustion. Header consistency alone
does not cryptographically bind an authored no-transcript proof to context; the
corpus includes a rewrapped-header control demonstrating this boundary.
[Attempts](native-attempts.md) retain consumed randomness/work and discard retry
buffers under an application-owned returned-decision policy. Fatal stops are not
retry decisions.

[Merlin's operations](https://merlin.cool/transcript/ops.html),
[round-by-round soundness](https://eprint.iacr.org/2019/1261) and
[duplex Fiat–Shamir](https://eprint.iacr.org/2025/536) describe separate interfaces
and models. Using their primitives establishes neither theorem's applicability
to an arbitrary authored protocol.

## Informative DLEQ sketch

The following uses additive notation and omits concrete origin/codec arguments
only for readability. All four public group values are bound. Nonzero bases are
an explicit relation/application requirement; guards are kept when authored.

```text
source relation: Y = x*G and Z = x*H

P: k <- private_rng.draw()
P -> V: A = k*G
P -> V: B = k*H
V: c <- challenge_rng.draw()
V -> P: c
P -> V: z = k + c*x
V: return z*G == received_A + c*Y
       and z*H == received_B + c*Z

constructed P                         constructed V
T = host_transcript(public_context)    T = host_transcript(public_context)
k <- private_rng.draw()               A = proof.receive()
A = k*G; proof.send(A)                T = observe(T, received_A, source_A)
T = observe(T, sent_A, source_A)       B = proof.receive()
B = k*H; proof.send(B)                T = observe(T, received_B, source_B)
T = observe(T, sent_B, source_B)       c, T = challenge(T, source_draw)
c, T = challenge(T, source_draw)       T = observe(T, c, erased_delivery)
T = observe(T, c, erased_delivery)     z = proof.receive()
z = k + c*x                           T = observe(T, received_z)
proof.send(z); T = observe(T, z)       ok = both_original_equations(...)
return internal T                     return ok, internal T

host: dispose T; publish on success    host: dispose T; accept iff ok,
                                           normal return and proof exhausted
```

These are separate programs, not a schedule containing both roles. A changed
proof changes the validator's actual received components. The compiler does not
substitute the producer's commitment expression into the validator equation.
The selected source challenge service disappears; the private nonce service
remains. A scalar-service nonce-reuse control demonstrates the changed
experiment without claiming the compiler can prove a provider's independence law. Existing affine
`nonce` commitment/response kernels retain their separate one-use custody
contract; exercise them as well. Copyable scalar randomness does not replace
that supported capability or prevent reuse across invocations.

## Command-line use

After building the compiler and runtime, put their binaries on `PATH` or use
absolute paths. With a mathematical source, policy and invocation inputs:

```sh
zkc-compile protocol-proof protocol.mlir policy.json > deployment.json
zkc produce-native-proof deployment.json TRUSTED_SHA256 producer.json proof.bin
zkc validate-native-proof deployment.json TRUSTED_SHA256 validator.json proof.bin
```

Obtain `TRUSTED_SHA256` from trusted compilation or deployment configuration.
The [walkthrough](../runtime/bundles.md#separate-producer-and-validator) supplies
complete inputs and commands. `protocol-construct-proof` emits unsimplified
participant mathematics; `protocol-check-proof` checks a supplied candidate
against original source and policy. The C++ API is `compileNativeProof` in
[`NativeProof.h`](../../compiler/include/zkc/Compiler/NativeProof.h).

Setup-bearing deployments require application authorization through
`--setups=AUTHORITY`, including deployments with one key. `--attempts=POLICY` selects
[bounded attempts](native-attempts.md); `--capacity=LIMITS` selects host limits.
These settings do not authorize keys or program identities supplied by a prover.

## Commitments and setup authority

The committed Sumcheck clients keep original commitments and private immutable
opening states while prover scratch tables shrink. The validator accumulates its
actual challenge point, checks every round and verifies openings of those original
commitments at the final point. The terminal follows the Sumcheck/PCS separation
in [Thaler's text](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf).
Repeated openings use ordinary immutable state; no second affine lifecycle is
needed. The installed PCS requires positive arity and is nonhiding.

`NativeDeployment::admit` in `zkc_tools::proof` takes independent
deployment and setup authority. The Host imports canonical, fingerprint-checked
public keys before PCS decoding and binds their full bytes in the invocation
root. Prover material has a separate full-material pin. Each setup-bearing input
has an authorized key association; peer metadata may select only a registry key.

An incoming value under another authorized setup may decode and be observed.
The explicit verifier-key operand at `pcs.check` enforces the protocol's expected
key and arity. A returned PCS value without that check is authorized but need not
belong to a specific output setup. The Host has no output setup slots or
per-receive source selectors. Path-specific mixed-setup input authorization
remains unsupported. See the [setup contract](../spec/profiles/compiler/structured-proof-messages.md#application-authorized-setups).

Admission checks every mapped input, including unused ports and inactive PCS
alternatives. Internal point/opening-state types can be valid IR without an
external constructor. An unused helper alone does not create a setup requirement;
actual executed PCS work needs its explicit key or opening-state operands.
The compiler checks terminal operand preservation but does not infer that an
authored predicate proves the intended relation.

## Loading and capacity

Public declarations count toward invocation loading even when used only in the
binding root. Matching role operands reuse decoded values after exact agreement;
each operand still counts toward entry retention. Per-value decode preflight
precedes payload decoding. Cumulative loading admission has its own ledger and
can occur after that decoding; it is not a whole-process memory bound.
Key files use bounded regular-file reads and pinned material. Data, entry and
transcript-root capacities are checked before execution entropy.

Nonce/RNG operands and the selected transcript reserve their capability retention
charges before issuance. Sequential attempts reserve one live transcript slot
while retaining cumulative execution work and allocation accounting. JSON,
logical counts, retained values, wire bytes and primitive work have distinct
ceilings; raising one does not raise the others. See
[mathematical composition and capacity](mathematical-composition.md).

## Validation clients and extension conditions

| Maintained controls | Boundary exercised |
|---|---|
| [Flat proofs](../../compiler/test/native_proofs.py) and [independent reference](../../crates/zkc-tools/examples/native_proof/reference.rs) | Schnorr, DLEQ, affine nonce custody, two draws, nested/reversed-role applications, Boolean messages, public bindings and authored no-transcript execution |
| [Iterated proofs](../../compiler/test/native_iterated_proofs.py) | Product/cubic Sumcheck, nested received counts, zero-trip loops, coordinate/state/order mutations and compact program size |
| [Committed proofs](../../compiler/test/native_committed_proofs.py) | Original commitments, actual verifier points, independent PCS checks, wrong context/key/point/proof and malformed frames |
| [Domain clients](../../compiler/test/native_domains.py), [setup clients](../../compiler/test/native_setups.py) | BN254 G1/G2/Fr, Ristretto and ext8, actual provider draws, multiple authorized setups and swapped terminal keys |
| [Native execution suite](../../tests/protocol/test_native_mathematical.py) | Separate processes, fixed-randomness comparisons across lowering modes, atomic publication, malformed data, custody, retries and capacity |

The references independently reconstruct equations, roots, origins and frames,
while reusing trusted upstream arithmetic/transcript primitives. They are bounded
execution evidence. These controls are not complete Groth16, BP+ or zkVM libraries. Native Lean
semantics and cryptographic proofs remain separate work.

New schemes, dynamic protocol composition, differing-root affine joins and
broader construction recipes require explicit design and admission rules. Existing [structured data](structured-proofs.md), [nested data](nested-data.md),
[authored transcripts](authored-transcripts.md), [relation bindings](relation-bindings.md)
and [entry completion](entry-completion.md) already use this pipeline. [Roadmap](../roadmap.md) records further native work;
retired source/application consumers impose no porting obligation.
