# Independent artifact host

The `zkc` binary runs one checked constructed participant per process with the
actual NativeBackend. The construction contract is
[constructed artifact format](../../docs/compiler/artifact-format.md).

```sh
zkc produce-artifact SOURCE DESCRIPTOR CONSTRUCTION PARTICIPANTS PRODUCER_INPUTS COMPILER_CHECKER LEAN_CHECKER PROOF TRANSCRIPT_BUDGET
zkc validate-artifact SOURCE DESCRIPTOR CONSTRUCTION PARTICIPANTS VALIDATOR_INPUTS COMPILER_CHECKER LEAN_CHECKER PROOF TRANSCRIPT_BUDGET
```

All paths are supplied by the application. Both commands independently read and
check the original source, descriptor, six-element construction result and
physical participants. `COMPILER_CHECKER protocol-check-construction` recomputes
the prescribed construction against exact immutable source/descriptor snapshots.
This is a trusted native construction check, **not independent Lean construction
correctness**. `LEAN_CHECKER --check-generic`
independently admits physical projection against the constructed common program.
The independent `artifact-reference` additionally executes original protocol or
generic-library source against the actual proof; it receives no generated helper
manifest or participant program. Installed checker binaries
are trusted application dependencies, not candidate-supplied executables.

Explicit-binding sources admit the installed BLS and Ristretto transcript
suites under either the exact or the normalized identity policy of a
`zkc.construction/1` descriptor. Closed-profile source carriers are refused.
Ristretto uses `merlin3.ristretto255.scalar64le/1`: the primitive service
returns 64 challenge bytes through `zkc.transcript-request/3`, and the reference
reduces them little endian. The primitive service has no profile-tagged challenge route. Prover RNG inputs use the nominal field of the admitted port
and actual OS-seeded resources.

`tests/artifact/test_composable_domains.py`, in the repository's cross-build tests,
names the tools it needs and records their hashes. It tests vector
counter parity, shared diagonal consumers, both descriptor identities, and
full artifact observations for honest, trailing-byte and false-equation proofs.

Generate artifacts separately:

```sh
"$COMPILER_CHECKER" protocol-construct source.json descriptor.json > construction.json
python3 -c 'import json; print(json.dumps(json.load(open("construction.json"))[2]))' > common.json
"$COMPILER_CHECKER" protocol-compile common.json > participants.json
```

`CheckedBundle` retains the checked source, mappings and admitted program.
Physical input names may be renamed by lowering; the host follows the common
role-port order established by independent projection admission. Acceptance uses
exact checked source-to-generated result mapping and requires a true Boolean
and exact proof EOF. A candidate manifest or proof header never authorizes itself.

Before issuing resources or accessing proof bytes, both commands require the
public artifact profile: all serializable original V entry ports are explicitly
public-bound, verifier keys are configuration-bound, and the selected RNG is the
only V resource input. Original local/protocol signatures cannot already contain
`transcript`. General common construction can represent broader private-verifier
flows, so constructor success alone is insufficient. The Lean original-source
reference independently checks these same restrictions. Low-level Rust
`produce`/`validate` helpers assume their caller has admitted its runner and root;
they do not confer the public artifact profile by themselves.

## Prepared execution

The Rust host can admit immutable artifact and caller requirements once, then
execute repeatedly with fresh authority. `CheckerInstallation` is an opaque
process-local epoch. Its executable paths launch checkers; they are not content
identity or automatic deployment-change detection. The application keeps actual
checkers, dependencies, backend and admission policy fixed during an epoch and
creates a new epoch when any changes. `prepare_checked` additionally requires
the caller to attest that its existing bundle was checked under that installation.

```rust
let installation = CheckerInstallation::new(compiler_path, lean_path);
let prepared = installation.prepare(paths, CacheLimits::default())?;
let requirements = ClaimRequirements::from_slices(&contract_bytes, &certificate_bytes)?;
let mut prepared = prepared.with_requirements(&installation, requirements, physical_choices)?;

let proof = prepared.produce(&installation, &producer_inputs, options)?
    .execution.outcome?;
prepared.validate(&installation, &validator_inputs, &proof, options)?
    .execution.outcome?;
```

`with_requirements` checks the retained caller contract against the captured
source, construction and **actual physical candidate**, using the selected
implementation, contraction and storage options. These are the same options
accepted by `claim-check-lowering`. It does not authenticate the caller contract
or prove its trusted law premises. The application still authorizes each
request's actual ledger, context, configuration and statement. Replacing
requirements needs a new admission; failure consumes the proposed prepared
handle. The one-shot CLI does not implicitly perform this caller-claim check.

Only validated immutable proving/verifying keys cross invocation boundaries.
The private cache is bounded to at most 64 entries and 64 MiB of conservative
material/identity charge. Every call still reads and hashes actual proving-key
bytes, checks the full associated verifying key, and charges input work and
resource budgets on cache hits. Full or disabled caches skip retention. Proof,
wire and witness validation are never cached. `clear_cache` releases retained
keys. This charge is not RSS or a total allocator limit.

Each call constructs a fresh native backend, transcript, RNG/nonce authority,
runner and proof reader/writer. Neither mutable resources nor private inputs are
retained. Calls use `&mut self` and are sequential. A failed call may keep fully
validated immutable keys, but never partial imports or execution state.

The [prepared artifact example](examples/prepared_artifact.rs) and its
[argument driver](examples/support/prepared.rs) support retained claim checking,
cache-disabled comparison and separate admission/binding/execution timing.

## Inputs and configuration

Each process receives this exact array envelope:

```text
["zkc.artifact-inputs/1", applicationContextHex,
 [[publicLabel, fullNominalType, canonicalPublicWireHex], ...],
 roleSourceInputRecords,
 ["zkc.public-configuration/1", verifierRecords, inputSelections, receiveSelections]]
```

Public records are named and may be provided in any order. The host requires
exact descriptor coverage and normalizes them into descriptor order for root
binding. Labels retain exact UTF-8 bytes. Multiple distinct ports of one role
may share a public equality binding. Unknown/duplicate labels and ports fail
closed. Explicit source values for filled public ports must agree byte-for-byte.

Source records are named using **original source entry ports**, never generated
SSA names. The supported records are:

- `[port, fullNominalType, canonicalWireHex]` for ordinary source values. The nominal type must match the
  admitted source port. These are full `ZKCV` ordinary
  wire bytes, including headers, not bare field/group encodings.
- `[port, "prover_key_file", path, expectedMaterialFingerprintHex, verifierSourcePort]`
  for P proving material. The application supplies the expected full 32-byte
  material fingerprint and the corresponding configured V port. Loading validates
  the fingerprint, VK association, canonical points, bounded shape and exact EOF.
- `[port, "nonce", transitionBudgetDecimal]` or `[port, "rng", transitionBudgetDecimal]`
  for unrelated P-owned source capabilities. These are public issuance policies;
  the CLI issues secret material exclusively from the OS. They cannot import
  private nonce values or forge capability state.
- `[port, "verifier_key:multilinear.kzg.bls12-381/1", canonicalVerifierKeyHex]` for an optional explicit V
  key duplicate, which must exactly match that port's configured bytes.

VK configuration records are in **original V source entry-port order**, with all
and only its actual verifier-key inputs. Their bytes use the canonical Ark key
file format (`ZKCAR006`, verifier kind), not the ordinary message codec. Full VK
bytes come from the application, never from the proof. Multiple distinct
identities are authorized by the setup registry. Group-only entries use an empty
key list. The host does not generate setup. Validator input files never contain P
witness or proving-material records; wrong-owner records are rejected before file access.

The configuration is:

```text
["zkc.public-configuration/1",
 [[verifierSourcePort, fullVerifierKeyType, canonicalVerifierKeyHex], ...],
 [[role, originalEntryPort, verifierSourcePort], ...],
 [[originalInstance, receivingRole, messageSite, verifierSourcePort], ...]]
```

This permits multiple distinct setups. Input selections cover every commitment
and proof entry port across both roles; receive selections cover every executable
PCS receive under the fixed public loop counts. Exact zero-trip bodies are
excluded. Duplicate, unknown or missing selections refuse. A public label targeting
several ports must select the same setup at each. Full configuration arrays,
including selection order, are bound into the `zkc.artifact-binding/1` root. Wire headers cannot
select or register keys. The [format contract](../../docs/compiler/artifact-format.md)
defines the full envelope and root.

The selected source RNG cannot be supplied explicitly. If its checked generated
input remains, the host issues it with zero budget. Transcript issuance is also
internal and cannot be injected. Capabilities bind actual role/session/entry;
entry policy checks the root instance, and nested transfer requires the actual
Runner parent argument view. Unrelated resources are preserved and never replaced
by the transcript.

`TRANSCRIPT_BUDGET` is a required canonical u64 decimal limit on transcript
**transitions** (observations plus challenges). It is not an RNG draw count.
There is no guessed default. Current authored repeated DLEQ needs 10 transitions;
committed two-factor at rank 3 needs 15. Exhaustion fails with retained reached
state. Selected RNG generations remain zero; its source challenges are counted
from normalized challenge events. A nonce commitment and response each consume
one transition, so each DLEQ nonce needs budget 2.

## Reports, limits and publication

Success emits JSON status `produced` or `accepted`, exit 0. A failure emits
`refused`, exit 1, with its phase and code, including actual backend rejection
codes such as `rejected:require`. All failure paths keep the reached V observation
prefix; no response is synthesized for a failed operation.

`timings` separates admission from key/input loading and runtime. Key loading
includes input parsing, canonical root binding and capability issuance. Runtime
includes proof read/write and final atomic publication. `proof_bytes` counts
written/consumed framing bytes; `candidate_bytes` records full V candidate length.
`messages` counts complete framed messages consumed or produced, not source
messages erased by construction. Runtime instruction/call/iteration counts and
resource state (generation, transitions, remaining `budget`, stage) are separate.
No private outputs, witness values, key material or nonce values are printed.
V observer values are public ordinary full wire bytes; configured VKs use their
full public canonical key encoding.

`Observed<B>` wraps any installed `WireBackend<Value = zkc_backends::Value>` and
delegates custody hooks and operations. It uses the checked origin manifest and
actual Runner instance/call/loop path to normalize original V requests/responses,
all explicit source message observations, and selected challenges. Source formal
role names remain unchanged by actual-role renaming. P private and recipe helper
operations are excluded from the V comparison. Transcript challenges normalize
to original `random.draw` with `selected_rng` input/successor. The public
primitive requests are not native source observation events.

Source/physical admission has its own 1 MiB byte ceiling. Host input/construction
JSON and proofs have 16 MiB ceilings; key reads use the backend wire ceiling.
An allocation-free scan checks JSON depth, node count and array width before
parsing; objects and scalar JSON kinds are refused. Logical-tree limits (root depth 0, depth 64, nodes 200000, array size 32768 and
16 MiB encoded bytes) apply. Hex is lowercase, even-length, with no prefix;
counts have no signs or leading zeroes. The installed runtime/backend retain their
instruction, stack, payload, group, rank and resource ceilings. The observer has
an explicit 16 MiB retained JSON-event ceiling and fails with
`exhausted:observer-bytes`. Message events are sized before their transcript
transition. Challenge request/challenge/response bundles and ordinary operation
request/response bounds are reserved before applying the backend operation.
Completed transitions therefore retain their full event records at this limit;
a failing apply retains its request without a fabricated response. Installed type
bounds may conservatively refuse before a smaller actual response would fit.
Trusted backend/type-bound violations are separate `observer-output-bound`
failures; these bounds are not a general process-memory guarantee.

Input binding plans loading-pool and entry operand charges before ordinary value
decoding or proving-key file reads. Both have the runtime's 64 MiB / 16,384-value
ceilings; a separate 256 MiB cumulative loading-work proxy includes retained
charges, configured key/ordinary wire bytes and every file read. Repeated
immutable keys share only after successful authentication of captured file bytes,
the expected material fingerprint and full configured VK. Each named path is
still read and hashed; every entry operand still counts toward admission. The
backend's size estimator and actual retained accounting share one definition.
Stable failures are `artifact-input-bytes-limit`, `artifact-input-count-limit`,
`artifact-input-work-limit` and `artifact-input-size-estimate`. They do not bound
wall time, importer scratch space or all process RSS.
Checker subprocesses have 120-second execution limits. Construction-check replies
are bounded to 4096 bytes, prepared source to 1 MiB, and the generic correspondence
checker including source maps to 4 MiB. Prepared functions/bindings are checked
against the authenticated construction, and its control declarations against
the original library.

Production writes a same-directory temporary file only after Runner success,
syncs it, and atomically renames it to the requested destination. Execution
failure leaves an existing complete proof untouched. File atomicity is covered;
parent-directory crash durability and setup ceremony honesty are not claimed.
There is no network service, hidden peer, shared witness, ordinal transcript tape,
whole-protocol crypto callback, FS security theorem or backend verification claim.

## Reproduce the host tests

Build the production CLI and explicit development-only fixture exporter:

```sh
cargo build --offline -p zkc-tools --bin zkc --example artifact_fixture
cargo test --offline --workspace --all-features
cargo clippy --offline --workspace --all-targets --all-features -- -D warnings
python3 crates/zkc-tools/tests/artifact_host.py \
  --zkc "$ZKC" --fixture-exporter "$FIXTURE_EXPORTER" \
  --compiler "$COMPILER_CHECKER" --lean "$LEAN_CHECKER" --output-dir "$OUTPUT"
```

The exporter creates OS-random development keys, public inputs and test witness
files under its chosen output directory. It is never called by either artifact
command. The tests use frozen authored compiler sources under
`tests/fixtures/artifact`, regenerate candidates, run separate producer/validator
subprocesses and retain actual command/observation receipts.

To compare exact native validator traces with the independent original-source
Lean reference and its separate public cryptographic service:

```sh
python3 crates/zkc-tools/tests/artifact_reference.py \
  --zkc "$ZKC" --fixture-exporter "$FIXTURE_EXPORTER" \
  --compiler "$COMPILER_CHECKER" --lean "$LEAN_CHECKER" \
  --reference-driver "$REFERENCE_DRIVER" --reference "$ARTIFACT_REFERENCE" \
  --primitive "$ARTIFACT_PRIMITIVE" --output-dir "$REFERENCE_OUTPUT"
```

The reference receives original source, descriptor, V inputs and proof only.
The service resolves complete public requests independently; native observer
logs do not supply the reference's decisions or challenges. This comparison
covers the recorded cases, not arbitrary protocol/security equivalence.


The explicit BLS12-381 Fr consumer can select
`spongefish0.7.4.keccak.bls12-381.fr64be/1`. Descriptor/root identity keeps this
construction distinct from Merlin. The Lean-owned `zkc.duplex-request/1` service
carries fully framed absorb bytes and exact 64-byte squeezes; it does not call
the native transcript adapter. See the [construction contract](../../docs/compiler/artifact-format.md#second-construction-over-bls12-381-fr).

## Public-operand implementations

The explicit dense `dalek-vartime/curve.msm` requires public operands. After
checking the public artifact profile, `CheckedBundle` checks implementation uses
through the actual admitted participant graph. Uses by any role other than the
descriptor-selected validator fail with `artifact-public-implementation-role`
before inputs, resources or proof bytes are accessed. Fixed zero-trip bodies are
excluded; shared local functions count for every reached role. Binding grants
only that validator a backend public-role policy, after public roots,
configuration and fresh resource issuance have been checked. Ordinary interactive
hosts and low-level artifact helpers receive no implicit grant. See the
[implementation contract](../../docs/runtime/public-msm.md).

## Independent native baselines and primitive service

`examples/artifact_baseline` independently executes the two pinned authored
algorithms (DLEQ and committed two-factor), using upstream Arkworks and Merlin
primitives directly. Its source digests identify the host's exact fixtures;
inputs, setup selections and root bindings use the current nominal formats.
It never invokes Runner, NativeBackend or the source interpreter. Development
nonces and fixtures remain explicitly public. Different algorithms are refused
rather than interpreted. Tests retain separate wire and logical encoding goldens,
statement/proof binding, setup selection and malformed-proof controls.

The public primitive service accepts nominal `zkc.public-primitive/1` requests,
raw Merlin `zkc.transcript-request/3`, explicit `zkc.duplex-request/1` and
`zkc.hash/1`. It has no profile-tagged request route, and a retired request tag
is refused. Frozen transcript KATs replay their authentic
historical bytes through the current raw-byte service; they do not revive a
historical source interpreter.

### Structured local bodies

Admitted participant artifacts may retain local `if`/`for` regions after native
helper expansion. The ordinary runtime executes them with selected-path effects,
finite index bounds, region frames, and affine resources. Source identity visits
both branches and loop bodies, including transitive helper dependencies; normalized
region SSA scopes and site coordinates are independent of local name spelling.

The current native construction profile can retain whole pure local bodies.
Selected-draw, resource-bearing, and cross-role recipe constructions have explicit
native refusal boundaries; ordinary runtime admission does not waive them.
The static full observer additionally refuses structured local bodies with
`artifact-observer-local-control-unsupported`, because an unconditional operation
manifest cannot represent their dynamic paths. Use `TraceMode::None` for admitted
pure local-control artifact execution; this omits diagnostic trace production and
does not claim trace equivalence. It does not suppress backend guards or failures.
The public primitive services support dynamic `curve.get` and `curve.length` for
BLS12-381 G1, Ristretto255, and BN254 G1/G2, with exact nominal and index checks.
