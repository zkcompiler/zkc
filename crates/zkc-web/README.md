# Browser engine

`zkc-web` builds the ordinary Rust engine as one `wasm32-unknown-unknown`
module. It adds an in-memory proof adapter over the Rust SDK, rather than a
second evaluator, compiler or proof format. Compile source packages with the
usual compiler before shipping them to a browser.

## Build and use

Use the repository's pinned Rust toolchain, the `wasm32-unknown-unknown` target,
and `wasm-bindgen-cli` **0.2.129**, matching this crate's manifest.

```sh
cargo build --locked --profile web --jobs 2 -p zkc-web --target wasm32-unknown-unknown
wasm-bindgen --target web --remove-name-section --remove-producers-section \
  --out-dir crates/zkc-web/web/pkg target/wasm32-unknown-unknown/web/zkc_web.wasm
```

Serve `web/` over HTTP with JavaScript MIME types for `.js` and `.mjs`.
The `web` profile uses thin LTO and one code generation unit; ordinary native
release builds are unchanged. To deploy the optional SIMD variant, build it in
a separate target directory and generate matching glue:

```sh
CARGO_TARGET_DIR=target/web-simd RUSTFLAGS='-C target-feature=+simd128' \
  cargo build --locked --profile web --jobs 2 -p zkc-web --target wasm32-unknown-unknown
wasm-bindgen --target web --remove-name-section --remove-producers-section \
  --out-dir crates/zkc-web/web/pkg-simd \
  target/web-simd/wasm32-unknown-unknown/web/zkc_web.wasm
```

Both artifacts include the same provider support. Goldilocks base-field packing
and batched Keccak have two-lane Wasm SIMD implementations in the pinned
Plonky3 version; extension fields and other field families need not use SIMD.
Runtime provider selection restricts support without removing linked code.

The public `ProofClient` owns one dedicated Worker and admitted session:

```js
import { ProofClient } from '/zkc/client.mjs';

const client = new ProofClient();
try {
  await client.admit({ package: packageBytes, pin: authorizedPin,
    options: { providers: ['arkworks', 'blst', 'dalek', 'halo2curves', 'plonky3'] } });
  const proved = await client.prove({ public: publicJSON, witness: witnessJSON,
    context: applicationContext, budget: '18446744073709551615' });
  if (!proved.report.success) throw new Error(proved.report.error);
  const checked = await client.verify({ public: publicJSON, proof: proved.proof,
    context: applicationContext });
  if (checked.report.accepted !== true) throw new Error('verification refused');
} finally {
  client.dispose();
}
```

The application obtains the expected SHA-256 pin and setup authority independently
of downloaded candidate data. Public/witness JSON documents use the SDK's input
schemas and readable values. `admit` accepts optional `authority` bytes in
`zkc.entry-setups/0`; `setSetup(slot, materialBytes)` supplies material for a
declared, independently pinned slot. Material never grants authority. Setup
and named input copies share the selected SDK byte budgets. `setInput(name,
materialBytes, callOptions)` binds opaque bytes to an exact name for the existing
SDK input-reference decoder. For an admitted package with setup authority:

```js
await client.setSetup('main', verifierKeyBytes);
await client.setInput('pk', proverKeyBytes);
const witnessJSON = new TextEncoder().encode(JSON.stringify({
  pk: { file: 'pk', fingerprint: expectedProverKeyFingerprint },
}));
```

The SDK imports and checks the material fingerprint and setup association.
`setSetup` supplies a verifier key for an authorized slot; `setInput` supplies
named input bytes without granting setup authority. Both use the same queue,
snapshot/consuming-transfer rules and per-call controls as proof calls. Rust
retains immutable input bytes, bounds aggregate setup and input storage, and
allows at most 1,024 input names of at most 4,096 UTF-8 bytes each. A rejected
replacement in Rust invalidates the previous binding. Supply a valid replacement
before retrying; there is no fallback to previous material.
Replacing a named input clears cached prover imports before validation; replacing
a setup clears its verifier and prover imports. The SDK bounds retained numerical
material separately by the admitted value-byte ceiling. Cache pressure evicts or
bypasses retention while each call still authenticates, charges and authorizes
its own inputs.

The constructor options accepted by the generated `ProofSession` also include
`operation` (`both`, `prove`,
`verify`), the existing SDK `capacity` record, `package_bytes`, `external_work`,
and `allow_authored`. The provider set is fixed at admission; a different
installation requires a fresh Worker and admission. The SDK checks actual
compiled provider support and exact package bindings without reselection.

`ready` resolves after module initialization; callers may queue admission before
it resolves. Every method returns a promise except the immediate lifecycle
operations `dispose()` and `terminate()`. Calls resolve to reply objects; SDK
refusals reject with `ProofClientError`, whose `refusal` preserves the SDK's
`code`, `phase` and logical input `path`. An ordinary unsuccessful execution
resolves with its diagnostics. Require `report.success` and, for verification,
`report.accepted === true`. Keep `reportText` for lossless diagnostic integers:
parsed JSON numbers may exceed JavaScript's exact range. Pass `budget` and
`external_work` as `bigint`, canonical decimal strings or safe integer numbers.
The client preserves the complete unsigned 64-bit range. Byte lengths,
`package_bytes` and capacity size fields must fit wasm32. SDK capacity semantics
and hard ceilings remain independently enforced by Rust.

Inputs are borrowed by default: the client snapshots the supplied byte views at
enqueue, leaving caller buffers reusable. For an explicit consuming transfer:

```js
await client.prove({ public: disposablePublic, witness: disposableWitness },
  { consume: true });
```

Consumption detaches the entire backing buffers immediately when enqueued,
including aliases outside a supplied subview. Queue/argument refusals happen
before consumption. Consumed input is not restored on cancellation or failure.
Shared and detached buffers are refused. Transport uses owned transferable
buffers; crossing the JS/Wasm ABI still copies bytes. Returned proof/output
arrays are owned copies. The Worker holds the generated result through getter
copies and successful transferable publication, then calls `result.free()`.
Publication does not guarantee delivery to the client.

The client dispatches at most one call at a time. Defaults allow eight queued
requests and 64 MiB of pending byte buffers, including the active request;
`maxQueue` and `maxPendingBytes` configure these bounds. Consuming subviews
charge their complete backing buffers. These transport limits do not meter JS
object overhead, outputs, compiled code, Wasm memory or provider allocations.
Every request has an enqueue-to-reply deadline (default `timeoutMs: 120000`,
also configurable per call). A queued timeout removes only that request. An
active timeout means completion is unknown: it terminates the Worker and rejects
all pending calls. No call is automatically replayed.

An optional per-call `signal` removes a queued request on abort. An active
synchronous Wasm invocation cannot be cooperatively interrupted: cancellation
settles after its reply, discarding the result. `terminate()` hard-cancels the
Worker and every pending call. `dispose()` does the same and permanently closes
the client. Traps, Worker errors, message decoding errors and failed delivery
also discard the session. Rejected lifecycle calls carry `fatal` and
`completion` (`not-started`, `known`, `unknown`); uncertainty never licenses a
retry with the same invocation effects.

`await client.recycle()` requires an idle client. It terminates the old Worker,
increments the session generation and initializes a fresh Worker using the
cached `WebAssembly.Module`. It also works after a fatal failure, provided the
client has not been disposed. Packages, setups, inputs and authority are not replayed;
call `admit` again. `compiledModule` and the resolved `variant` can seed another
client with `{ compiledModule, variant }`. Cached code does not retain mutable
Wasm memory, admitted state or authority. Recycling is explicit; logical SDK
release and the Wasm memory high-water mark remain different quantities.

The admission reply includes `timings.package_capture_ms` and
`timings.package_admit_ms`, parsed from the generated session's `timings` JSON
getter and validated before publication. They measure separate Rust intervals
and exclude module loading, JS/Wasm argument conversion and message transport.
Proof and verification replies preserve `report.timings` and the complete
`reportText`. These milliseconds describe separate intervals:

- `memory_preflight_ms` includes document decoding, codec feasibility and
  output-key preflight. It excludes the Host's invocation preparation.
- `execute_cleanup_ms` includes Host preparation, input-key imports,
  reconstruction, execution and cleanup.
- `output_encode_ms` measures result encoding.
- `diagnostics_ms` measures diagnostics construction, excluding the final
  report's JSON serialization.

These intervals do not constitute a full end-to-end breakdown. The Worker's
`milliseconds` measures the inclusive synchronous call through JS/Wasm conversion,
SDK preflight, execution and report construction; getter copies and publication
follow that measurement.

## Direct Worker and generated bindings

The direct dedicated Worker API uses the same checked request schema. Await
each reply; it has no Worker-side request queue. Start with initialization:

```js
const worker = new Worker('/zkc/worker.js', { type: 'module' });
worker.postMessage({ id: 1, generation: 1, operation: 'initialize',
  variant: 'portable' });
// After initialization succeeds:
worker.postMessage({ id: 2, generation: 1, operation: 'admit',
  package: packageBytes, pin: authorizedPin, options: { providers: ['plonky3'] } });
// Subsequent operations: setup, input, prove, verify, dispose.
// Named input: { id: 3, generation: 1, operation: 'input', name: 'pk',
//                material: proverKeyBytes }
```

IDs are strictly increasing positive safe integers. Each Worker freezes its
positive safe integer generation at initialization and rejects stale generations,
ID reuse and reinitialization. Replies echo `id` and `generation`; malformed
metadata is omitted. Successful initialization returns `variant` and a cloneable
compiled `module`, which another fresh Worker may receive at initialization.
Direct `dispose` frees any session and closes the Worker after its reply,
including before admission or after an ordinary admission refusal. A
direct consumer owns timeouts and settlement after Worker loss; use `ProofClient`
for that lifecycle handling. Do not send client-owned Workers unrelated messages.

The portable glue path is `./pkg/zkc_web.js` and the SIMD glue path is
`./pkg-simd/zkc_web.js`, each paired with its own `zkc_web_bg.wasm`. Portable is
the default. `{ variant: 'simd' }` probes SIMD support before loading or
instantiation and refuses unsupported engines. `{ variant: 'auto' }` chooses
once from that probe and requires both artifacts to be deployed. Module loading
or admission failure never triggers fallback. SIMD artifacts must be built with
matching installation support; this client does not build or attest them.

`ProofSession` remains directly available from the generated ES module, with
synchronous methods. Such consumers own validation before glue conversion,
`dispose()`/generated `free()`, result custody and instance replacement after a
trap. The Worker validates all arguments before entering glue so a late JS
conversion error cannot strand earlier argument allocations. No Rust rollback
or destructor cleanup is promised after abort, trap or hard termination.

## Execution and limits

The adapter disables the engine's default `parallel` feature. Numerical work
runs inline; no Rayon pool, shared memory, browser threads or cross-origin
isolation is required. Native SDK applications retain owned parallel execution
by default. Cargo features are additive: build this crate separately from
workspace consumers that enable parallelism. Browser entropy support belongs
to this final adapter. The pinned C-backed blst provider is included; the
adapter does not substitute providers or change package bytes.

This facade exposes proof calls. Input documents resolve existing SDK reference
forms through the explicitly supplied `setInput` name map. Missing names are
refused; a `file` field grants no network or filesystem capability. JavaScript
passes opaque bytes and the shared SDK owns decoding and key import. Managed
capacities bound their documented payload/work scopes, not the entire Wasm heap, JS byte
copies or provider-private allocations. `wasm32` address space and `usize`
limits also apply; native capacities need not all fit a browser. The default artifact
uses portable target features. A separately deployed SIMD artifact is selected
only before initialization; browser numerical threading is not provided.

## Manual integration check

No browser download or new CI job is implicit. With Playwright **1.64.1** and
its Chromium or Firefox installed separately, prepare a directory containing `schnorr/`
and `fri-1024/`. Each contains an ordinary compiler `entry.zkpkg`, schema-valid
`public.json`, `witness.json`, and the independently recorded package SHA-256
in `pin.txt`. The existing Schnorr project and protocol benchmark's 1,024-row
FRI case supply these fixtures. Generated inputs and proofs are test artifacts.

```sh
cargo build --locked --release --jobs 2 -p zkc-web --example memory
ZKC_PLAYWRIGHT=/absolute/path/to/playwright/index.mjs \
  node common/tests/browser/roundtrip.mjs crates/zkc-web/web \
  /absolute/path/to/fixtures target/release/examples/memory
```

The check uses identical package and input bytes in both targets, cross-verifies
proofs in both directions, checks repeated calls and negative controls, and
writes complete diagnostics and Worker call timings. Browser times include
Wasm argument marshalling, SDK input decoding, execution and report construction;
they exclude module loading, admission, message transfer and getter copies.
Native times use the same SDK facade calls without JavaScript marshalling.
They are feasibility observations, not native/browser performance equivalence.
The test helper is not a second benchmark framework.

`ZKC_BROWSER=chromium|firefox` selects the engine (default `chromium`);
`ZKC_WEB_VARIANT=portable|simd` selects the deployed artifact (default `portable`).
The result records the actual browser version and selected variant. Only the
Playwright driver version is pinned here. Run the command once per engine or
variant to check another deployment.

`ZKC_BROWSER_FIXTURES=name1,name2` selects a comma-separated list of fixture
directories instead of the default pair. Each fixture can also provide
`options.json`, `authority.json`, `setups.json` (an array of `{slot, path}`), and
`inputs.json` (an array of `{name, path}`). Paths identify material files read
by the Node test driver. The selected native example must consume the same
optional files for cross-verification. Additional fixtures use ordinary
admission, binding and proof calls; witness-specific negative controls remain
with the existing Schnorr and FRI fixtures.

Worker envelope and trap-reporting controls also run without Wasm or a browser:

```sh
node common/tests/browser/worker.mjs
node common/tests/browser/client.mjs
```
