# Browser engine

`zkc-web` builds the ordinary Rust engine as one `wasm32-unknown-unknown`
module. It adds an in-memory proof adapter over the Rust SDK, rather than a
second evaluator, compiler or proof format. Compile source packages with the
usual compiler before shipping them to a browser.

## Build and use

Use the repository's pinned Rust toolchain, the `wasm32-unknown-unknown` target,
and `wasm-bindgen-cli` **0.2.129**, matching this crate's manifest.

```sh
cargo build --locked --release --jobs 2 -p zkc-web --target wasm32-unknown-unknown
wasm-bindgen --target web --out-dir crates/zkc-web/web/pkg \
  target/wasm32-unknown-unknown/release/zkc_web.wasm
```

Serve `web/` over HTTP. `worker.js` demonstrates one admitted proof session in
one ordinary dedicated Worker. Send an `admit` message with `package` and `pin`
as `Uint8Array`s. The application must obtain the expected SHA-256 pin and setup
authority independently of downloaded candidate data. Send `prove` with
`public` and `witness` JSON document bytes, or `verify` with `public` and `proof`
bytes. Input schemas and readable values are the SDK's existing ones. Use
strings for large integers; the optional draw `budget` is checked as an unsigned
64-bit value before conversion to `BigInt`. Direct bindings take a `bigint`
within that range. The Worker also retains the raw `reportText` for lossless
diagnostic consumers.

```js
const worker = new Worker('/zkc/worker.js', { type: 'module' });
worker.postMessage({ id: 1, operation: 'admit', package: packageBytes,
  pin: authorizedPin });
// After admission succeeds:
worker.postMessage({ id: 2, operation: 'prove', public: publicJSON,
  witness: witnessJSON, context: applicationContext });
// Check report.success. For verification require report.accepted === true.
```

`ProofSession` is also directly available from the generated ES module. Its
constructor accepts bounded JSON options: `operation` (`both`, `prove` or
`verify`), the existing SDK `capacity` record, `package_bytes`, `external_work`,
and explicit `allow_authored` binding permission. Defaults retain the SDK's
strict transcript binding. Optional authority bytes use
`zkc.entry-setups/0`; `setSetup(slot, bytes)` supplies material for declared,
independently pinned setup slots. Material never grants authority. Setup copies
are bounded in aggregate by the selected value budget and checked by SDK
preflight before execution.

Returned arrays are owned copies. Reports preserve diagnostics on ordinary
execution failure; incomplete proofs and outputs are withheld. An absent
verification decision is not acceptance. Call `dispose` and generated `free`
when finished. A trap or abort can bypass Rust cleanup: terminate and replace
the Worker. No rollback or reusable session is promised after a trap.

## Execution and limits

The adapter disables the engine's default `parallel` feature. Numerical work
runs inline; no Rayon pool, shared memory, browser threads or cross-origin
isolation is required. Native SDK applications retain owned parallel execution
by default. Cargo features are additive: build this crate separately from
workspace consumers that enable parallelism. Browser entropy support belongs
to this final adapter. The pinned C-backed blst provider is included; the
adapter does not substitute providers or change package bytes.

This first facade exposes proof calls, not the filesystem/project CLI or source
entry functions. File references are refused by the SDK decoder's absent
resolver. It does not add a network or filesystem capability. Managed capacities
bound their documented payload/work scopes, not the entire Wasm heap, JS byte
copies or provider-private allocations. `wasm32` address space and `usize`
limits also apply; native capacities need not all fit a browser. This profile
uses the default target features, without a separate SIMD or threaded build.

## Manual integration check

No browser download or new CI job is implicit. With Playwright **1.64.1** and
its Chromium installed separately, prepare a directory containing `schnorr/`
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
