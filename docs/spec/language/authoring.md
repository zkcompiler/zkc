# Source authoring services

The optional `zkc-source-lsp` serves the [development layout language](layout-execution.md) over standard LSP framing on stdin/stdout. It uses the same Source, Syntax and Language components as native checking. The `zkc-lsp` executable remains the separate MLIR server. Neither editor navigation nor formatting compiles MLIR or starts Lean.

## Build and configure

In the development shell:

```sh
cmake --preset dev -S compiler -DZKC_ENABLE_SOURCE_LSP=ON
cmake --build build/compiler-dev -j4 --target zkc-source-lsp
ctest --test-dir build/compiler-dev --output-on-failure -R '^(source-lsp|language-authoring)$'
```

Configure an LSP client to launch `build/compiler-dev/zkc-source-lsp`. For a project with imports, send an explicit module map in `initialize.initializationOptions`:

```json
{
  "modules": [
    { "module": "algebra", "uri": "file:///absolute/project/algebra.zkc" },
    { "module": "demo", "uri": "file:///absolute/project/demo.zkc" }
  ]
}
```

These files are captured at initialization. Open document text overlays that capture. An unconfigured open file uses its file-module header, or its filename stem when no header is present; the resulting name must satisfy ordinary module admission. Import dependencies must be configured or opened explicitly. There is no directory crawl or implicit project manifest discovery.

Every accepted edit or reopen recomputes an unconfigured document's module name from its current text. Removing a header restores the filename fallback. Configured module names remain authoritative: a conflicting edited header is a native diagnostic, not a replacement module mapping.

Clients report closed-file changes through `workspace/didChangeWatchedFiles`. This is the only reload path after initialization. Queries never read files. Closing a configured document restores the latest captured disk text; closing a standalone document removes it. A deleted configured file remains unavailable until a later file event successfully reloads it. Asset maps, live configuration replacement and persistent caches are outside this initial service profile.

## Requests and native information

The server implements initialize/shutdown/exit, open/change/close, cancellation, diagnostics, document symbols, definition, hover, completion and formatting. It defaults to UTF-16 positions and selects UTF-8 when the client advertises support. CRLF and non-BMP characters use the shared checked position conversion.

`language::Authoring` in the installed Language SDK answers the semantic requests over an immutable `CheckedProject`. Definitions come from resolved lexical and declaration references. Local completion respects visibility intervals and shadowing; it suggests names, not a guarantee that an affine value can be used again. Hover exposes native value types and protocol availability. It may report a retained spec as unavailable for assurance. A checked native project is not a verified security claim.

Displayed protocol signatures keep data and random-service parameters in their checked source order, including interleaved categories, matching positional call arguments.

Successful project checking retains each full syntax tree under its exact imported notation environment. Formatting uses that tree and the Syntax formatter's equivalence check. An invalid project still supplies recoverable header symbols, but semantic queries and formatting refuse unavailable information. The service does not guess expression grouping when imports are broken. Rename, whole-project references, proof actions and Lean companion navigation are not implemented.

The diagnostic `zkc/status` request takes `{ "textDocument": { "uri": "..." } }`. Its response contains the project `generation`, exact `capture` identity, `native` (`checked` or `invalid`) and `assurance` (`not-requested`, `unavailable` or `unknown`). These fields describe authoring state; they are not admission receipts or reusable proof identities.

## Revisions and cancellation

Document notifications run in order. Every accepted project edit creates a new immutable project generation, including changes to private helpers, imported notation and the absence or presence of specs. One compute worker shares the active generation's completed native analysis. It does not reuse semantic results across generations. This conservative cache includes all captured project inputs and fixed installation/build/limit context by ownership.

Multiple changes in one notification apply sequentially and commit atomically. Older document versions are ignored. A malformed edit marks the document unsynchronized, preserves the last complete bytes and requests a full-text change or reopen through a log notification. No semantic answer uses those preserved bytes as the current document. Signed LSP document versions are separate from internal immutable revision counters.

Each queued request owns its exact string or signed 32-bit integer ID and cancellation token. Duplicate outstanding IDs refuse; an ID can be reused after its terminal reply. Superseding edits cancel old jobs. Diagnostic and response publication check the originating generation while serialized with document changes. A cancelled analysis never fills a completed cache slot. Native work-budget charge points and parsing check cancellation; external LLVM work is not asynchronously interrupted.

## Bounds and validation

The service admits at most 256 source documents, 1 MiB per document, 8 MiB of active source and 8 MiB of captured disk source. The native checker retains its ordinary work, syntax and semantic limits. The coordinator permits 32 queued jobs and 32 outstanding requests, with one compute worker. Cancelled and superseded queued work is removed, releasing its capacity before a terminal cancellation reply; an in-flight job can retain its old snapshot until it stops.

Transport bounds are 8 KiB headers, 16 MiB message bodies, JSON nesting depth 64, 1 KiB string request IDs and 8 KiB URIs. Semantic request parameters are limited to 64 KiB and responses to 8 MiB. The input adapter rejects duplicate JSON keys, invalid string encodings, ambiguous numeric request IDs and batches before dispatch. Invalid framing terminates the connection. These bounded controls are not a claim of complete LSP conformance.

The [subprocess suite](../../../compiler/test/source_lsp.py) exercises real framing, lifecycle, positions, cancellation, stale publication, recovery and fresh-process comparison after dependency changes. The [native API suite](../../../compiler/test/language_authoring.cpp) checks resolved definitions, lexical shadowing, availability, formatting and cancellation. The Language SDK remains usable without MLIR.
