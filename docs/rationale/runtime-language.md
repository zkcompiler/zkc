# Rust owns the runtime and its backend integration

The [architecture](../architecture.md#5-rust-tools-execution-and-backend-adapters)
uses Rust for execution, artifact tooling and backend adapters. C++ owns the
compiler. Runtime language is independent of interpreter versus generated
execution and of whether deployment installs the compiler or checker.

## Alternatives

A C++ runtime can preserve the same admission, ownership and formal contracts.
It is attractive when the dominant consumers and kernels already expose C++
interfaces. The selected Rust backend libraries instead give the current Rust
runtime direct typed integration and avoid an extra adapter for each boundary.

| Consideration | Rust runtime | C++ runtime |
|---|---|---|
| Buffer and resource ownership | Safe Rust checks borrowing and lifetimes across supported APIs; unsafe/native boundaries remain obligations | RAII and move-only interfaces support disciplined ownership; borrowing/alias restrictions require additional discipline and checking |
| Selected Rust backends | Direct typed library calls | Rust backends remain usable through an adapter; using them still requires Rust builds and a language boundary |
| C++/GPU kernels and MLIR-generated native code | Requires suitable foreign-call and ownership contracts | More direct integration with C/C++ interfaces |
| Build and maintenance | Cargo plus CMake and cross-language integration | Fewer zkc implementation-language boundaries; Lean and any Rust backend dependencies remain |
| Native proof route | Aeneas provides a documented route for a safe Rust subset to Lean; actual-wrapper suitability is untested | Common realization contracts still apply; choose and assess the concrete implementation-proof route |
| Performance and deployment | No language-level speedup established; can deploy without compiler/checker installations | No language-level speedup established; can also deploy without compiler/checker installations |

Rust borrowing and ownership support the custody-sensitive core without a
garbage collector. C++ RAII and move-only interfaces also support disciplined
resource management. Neither proves cache keys, cryptographic resource reuse
or constant-time behavior. No performance advantage follows from the language
choice alone. An optional native proof must connect the actual implementation
to its contract; using Rust does not supply that proof. See
[Rust ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html),
[C++ resource management](https://isocpp.github.io/CppCoreGuidelines/CppCoreGuidelines#S-resource)
and the [Aeneas scope](https://github.com/AeneasVerif/aeneas#targeted-subset-and-current-limitations).

Compiler-specific tools stay with their C++ libraries. A helper does not need a
Rust wrapper simply for language consistency. Foreign kernels retain explicit
ABI, lifetime, error and ownership obligations.

## Reopen when

Dominant kernels and consumers are C++, or the Rust boundary requires substantial
copying, unsafe glue or proof friction. Compare the same plans, algorithms,
kernels and failure/state behavior before changing language ownership.
