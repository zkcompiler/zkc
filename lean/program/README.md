# Program

Shared finite execution, typed regions, interpretation laws and shared algebraic data. The Interaction and Region core is Lean/Std-only; mathematical support uses Mathlib. No dependency on compiler IR, protocol proof engines or concrete applications.

See [architecture](../docs/architecture.md) for ownership, dependencies and extension rules.

Run `lake build` from this directory. Focused module builds use the package's full `Zkc.Program` import prefix. Tools and tests are separate targets in this package.
