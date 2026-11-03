# Target declarations

`evm.json` is the EVM target declaration, format `zkc.evm-target/0`: the
verifier ABI and selector, the pinned solc version and optimizer settings, the
forks and default fork, the deployment ceiling ranges and the revert classes.
The [EVM target specification](../../docs/spec/targets/evm.md#target-declaration)
defines its fields, rules and identity. It is separate from the logical
[catalog](../catalog/README.md).

Two validators check it independently:

- `generate.py` runs at the compiler's configure step. It checks every rule
  and writes `zkc/Target/Evm/Declaration.h.inc`, the compiler's fork, limit and
  revert tables. It uses only the Python standard library.
- `crates/zkc/build.rs` checks the same rules when the SDK's `evm` feature is
  built and writes the typed `zkc::evm_target` module.

`evm-validation-cases.json` lists edits of the declaration that both must
refuse, each naming the broken rule; `validation_cases.py` applies them. The
compiler's `evm-target-declaration` test runs them against the generator, and
the SDK's `unicode_tables` test runs them against the Rust build. Generated
tables are build outputs and are not checked in.

```sh
python3 common/targets/generate.py --source common/targets/evm.json
```
