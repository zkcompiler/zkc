# Common-input inventory fixture

`boolean.*` and `custody-fields.*` are freshly emitted checked
source/original/interface triples. Both the outer and dormant inner Boolean
control contribute distinct input equivalence classes. The custody fixture
selects one shared ordinary Boolean field below a two-role affine prefix. Its
source field path is `[field(0)]`; the existing component map resolves it to
native input 2, independently of the custody components at inputs 0 and 1.
This semantic subject supplies no external construction or custody authority. Generation checks the
source/native association, independent native inventory reconstruction and exact
source inventory comparison before writing any fixture.

`zkc-common_interface-test` writes both triples when given this directory.
[The interface fixture script](../../../../scripts/regenerate-interface-fixtures.py)
runs it, together with the other compiler-produced interface fixtures, from a
named compiler build and recomputes the digest table below:

```sh
python3 scripts/regenerate-interface-fixtures.py build/compiler
```

The interface original digest binds the exact original bytes. The toolchain
identity binds the compiler's semantic sources; neither digest independently
proves source adequacy. A consumer testing schema structure takes the toolchain
identity as a fixture parameter, so a compiler edit that changes only that
identity needs no regeneration. Independent SDK tests must consume a fresh emitted
package and execute actual participants with an externally pinned input context.
This fixture supplies no input agreement, execution certificate or formal proof.

## Current fixture SHA-256

These hashes cover the exact retained bytes from the generator above.

| File | SHA-256 |
|---|---|
| `boolean.zkc` | `77d5eb5f80a516bc6466a6ec40223d28c72b75ed86cb1af9fbf44f47f16867ac` |
| `boolean.mlir` | `a6370d7c8fbca788da8a9e6f3ebf3744c88c431102ca7d490de064d7ada34e42` |
| `boolean.json` | `7d400afc468d36aa98d21cea7c03ebe20b4d5d99145eb0628098fd7c05f49277` |
| `custody-fields.zkc` | `7f860eafedb25f0ce4970c0381bac5dde69f306d439b6b5fe54f27609df13483` |
| `custody-fields.mlir` | `8ef8adb9f7f7706852f0c6662f6103c6aae2c953b7ab36a981bb1d807973413e` |
| `custody-fields.json` | `2fb1b346c3135b03d9febd6f46560799b2dc72bb398c05a0309b7348f38fd765` |

The SDK interface suite consumes the emitted custody fixture directly and checks
that the ordinary field maps to native input 2, after the two custody components.
Fresh compiler-to-SDK CPU tests separately check actual common-input admission.
External supply and capability admission keep their own policies.
