# Executable table protocol profile

A finite interpretation of the generic typed source/direct-plan machinery for
native differential testing. This example uses fields F₂/F₇, original immutable
tables, ordered prefixes and complete state/events. It adds a closed one-variable
Sumcheck trace and toy natural-pair Merkle operations, not protocol security.

| Module | Responsibility |
|---|---|
| `Language` | Types, values, base table operations, complete handler and protocol operations |
| `Format` | Exact tagged-array sort/operation codecs and selected dependency profile |
| `Invocation` | Named input/state decoding and complete execution serialization |
| `Endpoint` | Persistent actor/phase wrapper, entry validation and complete-execution erasure |
| `Admission` | Consumer-selected send/draw interaction and all-reply phase-summary laws |
| `Optimization` | Identical-variable interpolation law supplied to generic region folding |
| `Tools.TableProtocol` | Installed source-relative checker and independent Lean runner |

The general all-ring table model and restriction/evaluation laws are reusable
through `Zkc.Polynomial.Table`. The example imports `Zkc.Source` and
`Zkc.Compiler` APIs; it does not implement another checking framework. The
maintained declaration audit includes every example module and an explicit
`Tests.TableProtocolAudit` audit.

```sh
lake build table-protocol Tests.TableProtocolAudit
.lake/build/bin/table-protocol check SOURCE PLAN
.lake/build/bin/table-protocol run SOURCE PLAN INPUTS
.lake/build/bin/table-protocol admit SOURCE PLAN table-round/1 CERTIFICATE
.lake/build/bin/table-protocol run-admitted SOURCE PLAN INPUTS table-round/1 CERTIFICATE
```

The native [compiler client](../../../compiler/README.md) gives a complete example.
Exact direct lowering is checked over decoded source and plan. Compiler decoding,
Rust allocation/kernels, challenge randomness and native code generation remain
outside this theorem. Differential execution checks that connection at a finite
scope.

The [physical client](../TablePhysical/README.md) additionally checks logical
folding against the original source before composing physical correspondence.
`Optimization` supplies one total field law; the reusable traversal and checker
live in `Zkc.Compiler.RegionFolding`. The direct executable above retains its
separate exact-lowering rule.

Optional phase admission is checked against the same decoded artifact. The
profile fixes role `trace` and a `ready → sent → ready` discipline; it supplies
no cryptographic randomness or endpoint projection claim. Both tree and compact
source use the maintained phase checker. `Tests.TableAdmission` instantiates its
artifact permission theorems with these summaries.

`table-endpoint/1` instead takes a consumer entry `["prover", phase]` and an
invocation state `["prover", phase, tableState]`. `admit-entry` checks this phase;
`run-entry` also checks actual state agreement before binding inputs.
`Tests.EndpointAdmission` connects accepted entry validation to the existing
artifact call/return theorems. This is a bounded local phase profile, not a
multi-role ownership or security proof. The two profiles use the shared
`Tools.SourceConsumer` driver with the independent vector-service consumer.
