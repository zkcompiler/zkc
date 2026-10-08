# Writing protocols

Write `.zkc` modules and select an Entry to compile and execute a protocol. The
Language implementation checks the source and emits mathematical MLIR for the
common participant compiler and Rust Host.

Start with the [walkthrough](../getting-started.md), then read the
[mathematical source guide](mathematical.md). The maintained
[Schnorr and Sumcheck projects](../../examples/projects/README.md) show reusable
libraries with separately authored clients.

| Task | Reference |
|---|---|
| Define types, helpers, roles, services and control | [Mathematical source](mathematical.md) |
| Compile, run, prove or verify an Entry | [Entry execution](entries.md) |
| Capture relation data and bind its meaning | [Relation Assets](relations.md) |
| Read exact typing, effects and Entry rules | [Mathematical language profile](../spec/profiles/source/mathematical-language.md) |

The compiler checks declared contracts and availability. A relation clause alone
adds no runtime guard or proof of satisfaction. Backend implementations must
satisfy their operation and representation contracts; a successful type check
does not infer cryptographic assumptions. [Status](../status.md) records supported
syntax and native capabilities, and [model guides](../guides/README.md) explain
the independent semantic foundations.
