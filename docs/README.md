# Documentation

zkc compiles `.zkc` source or Protocol IR into participant programs executed
by a shared Rust runtime. The [architecture](architecture.md) explains the system;
the [walkthrough](getting-started.md) compiles and runs a complete example.

## Reading routes

| Task | Start here |
|---|---|
| Write a protocol and select an Entry | [Language](language/README.md), [libraries](../libraries/README.md), [projects](../examples/projects/README.md) |
| Run an Entry or integrate an application | [Runtime and Hosts](runtime/README.md) |
| Work on the compiler | [Compiler](compiler/README.md) |
| Find exact syntax, IR or artifact rules | [Specification](spec/README.md) |
| Check implemented capabilities | [Status](status.md) |
| Assess proofs and tests | [Assurance](assurance.md), [formal models](../lean/docs/README.md) |
| Build, test or contribute | [Development](development/README.md), [tests](../common/tests/README.md) |
| Understand adopted choices or future work | [Rationale](rationale/README.md), [roadmap](roadmap.md) |

## Authority

`docs/spec/` owns native contracts and the mathematical laws they use.
`lean/docs/spec/` owns the independent Lean models; their theorem scope is in
[formal support](../lean/docs/support.md). Applying a model theorem to the native
implementation requires an explicit correspondence. A specification, compiler
check, test and security proof establish different claims.

Guides explain these contracts without redefining them. Component READMEs own
their APIs and procedures. [Status](status.md) records implementation coverage;
[roadmap](roadmap.md) records remaining work. Research proposals, review logs and
superseded documents stay outside this public reference. See the
[documentation guide](development/documentation.md) for maintenance rules.
