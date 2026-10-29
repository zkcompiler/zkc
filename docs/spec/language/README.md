# Source language contract

These native contracts define `.zkc` source and its checked translation. The
[language guide](../../language/README.md) introduces syntax with examples.

| Chapter | Owns |
|---|---|
| [Source text and names](lexical.md) | Exact UTF-8, Unicode identifiers, mathematical tokens and pinned profile |
| [Layout syntax](layout-syntax.md) | Immutable source revisions, lossless layout parsing, notation environments, recovery and formatting |
| [Mathematical notation](notation.md) | Descriptors, fixity, delimiter calls, scope, inspection and bounds |
| [Definitions and types](definitions.md) | Capture, names, static terms, mathematics, permissions, callables and bounds |
| [Protocol bodies and relations](protocols.md) | Ordered control, availability, services, composition, repetition, completion and specification clauses |
| [Entry declarations](entries.md) | Closed jobs, participants, construction, selected results and setup associations |
| [Source claims](claims.md) | Versioned wire requests, Entry/target/site resolution and optional Lean handoff |
| [Operation bindings](bindings.md) | Native nominal types, operation applications and physical selection |
| [Written source AST](source-ast.md) | Syntax retention, structural addresses and the source-correspondence input |
| [Translation](translation.md) | MLIR emission, independent source comparison and the immutable checked original |

The retained [interface and package](../formats/entry.md) are serialized
contracts. [Entry admission and calls](../runtime/entries.md) define the Host
boundary. Source declarations record intent and bindings; a relation clause does
not insert an executable guard or prove satisfaction.
