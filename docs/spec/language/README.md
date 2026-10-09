# Source language contract

These native contracts define `.zkc` source and its checked translation. The
[language guide](../../language/README.md) introduces syntax with examples.

| Chapter | Owns |
|---|---|
| [Definitions and types](definitions.md) | Capture, names, static terms, mathematics, permissions, callables and bounds |
| [Protocol bodies and relations](protocols.md) | Ordered control, availability, services, composition, repetition, completion and specification clauses |
| [Entry declarations](entries.md) | Closed jobs, participants, construction, selected results and setup associations |
| [Operation bindings](bindings.md) | Native nominal types, operation applications and physical selection |
| [Translation](translation.md) | MLIR emission, independent source comparison and the immutable checked original |

The retained [interface and package](../formats/entry.md) are serialized
contracts. [Entry admission and calls](../runtime/entries.md) define the Host
boundary. Source declarations record intent and bindings; a relation clause does
not insert an executable guard or prove satisfaction.
