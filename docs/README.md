# Documentation

| Document | Content |
|---|---|
| [Status](status.md) | what the repository supports now and what it does not |
| [Development](development.md) | prerequisites, layout, commands, tests and CI |
| [The core language](spec/core/README.md) | the specification of the core language: its types and admission, its meaning, the declaration of a scheme, the package format and the stages |
| [The source language](../language/README.md) | the reference of the source language, its libraries and its conformance tests |

The guides of the Lean packages describe their modules, their tools and the statements of their
theorems:

| Guide | Content |
|---|---|
| [Compiler package](../lean/compiler/README.md) | the Lake package of the core and the frontend |
| [Core](../lean/compiler/Zkc/Core/README.md) | admission, construction, projection, the executor and their theorems |
| [Frontend](../lean/compiler/Zkc/Frontend/README.md) | the lexer, the parser, the checker, the emission to the core, the tools and the test driver |
| [Formal package](../lean/formal/README.md) | statements and proofs over the meaning of the core |

## Which document decides what

The [reference of the source language](../language/LANGUAGE.md) defines the source language, and
the [specification of the core language](spec/core/README.md) defines the core language. The
guides of the packages describe the implementation and do not redefine either language. The
[status](status.md) records what is implemented. Contributions follow
[the contribution guide](../.github/CONTRIBUTING.md).
