# Shared declaration source

`declarations.json` is authored neutral data, not a generated snapshot. It owns
the built-in declaration facts in [`zkc.contract-declarations/0`](../../docs/spec/formats/contract-declarations.md).
Edit this source when changing identities, kinded signatures, requirements,
permissions or mathematical facets. Array order is declaration order; nominal
identity determines meaning. No row installs executable code or a formal interpretation.

The compiler's configure step checks exact JSON shapes and projects ordinary
TableGen records. `zkc-tblgen` independently checks declaration formation before
generating native C++ data and MLIR adapter inputs. The Rust `zkc-catalog` build
checks the same source independently and emits static typed tables in `OUT_DIR`.
Rust does not run Python or LLVM; the compiler does not run Cargo. Generated
records and tables are build outputs and are not checked in.

The source format is intentionally explicit. Scope references, signature-family
tags and facets remain data rather than authoring-class privileges. Backend
installation, executable behavior and supported interpretation profiles have
their own owners. Native contribution declarations are separately admitted and
are included in the installed exported inventory; adding one does not silently
change the built-in Rust installation.
