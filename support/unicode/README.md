# Source-name Unicode data

This directory owns the shared inputs for the Unicode 17 source-name profile.
[manifest.json](manifest.json) pins the five upstream UCD files, their source
URLs and SHA-256 hashes, the explicit identifier additions, and the C++ and Rust
normalizer releases. The unmodified data is distributed under
[Unicode License v3](LICENSE.txt). The manifest records the license's source and
hash as well. The C++ normalizer is MIT-licensed utf8proc 2.12.0; Nix fetches its
exact source archive using the pin in this manifest.

`generate.py` uses only the Python standard library. It verifies the raw inputs
and emits private C++ tables during the build. Rust's build-time reader uses the
same files independently. Generated tables are not source-controlled, and no
runtime needs Python or UCD files. Native CMake builds must provide the exact
utf8proc CMake package; the Nix development shell and compiler package provide it.
Generation and Nix package builds require no network access after fetching the
pinned dependencies.

Identifiers use XID_Start plus underscore, XID_Continue plus U+2080–U+2089, and
exclude Default_Ignorable_Code_Point and Bidi_Control. The Names API checks this
membership before NFC. Symbol candidates use non-ASCII Sm outside those classes;
delimiter candidates use reciprocal non-ASCII BidiBrackets pairs with Ps/Pe
categories. Both APIs then check NFC using the pinned mature normalizer. The
normalizer's newer repertoire never supplies classification. Sum and product
remain symbol tokens; their declaration reservation belongs to the syntax owner.

The source-profile identity is `zkc.source-names/0:` followed by the lowercase
SHA-256 of the exact manifest bytes. Compiler build identity additionally hashes
the raw files, generator and license. A profile update must change all readers
and their fixtures together. Source admission and native ordinal/hex encodings
are exposed by [Names.h](../../compiler/include/zkc/Language/Names.h).

## Focused checks

From the repository root, with LLVM 23 and utf8proc 2.12.0 installed:

```sh
cmake -S compiler/test/names -B build/names -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_DIR=/path/to/llvm/lib/cmake/llvm \
  -Dutf8proc_DIR=/path/to/utf8proc/lib/cmake/utf8proc
cmake --build build/names --parallel 4
ctest --test-dir build/names --output-on-failure
python3 compiler/test/names/sdk.py --output build/names-sdk \
  --llvm-dir /path/to/llvm/lib/cmake/llvm \
  --utf8proc-dir /path/to/utf8proc/lib/cmake/utf8proc
```

The focused C++ test checks all Unicode scalars against independent raw-data
readers, all 20,034 normalization rows (five NFC equations each), malformed UTF-8,
non-NFC ordering, Unicode 18 drift, labels and bounded reversible encodings.
Python controls reject damaged hashes, unsupported profiles and malformed or
overlapping data. SDK checks build static/shared Names libraries with the
production export configuration and independently link clients without MLIR.
They cover exact-version discovery and missing/incompatible dependencies. The
full compiler and installed compiler suites remain separate integration checks.

For cross-language comparison, `generate.py --output /tmp/profile.json --json`
emits candidate ranges. `zkc-language_names-test --dump-profile` emits admitted
ranges as decimal `first..last` lines in start, continuation and symbol sections,
each terminated by `;`, followed by decimal `opener:closer` pairs. The latter
includes NFC filtering and is suitable for comparison with the independent Rust
implementation.
