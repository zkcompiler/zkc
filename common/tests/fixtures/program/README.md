# Executable byte-language controls

`bytes.json` contains hand-authored UTF-8 program inputs. The `wire` string is
passed unchanged to each reader; parsing and reprinting it first would lose
controls for whitespace, escapes, trailing input and invalid Unicode escapes.
`admitted` is the expected result of decoding **and static admission** with the
standard contract context. It is not an expected result for syntax parsing
alone, installation or execution.

The corpus covers every instruction alternative in `zkc.program/0`, including
local versus participant control, origins, bindings, variants, services and
ordered message schemas. Negative cases mutate valid controls, including unused
functions and dormant branches. Refusal identifiers are reader-specific; the
shared contract is the admission decision. Neither reader generates expected
answers for the other.

Consumers:

- `compiler/test/program_bytes.py`, through the public C++ program codec and
  admission driver;
- `shared_program_byte_language_controls` in the Rust runtime's VM tests,
  through `Program::decode` and the standard contract context;
- independent readers may consume the same manifest without a compiler.

The exact format is specified in `docs/spec/formats/program-bytes.md`.
The corpus is bounded agreement evidence, not a proof of a reader or of
source-to-execution correspondence.
