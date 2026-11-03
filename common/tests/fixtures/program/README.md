# Executable byte-language controls

`bytes.json` contains hand-authored UTF-8 program inputs. The `wire` is passed
unchanged to each reader; parsing and reprinting it first would lose controls
for whitespace, escapes, trailing input and invalid Unicode escapes. A wire is
one string, or ordered segments for inputs too large to keep literally: a string
segment is copied, and `{"repeat": item, "count": n, "separator": s}` writes
`item` n times, with `{i}` replaced by 0 to n - 1, separated by `s`.

Each case has exactly one expected result of decoding **and static admission**
with the standard contract context, never diagnostic prose:

- `admitted`: the normalized measures of the admitted program, its static
  instruction count and its cumulative descriptor charge;
- `refused`: the refusal class of the one violation the case isolates.

The classes, the bounds and the descriptor charge are defined in
[the byte language](../../../../docs/spec/formats/program-bytes.md). Expected
results are derived from that specification, not from either reader, and are not
expected results for syntax parsing alone, installation or execution. Refusal
codes and details remain reader-specific.

The corpus covers every instruction alternative in `zkc.program/0`, including
local versus participant control, origins, bindings, variants, services and
ordered message schemas. Negative cases mutate valid controls, including unused
functions and dormant branches. Every bound of the bounds table has a case at the
bound and one past it, each reaching its own bound first; scoping cases cover
sibling and nested participant bodies, duplicates within one body, untaken arms
and zero-trip loops.

Consumers:

- `compiler/test/program_bytes.py`, through the public C++ program codec and
  admission driver in its `--report` mode;
- `shared_program_byte_language_controls` in the Rust runtime's VM tests,
  through `Program::decode` and the standard contract context;
- independent readers may consume the same manifest without a compiler.

The corpus is bounded agreement evidence, not a proof of a reader or of
source-to-execution correspondence.
