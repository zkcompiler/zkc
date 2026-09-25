# Bounded entry selection for compact protocol families

These fixtures exercise the [bounded carrier contract](../../../docs/compiler/interactive-execution.md#input-selected-families)
under the [family semantics](../../../docs/spec/profiles/source/families.md).
They are not complete BP+ or OpenVM implementations.

An authored instance binds a protocol parameter with an ordinary stored local
function for each actual role:

```text
parameters (rounds = ingress(10, P = Select(metadata), V = Select(receivedMetadata)));
```

The Source model uses `ParameterBinding = variant<string, FamilyIngress>`.
Numeric strings remain static counts. A dynamic carrier binding is:

```json
["rounds", ["ingress", "10", [["P", "Select", ["metadata"]], ["V", "Select", ["receivedMetadata"]]]]]
```

The ordered argument list names a unique subset of that role's actual entry
ports. Selected values must be serializable and match the stored selector's
input types exactly; its sole result is `index`. The interface does not pass
unlisted witness or capability ports to the selector. It also does not assert
that all serializable fields are public: which fields constitute public shape
metadata is the adapter's contract. All roles of the instance need exactly one
selector, and projected copies carry the same descriptor. No external selector
body, forward reference to a later protocol value, implicit peer input, or
capability argument is admitted.

The bound is a canonical natural at most 1,048,576. Each runner executes its
selector once after admission of its own entry inputs, before any protocol
instruction. Multiple parameters are selected in lexical parameter-name order.
The result must fit the declared bound; normal native work, call, iteration and
value budgets still apply. Ordinary arithmetic overflow or selector rejection
is a failure, not a default count. Entry-frame identity stays immutable; selected
counts are exposed by `Runner::selected_parameters()` and attached to subsequent
execution frames. Existing `EntryRole.parameters` contains static bindings.

`Count.Parameter` survives common MLIR, participant projection and the carrier.
Participant loop counts use `["parameter", "rounds"]`; fixed projected loops
retain the existing numeric-string encoding. MLIR `argument_names` binds
selector references to entry SSA arguments, and export rewrites those references
with the ports. A dynamic loop never causes compilation of one body per count.

The joint native driver and joint Lean reference explicitly fail with
`interactive-family-disagreement` when local counts differ. Independent role
execution retains the role's own selected count. Agreement on a count does not
establish equality of all metadata bytes; the protocol/adapter must establish
any stronger agreement it needs.

This gate supports entry selection only. Dynamic families cannot have instance
dependencies or be selected by a parent's dependency, and dynamic participant
calls are refused. Static execution/provenance expansion and transcript
construction refuse unresolved family inputs. Arbitrary global branching,
symbolic construction provenance and a native refinement theorem are outside
this gate.

| Fixture | Exact input contract |
| --- | --- |
| `counted.pir` | Each role supplies one actual index in 0..10. |
| `bp-shape.pir` | Each role supplies original 32-byte encodings in flattened index arrays; every index is a byte, commitment count is 1..16, and L/R arrays each contain `6 + ceil(log2(count))` encodings. Padding handles nonpowers of two. This checks lengths and bytes, not point/scalar/subgroup validity or a BP+ proof. |
| `openvm-shape.pir` | Each role supplies actual metadata `[rounds, width]`; width must be one and rounds 0..10. This is a minimal ingress contract, not a full AIR/VK metadata parser or OpenVM verification. |
| `private-inputs.pir` | Selectors read only count indices. Ordinary protocol code doubles a private witness and consumes one RNG draw each round; the sample is discarded so output/resource comparisons do not assume identical random tapes. |

`refusals.json` names the identifier each malformed family control is refused
with, by the rule it breaks. The cross-build test holds the compiler and the
Lean reader to it on the same source mutations; the native reader's own
controls, which mutate compiled participants rather than source, read the same
table.

Run `.venv/bin/pytest -q tests/protocol/test_input_families.py` after building
`build/compiler/{zkc-compile,zkc-opt}`, `target/release/zkc`, and
`formal/.lake/build/bin/interactive-protocol`. The test compiles each fixture
once, checks the independent Lean projection, executes multiple actual counts
in Rust and Lean, checks malformed controls, and preserves carrier hashes and
MLIR/node-count evidence under `build/reports/tests/input-families-*`.
