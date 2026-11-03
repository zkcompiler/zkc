# Entry JSON node-ceiling controls

`nodes.json` contains hand-authored UTF-8 inputs at and one past the lexical
node ceilings of the [Entry carriers](../../../../docs/spec/formats/entry.md):
200,000 nodes for an interface document and 800,000 for a Host control
artifact. A node is an array, an object, a string (an object key included) or
a scalar token. Each `wire` uses the segment syntax of the
[program byte fixtures](../program/README.md): a string segment is copied, and
`{"repeat": item, "count": n, "separator": s}` writes `item` n times, with `{i}`
replaced by 0 to n - 1, separated by `s`. One case of each pair counts flat
scalars; the other mixes objects, keys, strings and literals.

Each case names its `reader`, `interface` or `host`, and one expected result:

- `node-limit`: the reader refuses with its node-ceiling refusal;
- `within`: the reader does not refuse for the node ceiling. These inputs are
  not interfaces or Host artifacts, so a reader refuses them later for another
  reason.

Expected results are derived from the ceilings, not from either reader. Refusal
codes remain reader-specific: the compiler's readers refuse with `source.limit`
"Entry JSON node limit exceeded", and the SDK's with `entry-interface-limit`.

Consumers:

- `compiler/test/host_entry.cpp`, through the interface document parser and
  `checkHostArtifact`;
- `crates/zkc/tests/entry_json_nodes.rs`, through `BoundInterface::read` and
  `FunctionInterface::deployment_interfaces` over packaged inputs.

The corpus is bounded agreement evidence for these two ceilings, not a proof of
either reader.
