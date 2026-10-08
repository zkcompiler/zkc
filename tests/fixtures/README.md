# Independent reference fixtures

These vectors remain independently useful after retirement of the old source
Frontend and source-bound execution tests.

- `variants/history-contracts.txt` is embedded by `formal/Tests/Variant.lean`
  and included by the formal package's input manifest and reproduction checks.
  The compiler's native operation-contract tests also consume these vectors.
- `blocks/blocks.json` and `blocks/block-results.jsonl` are inputs and expected
  outputs for `formal/checks/check_tools.py`.
- `contracts/` records the current native conformance probe coverage and
  consumer-specific facet observations; see its README for the scope.

Do not regenerate these fixtures from the implementation they check. The
optional formal package includes its required vectors without invoking the C++
compiler or Rust execution toolkit. Current native integration generates its
programs from mathematical MLIR and `.zkc` source in fresh report directories.

Native backend transcript vectors now live under
`crates/zkc-test-support/fixtures/`, owned by the Rust workspace. The former
source-bound artifact-identity KAT has been retired with that format.
