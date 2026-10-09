# Independent reference fixtures

These independently retained vectors support the native and formal checks below.

- `variants/history-contracts.txt` is embedded by `formal/Tests/Variant.lean`
  and included by the formal package's input manifest and reproduction checks.
  The compiler's native operation-contract tests also consume these vectors.
- `blocks/blocks.json` and `blocks/block-results.jsonl` are inputs and expected
  outputs for `formal/checks/check_tools.py`.
- `contracts/` records the current native conformance probe coverage and
  consumer-specific facet observations; see its README for the scope.
- `clean/air-control.json` is the output of the pinned Clean producer in
  `formal/integrations/clean` (`TestsClean/Control.lean`): exported relations
  and arenas, rows and Clean's residuals. The C++ and Rust native comparison
  consumes it; `just test-lean-clean` and `reproduce.py --with-clean` require it
  to be byte-identical to a fresh run. It comes from Lean and Clean, not from the
  native code it checks; replace it only with reviewed producer output.

Do not regenerate these fixtures from the implementation they check. The
optional formal package includes its required vectors without invoking the C++
compiler or Rust execution toolkit. Current native integration generates its
programs from mathematical MLIR and `.zkc` source in fresh report directories.

Native backend transcript vectors live under
`crates/zkc-test-support/fixtures/`, owned by the Rust workspace.
