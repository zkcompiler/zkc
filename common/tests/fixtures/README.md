# Independent reference fixtures

These independently retained vectors support the native and formal checks below.
`projects/` contains source clients for language features and library regressions;
user-facing protocol examples live in `examples/projects/`.

- `variants/history-contracts.txt` and `blocks/` retain vectors for historical
  reference models. The current scalar protocol package does not consume them.
- `contracts/` records the current native conformance probe coverage and
  consumer-specific facet observations; see its README for the scope.
- [Bulletproofs+](bulletproofs-plus/README.md) retains independent Monero proofs with recorded test coins. Its [upstream producer](../reference/monero/README.md) also owns the native Edwards map vectors.
- `kzg-eip4844/` retains the c-kzg-4844 v2.1.8 EIP-4844 vectors and derived
  cases whose outcomes the pinned c-kzg-4844 reference computed; see its
  [reproduction](../reference/c-kzg/README.md).
- `clean/air-control.json` is the output of the pinned Clean producer in
  `lean/integrations/clean` (`TestsClean/Control.lean`): exported relations
  and arenas, rows and Clean's residuals. The C++ and Rust native comparison
  consumes it; `just test-lean-clean` and `reproduce.py --with-clean` require it
  to be byte-identical to a fresh run. It comes from Lean and Clean, not from the
  native code it checks; replace it only with reviewed producer output.

Do not regenerate these fixtures from the implementation they check. The
optional formal package includes its required vectors without invoking the C++
compiler or Rust execution toolkit. Current native integration generates its
programs from Protocol IR and `.zkc` source in fresh report directories.

Native backend transcript vectors live under
`crates/zkc-test-support/fixtures/`, owned by the Rust workspace.
