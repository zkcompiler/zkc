# Reusable library contract clients

These captures exercise member-generic interface dispatch through actual native
protocol execution. The integration tests are
`common/tests/protocol/test_language_library_contracts.py`.

- `evaluation.zkc`: sealed linear residual evaluation and a consuming checker.
- `sumcheck.zkc`: two-variable Sumcheck followed by a field-generic opening
  consumer. The verifier supplies the complete authoritative table; this is an
  explicit table opening control, not a compressed polynomial commitment.
- `group.zkc`: Schnorr with a group-generic response member and associated scalar
  type, explicit nonce/challenge services and communication sites.

Specifications remain neutral authored requests. The native checker retains
all postconditions, requests, relation syntax, owner/audit attachments and
companion lookup keys. The test journal retains fresh written-source and
source-correspondence output alongside the actual compiled package. Those are
inputs for the Lean-owned connector, not generated proofs. The named `formal`
requests intentionally have no installed interpretation in this fixture; their
status must remain open, including after successful native execution.

The test mutations distinguish false final acceptance, reached stop, use after
consumption and changed implementation with a surviving lookup key. A stable
companion address does not authorize reusing a receipt for a changed subject.

`distributed.zkc` transfers a linear product through a selected generic Protocol
member with alpha-renamed role binders and a nonidentity call map. It constructs
the record in its home, preserves both custody fragments, and consumes it before
returning the verifier's scalar result; it does not fabricate external ingress.
