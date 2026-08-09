# Python reference twin

This project independently implements the current PIR judgments, canonical
encodings, soundness-signature checks, and selected endpoint execution used by
zkc's differential tests. It is a conformance oracle for declared parity
surfaces, not a second specification or a cryptographic proof.

Run its self-checks from the repository root:

```sh
uv sync --locked --project reference
uv run --locked --project reference python -m oracle.model
```

The C++/MLIR implementation and this twin share the normative documents under
`docs/spec/`; agreement between them is bounded implementation evidence.
