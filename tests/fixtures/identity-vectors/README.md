# Identity vectors

Four named families exercise ordinary calls, generic definitions, nested calls
and configured receives. Each has a `.source.json`, `.descriptor.json` and
handwritten `.normalized.json` expectation. The receives family additionally
uses `.configuration.json`.

[The comparison](../../identity/test_identity_reference.py) checks independent
Rust and Lean identity implementations against these expectations, and submits
malformed source mutations to C++, Rust and Lean. The ordinary and receives
descriptors have identical bytes but belong to independent cases; keep both.

[FrontendIdentity.py](../../../formal/checks/FrontendIdentity.py) defines the
vectors and their expectations. To export them for review from the repository
root, with the formal tools already built:

```sh
python3 formal/checks/FrontendIdentity.py --emit build/identity-vectors
```

This also runs the script's existing controls. Compare the emitted JSON with
this directory before replacing any vector. Runtime inputs used inside those
controls are not part of this identity-only corpus.
