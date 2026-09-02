# Python reference twin

This project independently implements the current PIR judgments, canonical
encodings, soundness-signature checks, and selected endpoint execution used by
zkc's differential tests. It is a conformance oracle for declared parity
surfaces, not a second specification or a cryptographic proof.

## Architecture

The twin is deliberately narrower than the product and depends only on the
Python standard library:

```text
canonical values and digests        oracle/canonical.py
              |
              +--> PIR/OIR kernel   oracle/model.py
              |       |             registry admission, judgments, projection
              |       +--> witnesses / parity / selected execution
              |
              `--> signature.py --> wellformed.py --> derive.py
                      declarations       typing          structural derivation
```

`canonical.py` is the dependency-free bottom layer. `model.py` currently owns
the PIR registry, judgments, canonical artifact image, and OIR projection, and
re-exports the canonical names used by existing parity clients. That facade is
compatibility, not duplicated implementation. Further extraction should move
one semantic owner at a time while preserving byte-for-byte parity outputs.

`witnesses.py` contains hand-built finite cases; it is evidence input, not
authority. `parity.py` is the command-line comparison surface. `exec.py`
implements only the selected endpoint fixtures. The signature,
well-formedness, and derivation modules intentionally stop before treating a
second copy of theorem arithmetic as independent evidence.

No reference module may import compiler/runtime code or exploratory
`evaluation/` models. The architecture tests enforce the bottom-layer and
soundness-module dependency directions. The canonical-law suite adds an
independently encoded finite grammar, round trips, negative mutations, and
metamorphic ordering checks, while the native lit suite checks the declared
cross-implementation parity surfaces.

Run its self-checks from the repository root:

```sh
uv sync --locked --project reference
uv run --locked --project reference python -m oracle.model
uv run --locked --project reference python -m unittest discover \
  -s reference/tests -v
```

The C++/MLIR implementation and this twin share the normative documents under
`docs/spec/`; agreement between them is bounded implementation evidence.
