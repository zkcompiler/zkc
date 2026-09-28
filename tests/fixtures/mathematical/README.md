# Mathematical canonical encoding fixtures

Run from the repository root:

```sh
python3 tests/fixtures/mathematical/check.py --lean
```

`encoding.py` implements the bounded [canonical format](../../../docs/compiler/mathematical-format.md).
`check.py` checks five saved vectors against their complete bytes, round trips,
independent `sha256sum` subject hashes, malformed encodings, bounded resource
refusal, deterministic byte mutations and semantic-identity mutations. `--lean`
compares every vector with the independently implemented typed-value conversion
in [Encoding.lean](../../../formal/Examples/Mathematical/Encoding.lean), followed
by the existing Lean logical-tree codec. Lean dependencies must be available.

The scalar/key vectors cover unsigned bounds, Boolean/string distinctions,
UTF-8 ordering and absence of Unicode normalization. The mathematical message, located message and indexed
subjects illustrate the exact record format, including explicit capability
and static tables. Their all-zero registry digests are fixture placeholders;
they are not admitted production interpretations. The saved JSON subjects are
hand-authored format examples, not exports proved to correspond to the typed
Lean protocol examples. A generic encoding round trip does not check typing,
role availability, root permissions, site formation or placement correctness.
Those admission readers are the next implementation unit.

Debug fields must stay outside the subject envelope. The encoder refuses them
at the subject-digest API rather than silently stripping unknown fields. The
Lean comparison tool accepts already parsed valid vectors; the Python transport
parser supplies the duplicate-key and hostile JSON controls. This does not claim
that Lean's general JSON parser has the same hostile transport behavior.
