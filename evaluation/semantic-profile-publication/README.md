# Semantic-profile publication evaluator

This bounded package reconstructs the complete indexed owner-source corpus in
[`docs-next/foundation/semantic-profile-manifests.json`](../../docs-next/foundation/semantic-profile-manifests.json)
under the publication contract in
[`docs-next/foundation/semantic-profile-publication.md`](../../docs-next/foundation/semantic-profile-publication.md).
It is a research and conformance instrument, not current repository authority,
a cryptographic proof, or an implementation-conformance claim. The six
durable v0 PIR artifacts remain byte-for-byte backward-compatibility controls.

The package contains two implementations:

- `reference_model.py` compiles the owner-source manifests with the selected
  Foundation `MetaValueV0`, declaration-reference, profile-body, and typed-ID
  constructors; and
- `independent.py` imports none of that code. It independently reconstructs
  the constitutional datum encoder, three prior-meta descriptors, typed
  content framing, source extraction, declaration graph, direct-use table,
  profile bodies, IDs, and exact root closures.

Run the gate from the repository root:

```sh
python3 -B evaluation/semantic-profile-publication/run.py --check
```

Print the independently reproduced identity table with:

```sh
python3 -B evaluation/semantic-profile-publication/run.py --print-identities
```

The gate compares complete profile-body and content-reference bytes, not only
digest suffixes. Its mutations cover missing, surplus, cyclic, and unused
direct imports; unresolved declaration references; missing selectors;
unreachable source; expected-ID feedback; source-marker duplication and loss;
CR, non-NFC, and trailing-whitespace source; concrete Core coordinates in the
selected FS dependent receipt templates; source-coordinate exclusion; exact
dependency rotation; sibling locality; owner-namespace disagreement;
source-page relocation under the owner-qualified source edition; parent/child
validation locality; exact Analysis branch topology; Relations semantic/module
catalog separation; and the Foundation law-source pins. Both compilers
reconstruct and compare the complete seventeen-profile identity table; the
printable table is a derived inspection artifact and is not committed.

Passing demonstrates that this exact finite source corpus deterministically
forms seventeen published target profiles under two implementations, preserves
the six frozen v0 PIR controls byte-for-byte, and rejects the listed malformed
cases or rotates only the intended dependency cone. It does not prove that the
marked prose is equivalent to a complete typed law interpreter, that every
semantic sentence is internally consistent, that any cryptographic theorem
applies, or that a production evaluator implements these profiles.
