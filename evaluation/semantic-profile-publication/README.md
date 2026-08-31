# Stable PIR semantic-profile publication evaluator

This bounded package reconstructs the six durable owner-source artifacts in
[`docs-next/pir/profiles/`](../../docs-next/pir/profiles/README.md). It is a
research and conformance instrument, not current repository authority, a
cryptographic proof, or an implementation-conformance claim.

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
dependency rotation; sibling locality; and the Foundation law-source pins.

Passing demonstrates that this exact finite source corpus deterministically
forms the six published target profiles under two implementations and that the
listed mutations are rejected or rotate only the intended dependency cone. It
does not prove that Markdown is equivalent to a future formal law calculus,
that every semantic sentence is internally consistent, that any cryptographic
theorem applies, or that a production evaluator implements these profiles.
