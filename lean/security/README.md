# Security theory and its consumers

`zkc_security` is the probability-bearing package above deterministic `zkc`.
It adds the pinned VCVio, PolyFun and CompPoly dependencies; ArkLib and Clean
remain independent optional packages. See the [dependency baseline](../docs/dependencies.md).

Three library roots have different responsibilities:

- `ZkcSecurity`: reusable definitions and kernel-checked theorems.
- `ZkcSecurityTools`: elaborators, tactics and source generators. Their proposals
  establish nothing until Lean checks the resulting term.
- `ZkcSecurityExamples`: closed subjects, selected generated artifacts and their
  applications. Theory and reusable tools cannot import this root.

`TestsSecurity` audits all three roots and exercises accepted and refused cases.
All three libraries and the tests are default Lake targets. These are source
boundaries within one package, so they do not introduce additional dependency pins.

The theory has six areas:

| Area | Responsibility |
| --- | --- |
| `Mathematics` | Probability, algebra and reusable oracle results |
| `ProgramLogic` | Charged derivations, process properties and transcript games |
| `Families` | Abstract protocol mathematics, independent of a selected source |
| `Transformations` | Fiat–Shamir, commitments, hash chains and stage composition |
| `Bindings` | Source-template installations, representations and actual participant connections |
| `Claims` | Fixed request meanings, resolution, receipts and separately owned proof methods |

An abstract family, a source-template installation and a closed Entry are
separate reuse units. A binding may fix the implementation of a reusable
component while quantifying over its checked definitions, model and layout.
That does not make it a closed subject. A proof that inspects one generated
payload belongs in `ZkcSecurityExamples`.

For example, the [Sumcheck facade](ZkcSecurity/Families/Sumcheck.lean) exports the
mathematical contract. Table/source installations live under
`Bindings/Sumcheck`, GKR installations under `Bindings/Gkr`, and the concrete
SmallSumcheck, TwoSums and GKR clients under `ZkcSecurityExamples`. New protocols
reuse a family contract and an existing installation when their mathematics
and source template match. A different implementation supplies checked body
associations and representation laws; a different family supplies its mathematics.
See the [component authoring guide](../docs/development/component-authoring.md).

Knowledge requests depend on lower transcript operations and the request-fixed
extraction profile. Sigma justification and endpoint assembly live in
`Claims/Methods/Knowledge.lean`. A proof method cannot change the requested
extractor or the actual verifier experiment. Commitment application claims
also retain the connection from an application failure to the designated
checkpoint and its actual verifier query log.

Import paths identify source ownership. Existing declaration namespaces and
mathematical theorem names are retained; they are not alternate import routes.
No forwarding modules are provided at the retired paths. The source-header
audit records public, meta and import-all edges. Standalone theory and tactic
clients test the exported interfaces outside this package.

From the repository root:

```sh
python3 scripts/develop.py fetch-lean --deps security
python3 scripts/develop.py lean --deps security
python3 common/tests/run.py lean-security
nix build .#security
```

The [architecture](../docs/architecture.md) documents the complete dependency
graph and the boundaries enforced by both source and declaration audits. These
formal models do not by themselves establish native correspondence or an
unspecified cryptographic assumption. Consult [formal support](../docs/support.md)
for the scope of each maintained result.
