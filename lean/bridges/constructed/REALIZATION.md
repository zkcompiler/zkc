# Actual scalar constructed realization

`realization.py` emits an actual-body normalization proof under fixed nominal
scalar and ideal transcript meanings. It consumes the checked export produced by
`extract.py` or `protocol-constructed-lean`. It never emits a security receipt.
The [formal model](../../docs/spec/constructed-realization.md) states the exact
interpretation and remaining native/provider boundary.

Supported source examples are the maintained
[Schnorr Helpers/Reordered](../common/fixtures/schnorr-forms.zkc) and
[Sumcheck Helpers/Horner](../common/fixtures/sumcheck-forms.zkc) entries. There is
no source-hash allowlist: the renderer checks the actual exported instruction
sequence, metadata and arithmetic. Other bodies satisfying the same bounded
profile still require the same kernel equations. WrongResidual is a freshly
compiled negative source example.

From the repository root, using a compiler with the constructed exporter:

```sh
python3 lean/bridges/constructed/realization_tests.py \
  --compiler build/compiler/zkc-compile
```

This regenerates source, policy, candidate and Snapshot artifacts, then checks
all four positive bodies and negative controls. Each generated `Realization.lean`
contains `snapshot`, transparent `program`, `imported`, actual checker `admitted`,
`full_denotation` and `projected_denotation`; a transitive axiom check rejects
anything beyond `propext`, `Classical.choice` and `Quot.sound`. Logs and the report
are written under `build/experiments/constructed-realization`. `--reuse-exports`
is only a development option and does not refresh native provenance.

Controls include stale state, a substituted observed message, returning the
pre-final-observation transcript, a forged terminal comparison, changed registered
field arithmetic, wrong residual mathematics, foreign bindings, unrelated
occurrence metadata, unselected Local origins, invalid references, input limits
and unknown primitives. In particular, returning a stale
transcript fails even when the acceptance Boolean is unchanged. A negative Lean
control must exit 1 with an equation proof error and no unrelated diagnostic;
signals, timeouts, missing imports and tool failures do not count as successful
refusals. Separate harness controls exercise signals, exit status 2, missing
imports and JSON size/depth limits.

Check the reusable modules and all their owned declarations separately:

```sh
cd lean
lake build Zkc.Source.Constructed.Scalar Zkc.Protocols.Sumcheck.NativeConstruction
lake env lean Tests/ConstructedRealizationAudit.lean
```

For a single export:

```sh
python3 lean/bridges/constructed/realization.py Snapshot.json Realization.lean \
  --protocol sumcheck
cd lean
lake env lean /absolute/path/to/Realization.lean
```

The Python entry point `render(data, protocol, namespace, receive_sites=None)`
returns a complete module. Exact receive selectors may be supplied by the parent
source-contract driver. No caller can supply Lean imports, expressions, meanings
or tactics. The parent must independently re-export the actual subject, check the
source contract, reconstruct the expected theorem type and select the security
consumer. A generated proof or retained digest alone does not authenticate a
native candidate.

The Sumcheck binding contains the full statement and exact occurrence schedule;
its second key retains the first challenge. Schnorr's `binding` constructor binds
source, candidate, policy, all primitive descriptors, application context, base
and key. The generic Schnorr normal-form theorem also permits a caller-supplied
binding; the request driver must use the identity-fixed constructor when claiming
that source/construction binding. Host initialization, codecs, native arithmetic,
lowering and Merlin conformance remain external.

The selected renderer profile bounds input JSON to 16 MB, nesting to 128,
constructor text to 2 MB, instructions to 256 and selected handlers to 32.
Larger valid native programs require an explicitly extended profile; they do
not fall back to an unchecked normalization.
