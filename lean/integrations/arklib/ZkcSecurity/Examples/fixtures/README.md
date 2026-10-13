# Constructed Schnorr fixture

`schnorr-constructed.json` is the actual unsimplified Helpers verifier exported
by `protocol-constructed-lean` after native candidate checking. It retains four
selected Local handlers, sixteen instructions, all primitive metadata/operands,
and the Boolean/transcript output. `../SchnorrConstructedData.lean` is its
transparent constructor rendering and actual-body normalization, with
kernel-checked admission by exact raw erasure.

Regenerate from the maintained Helpers source using the constructed bridge's
`extract.py` and its checked `protocol-construct-proof` candidate. The source hash
must also match `ZkcExamples.NativePrograms.Variants.SchnorrHelpersData.snapshot`.
Use the constructed realization renderer after exporting the snapshot:

```sh
python3 lean/bridges/constructed/realization.py \
  lean/integrations/arklib/ZkcSecurity/Examples/fixtures/schnorr-constructed.json \
  lean/integrations/arklib/ZkcSecurity/Examples/SchnorrConstructedData.lean \
  --protocol schnorr --namespace ZkcSecurity.Examples.SchnorrConstructedData
```

Compare the complete JSON and rendering, not just their identity fields. The native
exporter, Python renderer, and native checking remain tested trust boundaries.
The `SchnorrConstructed` example separately proves the admitted body's complete
canonical-RO denotation and its extraction connection.

The descriptor is `merlin3.bls12-381.fr64be/0`. Its retention identifies the native
subject. The formal primitive interpretation is explicitly ideal and does not
certify the deployed Merlin provider or native byte transport.
