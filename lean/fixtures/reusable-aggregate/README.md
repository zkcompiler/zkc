# Two independent record batches

Select `reusable_aggregate::TwoBatches<batch_opening::Scalar>` from `zkc.toml`.
The root checks its first transmitted batch inline, then applies `CheckBatch`
once to independent point, value and batch inputs. It returns, in order, the
first decision, first delivered batch, second decision and second delivered
batch. These are point/value records, with no PCS or security claim.

`Tests.ReusableAggregateTwoBatchesSource` checks the complete retained source
against reusable helper bodies. `Tests.ReusableAggregateTwoBatches` uses the
existing normalizer, template installation and composition APIs to prove the
whole mathematical reference for optional inputs and arbitrary typed replies.
Its controls keep both batches when the first decision is false and distinguish
the receive prefixes of missing first and second inputs.

Reproduce the snapshot and typed root from the repository root:

```sh
python3 lean/bridges/construction/plain.py --compiler PATH_TO_ZKC_COMPILE \
  --output build/two-batches --subject two-batches --write
```

`Tests.ReusableAggregateTwoBatchesData` serializes the native export.
`Tests.ReusableAggregateTwoBatchesBodies` is printed by Lean from the admitted
snapshot. The source installation checks this complete generated root together
with the reusable helper family. There is no authored slot layout or root-body
interpreter proof for this instance.

Print both compiled-role connections with the common generator, then check the
complete source reference and its missing-input controls:

```sh
cd lean
lake build Tests.ReusableAggregateTwoBatchesArtifacts ZkcTools.ConstructionBindings.Generate
lake env lean --run checks/GenerateReusableAggregate.lean .
lake build Tests.ReusableAggregateTwoBatches Tests.ReusableAggregateTwoBatchesConnection
```

`producerConnected` and `validatorConnected` use the same generic
`SourceConnection.Connected` theorem as the maintained protocols. The selection
file supplies declaration names only; it supplies no slots, semantic equations
or protocol-specific proof tactic. The native capture derives public input
positions from the actual exported role scopes.
