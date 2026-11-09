# Two independent record batches

Select `reusable_aggregate::TwoBatches<batch_opening::Scalar>` from `zkc.toml`.
The root checks its first transmitted batch inline, then applies `CheckBatch`
once to independent point, value and batch inputs. It returns, in order, the
first decision, first delivered batch, second decision and second delivered
batch. These are point/value records, with no PCS or security claim.

This source fixture carries no current formal endpoint. The former generated
source, normal-form and compiled-role proofs are retired. Native compilation and
new actual-source installation must be assessed separately; see
[formal support](../../docs/support.md).
