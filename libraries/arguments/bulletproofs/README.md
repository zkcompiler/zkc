# Weighted inner-product arguments

[`bulletproofs::weighted_inner_product`](weighted_inner_product/lib.zkc) owns
the reusable weighted inner-product rounds and the raw-point observation
contract. Its standalone manifest captures the core operations it uses and
selects no Monero codec, concrete group or application Entry.

The concrete [Monero Bulletproofs+ construction](../../constructions/monero/bulletproofs_plus/README.md)
owns its curve, transcript, 64-bit range statements and wire format. The
[example](../../../examples/projects/bulletproofs-plus/README.md) selects that
construction with managed randomness. There is no empty `bulletproofs` source
module linking all constructions.

Tests cover independent inner-product computations, false equations and exact
Monero proof bytes at every supported aggregation count. Execution agreement
does not establish knowledge soundness, zero knowledge or transaction validity.
