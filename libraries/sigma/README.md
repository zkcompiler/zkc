# Sigma compositions

Two discrete-logarithm Sigma protocols composed from the Schnorr pattern. Both are
generic over the group; the client selects the group and construction.

| Declaration | Contract |
|---|---|
| `DLogPair` | Each statement point is its base times its own witness scalar |
| `DLogEquality` | Both statement points are their bases times one witness scalar |
| `SchnorrAnd` | One nonce per statement, one shared challenge and one response per statement; accept when both Schnorr equations hold |
| `ChaumPedersen` | One nonce committed at both bases and one response; accept when both equations hold with that response |

Each protocol's `knowledge` target applies its relation to the verifier's bases
and points and the prover's witness ports. `SchnorrAnd` names two witness ports,
so two extracted witnesses need not agree. `ChaumPedersen` names one, and its
single response forces one witness for both bases. Sharing the challenge does
not make witnesses shared; sharing the nonce and response does.

The [example project](../../examples/projects/sigma/README.md) selects BLS12-381 G1
and the installed Merlin transcript suite. The
[formal support](../../lean/docs/support.md#sigma-compositions) states what is proved
about the retained exports.
