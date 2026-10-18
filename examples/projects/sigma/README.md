# Sigma composition project

[main.zkc](main.zkc) uses the [Sigma library](../../../libraries/sigma/README.md) with
BLS12-381 G1 and the installed Merlin transcript suite. `AndProof` and
`EqualityProof` are noninteractive; `AndInteractive` and `EqualityInteractive`
run the same protocols with actual messages and managed random services.

```sh
cd examples/projects/sigma
zkc run AndInteractive
zkc prove EqualityProof --output=equality.zkproof
zkc verify EqualityProof --proof=equality.zkproof
```

The inputs use public demonstration values. For `SchnorrAnd`, the first point is
3 times the generator and the second is 7 times the base 5 times the generator.
For `ChaumPedersen`, both points use the scalar 3, at the generator and at 5
times the generator. Scalars are decimal strings; group values contain canonical
element bytes.

The relations and targets retain the statement/witness association for
analysis. They add no implicit guard or knowledge theorem.
