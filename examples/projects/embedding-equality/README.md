# Mixed-domain equality

`main.zkc` publishes two KoalaBear base-field inputs, receives one octic
message, and draws an octic challenge. Acceptance requires both
`u + c == embed(a) + c` and `u + c == embed(b) + c`. The retained target is
`a == b`. The honest send expression does not restrict an adversarial proof.

The Lean fixture is in `ZkcExamples.Construction.EmbeddingEquality{Data,
Participant,Bodies,Binding}`. Native exports supply the constructor data;
`structured_views`, `checkCompiled`, selection and `SourceOccurrences.check`
check the exact source and constructed artifact. The typed body candidates
are independently checked against that snapshot.

`ZkcSecurity.Examples.EmbeddingEquality.compiled_verifier_eq` connects the
actual interpreter to the open verifier used by the existing typed reduction.
`compiled_ideal_soundness` proves zero error for arbitrary ideal-oracle
adversaries, including malformed and unread proof data.
`EmbeddingEqualityClaims` fixes the actual model and canonical subject;
`EmbeddingEqualityClient` contains the frontend-bound request and receipt.
`TestsSecurity.EmbeddingEqualityControls` checks refusal and necessity cases.

From `lean/security`, the targeted check is:

```sh
flock ../.lake/stage2-writers.lock env LEAN_NUM_THREADS=2 lake build \
  +ZkcSecurity.Examples.EmbeddingEqualityClient \
  +TestsSecurity.EmbeddingEqualityControls
```

The mathematical carriers are the actual base field and degree-eight binomial
quotient, with cardinalities `q` and `q^8` and characteristic `q` in both.
The theorem is relative to the admitted IR and ideal typed oracle. Native
octic basis/byte codecs and computational or QROM security require separate
correspondence and security arguments.

Check the source declarations from this project directory:

```sh zkc-example
zkc check
```
