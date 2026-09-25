# Randomized joint release is proved by one coupling of the whole released pair

When the artifacts and the runtime observations given to a recipient both
depend on randomness,
[permission to release them](../spec/properties/disclosure.md#randomized-joint-release)
is equality, across every allowed pair of worlds, of the joint law of the pair.
The sufficient proof is
[one coupling](../spec/properties/disclosure.md#couplings-and-joint-agreement)
of the two worlds' sample laws, with their actual marginals, on whose support
the artifact and the runtime observation both agree. The laws are normalized.

## Alternatives

**Check each channel and assume the channels independent.** Randomness shared
by one execution usually makes them dependent. Release a uniform bit `r` as the
artifact and `s xor r` as the runtime bit: each channel is uniform for either
secret `s`, and the pair reveals `s`. Two couplings that each justify one
coordinate can be incompatible, so the pair needs a single coupling that
justifies both.

**Require equal outputs under the same random seed.** This is sufficient and
too strong. It rejects an implementation in which a change of the secret is
matched by a translation of hidden masks, as in the
[correlated service](../spec/profiles/services/affine.md#joint-service-coupling-and-its-observer),
where the coupling pairs different private coins and the released pair is
still equally distributed.

**Couple subdistributions.** The coupling definition used here follows Barthe
et al. [1, §2, Definition 2], who admit discrete subdistributions. The
[normalized profile](../spec/properties/probability.md#normalized-discrete-distributions)
keeps stops as mass on stopped results and neither discards nor renormalizes
unsuccessful runs. Missing mass would need a meaning of its own, such as
divergence, and a statement of how the recipient observes it.

## Reason

A coupling is a joint witness with the actual marginals whose support lies in
the wanted relation; here the relation preserves the whole released pair. The
resulting law is small and reusable. It is not a program logic and asserts no
protocol's secrecy. Deterministic release keeps its simpler law, where
permission for the pair is equivalent to permission for both coordinates.

## Reopen when

A supported release claim holds only up to a statistical distance or a
computational advantage. Exact couplings no longer state it; an approximate
coupling with its loss is then needed, inside the
[experiment](../spec/properties/experiments.md#simulation-and-extraction-claim-boundaries)
that defines the comparison.

## References

1. Gilles Barthe, Benjamin Grégoire, Justin Hsu and Pierre-Yves Strub,
   "Coupling Proofs Are Probabilistic Product Programs," *POPL* 2017,
   pp. 161–174, §2, Definition 2.
   [Author preprint](https://arxiv.org/pdf/1607.03455).
