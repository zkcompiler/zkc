# Issued causal experiment

This experiment consumes the local code and retained inputs of an
[issued literal](affine.md#literal-selection-and-issuance). It uses the
[local cut types](../sumcheck/local-prover.md#local-prover-state-and-code) and the
[one-round verdict](../sumcheck/one-round-consumer.md#committed-local-prover-consumer).
Its sampler runs at each commitment. Unlike the product-provider request,
this experiment has no activity predicate or remaining-tape counter.

## Issued causal experiment

The causal experiment uses the literal's local code and retained inputs with
uniform finite local coins. Let `pre : PMF (Cut F)` be its normalized law of
complete cuts, and let `draw : Boundary F → PMF D` give the actual normalized
sampler law at each commitment. Using the
[common probability operations](../../properties/probability.md#normalized-discrete-distributions),
define:

```text
response(stopped localState) = pure none
response(committed b) = map some (draw(b))
joint = pre >>= (cut ↦ response(cut) >>= (d ↦ pure(cut,d))).
```

The observer applies the [one-round verdict](../sumcheck/one-round-consumer.md#committed-local-prover-consumer)
to a commitment and delivered `some d`; other cases give `none`. Its law is
the actual interpreted reduction. At a reachable commitment, local coin
normalization gives positive mass, and:

```text
joint(committed b,some d) = pre(committed b)*draw(b)(d).
```

Division by the actual commitment mass gives the conditional sampler law.
This allows a boundary-dependent sampler; the law is a stated input, not a
freshness conclusion from its marginal distribution. For a field, finite
injectively embedded challenge domain, point cap `ε` at every reachable
commitment, and `b.claim≠2` there, acceptance is at most `2ε`.

The check–issue–execute experiment returns `pure none` on issuance failure,
and otherwise executes the actual issued causal program. Its installed variant
also maps installer failure to `pure none`. The cap and falsity premises range
only over successfully issued outputs and their reachable commitments. These
are explicit non-accepting projections in this experiment; admission still
returns its own refusal and is not redefined as a verifier decision. Agreement
of admitted environments preserves the whole experiment for the same sampler
function and embedding. This one-round acceptance statement and the affine
service's witness-observation statement are separate properties.
