# Composing a KZG opening consumer

`Zkc.Protocols.OpeningSum` defines a typed verifier that requests an opening at
each of two public points, checks each opening before continuing, and compares
their sum with a public claim. Requests include the commitment and point. A
failed opening stops with `reject`; a failed sum returns `false`. The complete
process, including order and early termination, is its reusable
`VerifierContract`.

The source is an elaborated `RawProgram`, with a proved `program_denote`
equation. `accepted_false_implies_bad` decomposes false acceptance into a reached,
accepted opening whose value differs from the designated polynomial evaluation.
This deterministic decomposition assumes no commitment security and no
independence between the openings.

The optional `ZkcSecurity.ArkLib.KZG.OpeningSum` consumer instantiates the opening
predicate with ArkLib's actual `KZG.verifyOpening`. Its experiment samples the
nonzero setup trapdoor privately, publishes `Groups.PowerSrs.generate`, and runs
one adversary that returns polynomial coefficients, two points, a claim, and two
openings. The verifier's commitment is `KZG.commit` of those coefficients. The
coefficients are available to the reduction; the verifier receives only the
commitment, points, claim, and openings. All submitted values may depend on the
public setup and the adversary's probabilistic work.

`source_false_extract` chooses an incorrect accepted opening and constructs the
honest opening at that same point. ArkLib's correctness and two-opening algebra
produce a concrete t-SDH solution. `reduction_event` connects this computation to
the actual ArkLib t-SDH experiment, preserving the adversary invocation and its
state. `source_advantage` proves

```text
Pr[the typed source accepts a false evaluation-sum claim]
  ≤ tSDHAdvantage(reduction(adversary)).
```

`source_soundness` accepts an explicit bound on this particular reduced
adversary. It does not use the pinned library's unrestricted `tSdhAssumption`
predicate as a stand-in for PPT security. A computational application must supply
its own adversary admissibility, representation, and cost argument. Algebraic
premises include a prime-order group model, a nontrivial generator, a nonzero
bilinear pairing on the generators, and the selected structured setup.

`contract_advantage` reuses the reduction for any verifier proved to implement
the common open-process contract. Different helper layouts or arithmetic source
forms therefore need a contract proof, not a new cryptographic reduction.

This is a registered-polynomial evaluation game. It does not extract a polynomial
from an arbitrary malicious commitment and does not establish a multivariate
Sumcheck/PCS protocol. There is no native KZG, curve implementation, serialization,
trusted-setup ceremony, or Fiat–Shamir correspondence claim here. Those require
their own connections and, where applicable, stronger commitment properties.

`TestsSecurity.KZGOpeningSum` checks honest ArkLib openings and explicit pairing
executions over a transparent exponent group of order seven. Knowing the toy
trapdoor permits a false accepting opening, from which the actual reduction
extracts a t-SDH solution. This control intentionally demonstrates why the
hardness premise cannot be replaced by algebraic correctness.
