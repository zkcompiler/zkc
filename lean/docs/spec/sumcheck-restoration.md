# Quadratic Sumcheck in the cached restoration model

This independent formal model is owned by
`ZkcSecurity.ArkLib.Sumcheck.FiatShamir`. It uses the existing common-source
Sumcheck coefficient representation, quadratic polynomial semantics, and
imported-verifier contract. It does not specify a native cryptographic provider.

The supported endpoint has two logical rounds over a finite field `F`. A prover
message is the ordered triple of constant, linear, and quadratic coefficients.
The public statement is a bivariate polynomial of degree at most two in each
coordinate and its claimed Boolean-cube sum. There is no commitment or hidden
polynomial. Every supplied coefficient triple is permitted; an honesty condition
does not filter the adversary's messages.

For any residual polynomial `p`, residual claim `c`, and conjunction `C` of prior
checks, the knowledge witness type is `Unit` and its predicate is
`C ∧ c = p.booleanSum`. Sending message `m` adds `m.boundary = c`. Sampling
challenge `r` restricts `p` at `r` and replaces `c` with `m.evaluate r`. All
backward witness maps are the identity. A prover message preserves the predicate
backwards because it only adds a check.

The verifier's bad event is exactly

```text
∃ laterWitness, ¬ before.holds (extract laterWitness) ∧ after.holds laterWitness.
```

For this unit-witness instance it is equivalent to

```text
C ∧ m.boundary = c ∧ c ≠ p.booleanSum
  ∧ m.evaluate r = (p.restrict r).booleanSum.
```

This is proved for every authored prefix, not only prefixes having positive
interactive probability. A false boundary sum forces a nonzero difference of
quadratic polynomials, hence at most two roots. Uniform finite-field sampling
therefore bounds the entire existential bad event by `2 / |F|`. No local-security
hypothesis is supplied by the consumer.

The restoration experiment is the pinned
`Interaction.Oracle.Security.StateRestoration.verificationGame`. An arbitrary
adaptive total oracle program selects the statement, complete message/salt
sequence, and unit witness. The same initially empty cached uniform oracle serves
its queries and both completion queries. The native ArkLib verifier actually
queries its accumulated coefficient messages and evaluates both boundary checks
and the final public polynomial. Terminal knowledge equals this verifier's
accepting Boolean by a proved endpoint law.

The first restoration key binds statement, first message, and first salt. The
second key binds statement, both ordered messages, and both salts; previous
challenges are omitted. Reconstruction obtains earlier challenges from the same
cache. Arbitrary repeated or out-of-order requests are allowed. Input and salts
need decidable equality; the theorem does not require a finite salt space.

If the adversary makes at most `Q` oracle accesses on every branch, false-statement
acceptance is at most `(Q + 2) * 2 / |F|`. The budget counts precomputation, repeated
attempts encoded within that adversary, cache hits, and two final completion
accesses. Unbounded offline access or an uncharged verifier completion is not an
instance of the theorem. Independent private coin families inherit the bound
when each branch satisfies the same query budget.

The correspondence with a `Common.VerifierContract` observes only
`outcome = returned (some true)`. Ordinary PIR can reject after three receives,
or after the first challenge and second triple. Its reached-effect state is
respectively 3, 8, or 10; its challenge-site projection has length 0, 1, or 2.
Restoration completes both challenges regardless. Query/state equality between
these two executions is not asserted.

The optional full-prefix endpoint uses an arbitrary input type and a fixed
projection to the public Sumcheck statement. Its keys are `(input, m)` and
`(input, m, r, n)`, with all supplied values queryable. The proved
`FiatShamir.Prefix` simulation encodes the earlier challenge as the second
restoration salt; the first salt is `none`. It retains the entire input. The
reduction queries the first selected key to obtain that salt, so its adversary
budget is `Q+1` and its final restoration budget is `Q+3`. False acceptance is
bounded by `(Q+3) * 2 / |F|`. The simulation does not assume that an adversary's
queried prefixes are consistent with the first oracle answer.

`FullPrefix.earlyVerify` executes each guard before its challenge. For an
arbitrary preexisting cache, its acceptance probability equals full completion's
acceptance probability. This equality lifts through the adaptive adversary that
shares that cache. An early rejection may leave fewer keys cached and emit fewer
requests. Only the Boolean false-acceptance event is equated; no equality of final
cache or query trace follows from the coupling.

`Native.game` uses `NativeConstruction.Binding` as the full-prefix input,
retaining source, construction, application context, exact occurrence schedule,
coefficients and claim. Its selected output freezes source/construction/schedule
while allowing arbitrary adversarial queries at other bindings. Its handler
returns real replies and records the full keys. `PIR.Proc.runM` retains returned
transcript, stop reason, unit handler state and reached event log. A proved full
process equation for `Imported.denote` transports this entire game before the
acceptance projection; a returned true Boolean accepts, and every stopped result
rejects. A stopped process does not return its internal SSA transcript; the
execution still records its handler state and reached events. `Native.soundness`
then supplies the bound without any residual-security
or oracle-simulation premise. The actual game needs at most `Q+2` accesses; the
security reduction conservatively charges `Q+3`. Independent private coins may
select a family of adaptive adversaries with a common budget.

`Native.soundnessProperty` owns this registered conclusion as a property of the
actual subject. `Native.soundnessConsumer` requires the full process equation
uniformly over every selection and discharges that property.
`Native.direct_soundness` separately proves `(Q+2) * 2/|F|` for the same game.
`FullPrefix.earlyVerify_acceptance_queries` proves the actual two-query trace on
acceptance for every answer table; `earlyGame_failureTrace` lifts it through any
adaptive adversary. ArkLib's extraction-failure lemma and VCVio's bad-query bound
then apply to the actual accesses. `randomized_direct_soundness` also permits
independently sampled private coins with a common all-branch budget.

This endpoint relies on finite-field axioms, the supplied uniform `SampleableType`
laws, Lean's kernel and standard logical axioms, and the audited pinned upstream
theorems. Actual Host initial-transcript/proof-buffer conformance, byte encodings,
concrete transcript implementations, cryptographic primitives, native lowering,
and source/export authenticity require their own
correspondences. The typed full-prefix simulation is proved here and in its
owning optional
integration. It does not cover Merlin/STROBE state, byte framing, digest collisions,
or modulo/rejection sampling in an arbitrary native transcript provider.
