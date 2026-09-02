# Verifier-Derived Query-Plan Evaluation

This bounded instrument tests the selected PIR architecture for verifier-
derived words and finite query plans.

It forms separately identified pure read programs and one finite logical plan,
statically elaborates every route into guarded ordinary source-Oracle queries,
answers, and derived values, and checks the complete logical-to-source map. The
modelled flat event sequence contains no derived-word publication,
commitment, transcript frame, host callback, or runtime-generated occurrence.

The selected profile fixes prime-field arithmetic, explicit partial-operation
terminals, public activation, and causal prior-result references. Source-answer
taint is rejected from activation, routing, requested indices, and transitive
child control, including when a read-free program returns an answer-tainted site
argument, while post-read pure value flow remains admissible. Prior values reuse
an existing Core value; the elaborator creates no logical-result event.

The representative plan exercises four materially different shapes:

- two DEEP-ALI-style multipoint quotient views over different source Oracles;
- a STIR-style nested fold whose two derived reads select the `Fill` and source
  branches respectively;
- a batch Circle-FRI-style verifier combination of three source words; and
- a WHIR-style four-leaf grouped fold.

An independently coded arithmetic oracle imports none of the reference model.
It reproduces every output and exact ordered leaf-query trace from the fixture.
An independently authored nine-event flat-Core fixture imports neither the
reference model nor its elaborator. A complete path-to-occurrence map accepts a
causally valid target ordering that differs from recursive expansion, while flat
Core admission refuses operand use before definition. Forty-three tests cover
cyclic programs, response-adaptive routing, read-free answer-taint laundering,
incomplete case partitions, composite field carriers, componentwise bound
calculation, transitive declassification, missing dependencies, undefined
quotients, invalid interpolation shape, absent source entries, future
references, causally valid and invalid reorderings, event/map/Core mutation,
invented publication or runtime events, multiplicity loss, and runtime or
static-elaboration limit exhaustion.

Run:

```text
python3 -B evaluation/verifier-derived-query-plans/run.py --check
```

The package establishes bounded formation, static-elaboration, mapping, and
execution evidence for these finite cases only. It does not establish paper
correspondence, theorem applicability, soundness, zero knowledge, commitment
security, general target-Core formation or admission beyond the bounded
independent fixture, implementation conformance, or support for answer-adaptive
or unbounded query programs. It also does not settle the separate one-case route
guard-normalization obligation for complete K2 admission.
