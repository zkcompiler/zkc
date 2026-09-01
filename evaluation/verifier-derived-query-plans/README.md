# Verifier-Derived Query-Plan Evaluation

This bounded instrument tests the selected PIR architecture for verifier-
derived words and finite query plans.

It forms separately identified pure read programs and one finite logical plan,
statically elaborates every route into guarded ordinary source-Oracle queries,
answers, and derived values, and checks the complete logical-to-source map. The
modelled flat event sequence contains no derived-word publication,
commitment, transcript frame, host callback, or runtime-generated occurrence.

The representative plan exercises four materially different shapes:

- two DEEP-ALI-style multipoint quotient views over different source Oracles;
- a STIR-style nested fold whose two derived reads select the `Fill` and source
  branches respectively;
- a batch Circle-FRI-style verifier combination of three source words; and
- a WHIR-style four-leaf grouped fold.

An independently coded arithmetic oracle imports none of the reference model.
It reproduces every output and exact ordered leaf-query trace from the fixture.
Negative tests cover cyclic programs, response-adaptive routing, incomplete
case partitions, false bounds, declassification, missing dependencies,
undefined quotients, absent source entries, event/map mutation, invented
publication or runtime events, multiplicity loss, and evaluator exhaustion.

Run:

```text
python3 -B evaluation/verifier-derived-query-plans/run.py --check
```

The package establishes bounded formation, static-elaboration, mapping, and
execution evidence for these finite cases only. It does not establish paper
correspondence, theorem applicability, soundness, zero knowledge, commitment
security, complete target-Core formation or admission, implementation
conformance, or support for answer-adaptive or unbounded query programs.
