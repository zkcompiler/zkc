# Fiat–Shamir as a mathematical transformation

The maintained transcript library interprets message absorption and typed challenge
queries over the shared Process. It fixes the event ordering, decoding, sampling
and failure semantics before any bound is proved. The mathematical reduction is
described in [multi-round security](fiat-shamir-security.md).

An installed native transformation requires two independent connections: the
actual source participant to its mathematical process, and the actual generated
controller/provider to the selected transformed meaning. Complete outcomes, shared
service state, pending queries, continuations, reply order, layout and resource
accounting must be preserved. Generated bookkeeping belongs in common infrastructure;
protocol companions supply mathematical laws and meaningful admissibility premises.

The former `Construction` evaluator and native endpoint installations are retired.
The compiler's [constructed-participant export](../../../docs/spec/formats/constructed-participant.md)
remains a native contract; its bytes or digest alone do not prove these connections.
The current [construction framework](source-construction.md) supplies reusable
Region/Process rules, with actual-source/controller integration still open.
