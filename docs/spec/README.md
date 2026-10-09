# Specification

This reference defines the native `.zkc` → mathematical MLIR → `zkc.program/0`
path, its application interfaces, and the mathematical contracts used to describe
it. Definitions are normative within their stated parameters and premises.
Examples are informative. [Status](../status.md) records implemented coverage.

## Native contracts

| Subject | Contract |
|---|---|
| Source language | [Definitions, types, bodies, Entries and translation](language/README.md) |
| Mathematical IR | [Protocol profiles](ir/protocols.md), [mathematics](ir/mathematics.md), [polynomial recipes](ir/polynomials.md) |
| Composition and control | [Applications](ir/composition.md), [iteration](ir/iteration.md), [functions](ir/functions.md), [control](ir/control.md), [completion](ir/completion.md) |
| Data | [Variants](ir/variants.md), [nested data](ir/data.md) |
| Construction and analysis | [Transcripts](ir/construction.md), [public-coin views](ir/public-coin.md), [compiler limits](ir/limits.md) |
| Serialized artifacts | [Program](formats/program.md), [Entry package and interface](formats/entry.md), [proof deployment and transport](formats/proof.md), [message frames and setups](formats/messages.md) |
| Host execution | [Entries](runtime/entries.md), [joint bundles](runtime/joint.md), [proofs](runtime/proofs.md), [attempts](runtime/attempts.md), [services](runtime/services.md) |
| Operational boundaries | [Capacity](runtime/capacity.md), [file admission and publication](runtime/publication.md) |

The four MLIR profiles constrain one program at successive compilation
boundaries; they are not four dialects. An artifact's structural admission does
not establish its derivation from source. Version `0` names the current schema,
without promising compatibility between development builds.

## Mathematical and checking contracts

These chapters define parameterized objects, laws and obligations. A native
consumer must fix the relevant interpretation, inputs, states and capacity
premises. A law alone does not prove that a C++ checker or Rust kernel realizes it.

| Subject | Contract and native use |
|---|---|
| Values and domains | [Values](domains/values.md), [vectors](domains/vectors.md): typed algebra, contractions and representations |
| Polynomial meaning | [Tables and polynomials](domains/polynomials.md), [shared ring expressions](domains/ring-expressions.md): formal substitution, polynomial SSA and recipe lowering |
| Relations and authentication | [Constraints](domains/constraints.md), [oracles](domains/oracles.md), [relation terminals](relations.md): imported assets, binding and explicit terminal checks |
| Representation | [Complete results](realization/representations.md), [codecs](realization/codecs.md), [artifacts](realization/artifacts.md): source comparison, wire admission and retained authority |
| External constructions | [Hash-chain and duplex transitions](realization/external-constructions.md): explicit native primitive calls |
| Validation | [Refinement](verification/refinement.md), [analysis](verification/analysis.md), [judgments](verification/judgments.md): the obligations of source-relative checking |

The mathematical chapters use the [formal core](../../formal/docs/spec/README.md)
vocabulary of signatures, interpretations, handlers, complete results and
observations. Those definitions are normative for the parameterized laws;
a native consumer must supply an instance and establish its connection to
actual execution. The native contracts above define the implemented surfaces.
Formal profiles supply informative examples and separate proof subjects,
without selecting another native execution path.
[Correspondence maps](../../formal/docs/README.md#definitions-and-proofs) identify
exact Lean declarations and their premises.

## Conformance

A claim names its actual source or artifact, accepted inputs, interpretation,
result or observation relation, and applicable limits. State failures and
residual state when they are observable. Do not substitute a theorem about a
different subject or a successful finite test for a missing implementation law.
[Assurance](../assurance.md) defines the evidence policy; the
[writing guide](../development/documentation.md#writing-specifications) defines
editorial rules.
