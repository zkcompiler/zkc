# Specification

This reference defines the native `.zkc` → Protocol IR → `zkc.program/0`
path, its application interfaces, and the mathematical contracts used to describe
it. Definitions are normative within their stated parameters and premises.
Examples are informative. [Status](../status.md) records implemented coverage.

The [shared contract register](contracts.md) records semantic owners, producers,
consumers, identity domains and cross-subsystem integration gates.

## Native contracts

| Subject | Contract |
|---|---|
| Source language | [Definitions, types, bodies, Entries and translation](language/README.md) |
| Protocol IR | [Profiles](ir/protocols.md), [mathematics](ir/mathematics.md), [numerical units](ir/computation.md), [polynomial recipes](ir/polynomials.md) |
| Foundation cutover | [Native ownership and semantics](ir/native-foundation.md), [interface changes](formats/foundation-interfaces.md), [shared catalog](formats/contract-declarations.md), [logical types](formats/logical-types.md), [application map](formats/application-map.md); target contracts with support tracked separately |
| Composition and control | [Applications](ir/composition.md), [iteration](ir/iteration.md), [finite computations](ir/finite.md), [functions](ir/functions.md), [control](ir/control.md), [completion](ir/completion.md) |
| Data | [Variants](ir/variants.md), [nested data](ir/data.md) |
| Construction and analysis | [Interactions](ir/interactions.md), [execution observations](ir/execution-observations.md), [protocol observations](ir/protocol-observations.md), [transcripts](ir/construction.md), [native index blocks](formats/native-index-block.md), [construction obligations](ir/construction-obligations.md), [checked binding](ir/construction-binding.md), [public-coin views](ir/public-coin.md), [compiler limits](ir/limits.md) |
| Serialized artifacts | [Program](formats/program.md), [oracle realization](formats/oracle-realization.md), [Entry package and interface](formats/entry.md), [proof deployment and transport](formats/proof.md), [message frames and setups](formats/messages.md) |
| Formal import | [structured source](formats/structured-source.md): original protocol-stage units with helpers, participants, contracts, applications and repeats; [constructed validator](formats/constructed-participant.md): a checked proof candidate's validator participant |
| Host execution | [Entries](runtime/entries.md), [joint bundles](runtime/joint.md), [proofs](runtime/proofs.md), [attempts](runtime/attempts.md), [services](runtime/services.md) |
| EVM target | [Checked verifier lowering, canonical ABI, effects, ceilings and artifact identity](targets/evm.md) |
| Operational boundaries | [VM execution](runtime/vm.md), [numerical calls](runtime/numerical.md), [capacity](runtime/capacity.md), [file admission and publication](runtime/publication.md) |

The four MLIR profiles constrain one program at successive compilation
boundaries; they are not four dialects. An artifact's structural admission does
not establish its derivation from source. Boundary versions follow the
[format policy](../development/maintenance.md#format-versions); all zkc-owned formats remain at version `0` before stabilization. A specified
schema does not imply an implemented producer or independent consumer.

See the [cross-component contract register](contracts.md) for owners, producers,
independent consumers and the assurance/stage vocabularies.

## Mathematical and checking contracts

These chapters define parameterized objects, laws and obligations. A native
consumer must fix the relevant interpretation, inputs, states and capacity
premises. A law alone does not prove that a C++ checker or Rust kernel realizes it.

| Subject | Contract and native use |
|---|---|
| Values and domains | [Values](domains/values.md), [vectors](domains/vectors.md), [permutations](domains/permutations.md): typed algebra, contractions, representations and cryptographic permutations |
| Shape and bounds | [Mathematical facts](domains/mathematical-facts.md): exact subjects, scoped premises, cardinality and bounded derivation |
| Polynomial meaning | [Tables and polynomials](domains/polynomials.md), [negacyclic quotient rings](domains/quotient-rings.md), [prepared quotient matrices](domains/quotient-matrices.md), [shared ring expressions](domains/ring-expressions.md): formal substitution, polynomial SSA and recipe lowering |
| Ordered execution | [Exec outcomes](ir/execution.md): return/stop propagation, Data values and independently checked Func/CF structure |
| Relations and authentication | [Constraints](domains/constraints.md), [relation bundles](domains/relation-bundles.md), [oracles](domains/oracles.md), [STARK reduction](domains/stark.md), [relation terminals](relations.md): imported assets, multi-table relations, binding and explicit terminal checks |
| Representation | [Canonical residues](ir/residues.md), [Complete results](realization/representations.md), [codecs](realization/codecs.md), [artifacts](realization/artifacts.md): source comparison, wire admission and retained authority |
| External constructions | [Hash-chain and duplex transitions](realization/external-constructions.md): explicit native primitive calls |
| Validation | [Refinement](verification/refinement.md), [analysis](verification/analysis.md), [judgments](verification/judgments.md): the obligations of source-relative checking |

The mathematical chapters specify parameterized obligations over signatures,
interpretations, handlers, complete results and observations. A native consumer
must supply an instance and establish its connection to actual execution.
The current [formal reference](../../lean/docs/README.md) mechanizes selected
models and protocol connections; [formal support](../../lean/docs/support.md)
identifies their exact claims. Unmechanized native contracts remain obligations,
not implicit theorems of the Lean package.

## Conformance

A claim names its actual source or artifact, accepted inputs, interpretation,
result or observation relation, and applicable limits. State failures and
residual state when they are observable. Do not substitute a theorem about a
different subject or a successful finite test for a missing implementation law.
[Assurance](../assurance.md) defines the evidence policy; the
[writing guide](../development/documentation.md#writing-specifications) defines
editorial rules.
