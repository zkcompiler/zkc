# Protocol compiler

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `compiler`
> **Authority:** None during the transition. Current compiler semantics remain
> governed by the [Compiler Core specification](../../docs/spec/compiler.md).

## Purpose

`compiler/` owns checked changes to protocol semantics: finite candidate
domains, transformations, legality, constraints, objectives, deterministic
selection, and independently rechecked decisions.

This is the protocol compiler, not a name for the entire zkc pipeline.

## Owns

- artifact authentication at compiler ingress through an exact adapter;
- finite domain providers and comparison scope;
- transform families, applications, plans, lineage, and candidate realization;
- protocol-semantic legality and preservation constraints;
- use of property-judgment results in constraints and objectives;
- objective values, comparison, scoring, and deterministic selection;
- compiler requests, plans, candidates, results, and decision checking; and
- provider-specific protocol transformations as separate profiles beneath the
  generic compiler contract.

The term “transform realization” must remain distinct from downstream target
realization. Compiler realization constructs a candidate semantic protocol;
target realization implements an already fixed endpoint.

## Does not own

- relation compilation or relation satisfaction;
- PIR structure, seal authority, or artifact identity;
- the meaning or truth of property judgments it consumes;
- PIR-to-OIR projection;
- backend lowering, code generation, deployment, or invocation;
- compiler UI and command-line behavior as semantic definitions; or
- test outcomes and performance measurements.

Successful transformation produces a new Open PIR subject. It must cross the
ordinary PIR seal boundary and cannot inherit the input's sealed identity.

## Dependencies

- `foundation/` for exact authorities, identity, and immutable capabilities;
- `pir/` for input and output protocol semantics;
- `judgments/` for typed properties, derivations, and result interpretation;
  and
- `relations/` for explicit prerequisites that transformations may preserve or
  require.

The compiler must not depend on endpoints for ordinary protocol selection.
Endpoint feasibility can enter only through an explicit, owned constraint—not
through hidden knowledge of a backend implementation.

## Consumers and outputs

- PIR consumes transformed outputs for re-sealing;
- endpoints may project any resulting Sealed PIR;
- evidence records decision parity, provider behavior, and performance at
  exact scope; and
- guides expose author and operator workflows.

## Bridge ownership

`compiler/` owns how authenticated PIR and property results become candidate
constraints, objectives, and selection decisions. It does not own the upstream
meaning of either input.

The compiler-to-PIR return is an explicit lifecycle edge: output is Open PIR,
and PIR owns subsequent seal and identity.

## Candidate internal topics

- compiler request and authenticated ingress;
- finite domains and provider contracts;
- transform plans, application, and lineage;
- legality and preservation;
- judgment-aware constraints;
- objectives, comparison scope, and selection;
- decision checking; and
- provider-specific transform families.

## Open boundary questions

- Which constraints are generic compiler legality and which are properties
  delegated to `judgments/`?
- Should provider-specific profiles live beneath compiler or beside the
  protocol families they transform?
- How should endpoint feasibility be represented without coupling the compiler
  to a concrete target realizer?
- Which compiler artifacts require persisted identities, rather than remaining
  transient checked values?
