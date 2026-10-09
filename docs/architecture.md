# Architecture

zkc uses one compilation and execution model. `.zkc` Language emits mathematical
MLIR, which passes through `protocol`, `participant`, `exec` and `physical`
profiles and is exported as `zkc.program/0`. Entry packages, proof deployments
and joint bundles execute through the same Rust Runner and installed kernels.

## System map

```text
explicit .zkc modules + Assets                 direct mathematical MLIR
              │                                          │
           Language ─────────────────────────────────────┤
                                                         ▼
                  protocol → participant → exec → physical
                                                         │
                                                   zkc.program/0
                                                         │
                          authenticated Entry / proof / joint Host
                                                         │
                                              shared Rust Runner
                                                         │
                                            installed backend kernels

Lean: independently formalized semantic models and proofs
      (native source/compiler/runtime correspondence remains open)
```

Source Assets capture immutable relation data. They do not install a relation
checker or infer proof obligations merely by appearing in a project. The
[relation ingress guide](compiler/relations.md) distinguishes data import,
relation declarations, library-level multi-table bundles and external adapters.

## Representation and checking

| Boundary | Responsibility |
|---|---|
| `.zkc` modules and Entry closure | Names, static parameters, types, permissions, capabilities, role availability and explicit application selection |
| `protocol` | Mathematical values, joint actions, services, relation declarations and participant dependencies |
| `participant` | Role-specific values, actual sends/receives, ordered actions and optional transcript construction |
| `exec` | Demand-driven mathematical realization and explicit executable local calls |
| `physical` | Admitted representations, installed kernels, conversions and storage handling |
| `zkc.program/0` | Closed executable participant description admitted by C++ export and Rust loading |
| Host package | Application-authorized identity, input/result layout, setup authority, execution limits and publication |

The [pipeline](compiler/pipeline.md) explains the transitions. Each
[adjacent preservation check](compiler/verification.md) reads actual candidate
operands and control against retained input. Source checking, IR formation,
transformation correspondence and runtime admission establish different facts.
Unknown or unsupported cases refuse; successful formation is not a security
judgment.

## Implementation owners

| Owner | Home and responsibility |
|---|---|
| Support and Contracts | `compiler/include/zkc/Support` and `Contracts`: diagnostics, closed types, domains, ring expressions, operations, effects and implementations |
| Language | `compiler/include/zkc/Language`: explicit modules/Assets, checked definitions, static application and Entry closure |
| Relation | `compiler/include/zkc/Relation`: R1CS/AIR data, relation bundles, staged predicates, normalization and evaluation |
| Program | `compiler/include/zkc/Program`: executable model, codec and structural admission |
| IR | `compiler/include/zkc/Dialect`: mathematical dialects, interfaces and mandatory profile verification |
| Translation | `compiler/include/zkc/Translation`: Language emission/comparison, relation import and checked program export |
| Transforms and Target | `compiler/include/zkc/Transforms` and `Target`: preparation, projection, realization and physical selection |
| Compiler | `compiler/include/zkc/Compiler`: composed compilation, Entry packages, bundles and proof deployments |
| Driver | `compiler/include/zkc/Driver`: command parsing and file I/O; links the Compiler API |
| Rust runtime | [zkc-runtime](../crates/zkc-runtime/README.md): Runner, bounded work and resource custody |
| Rust Hosts | [zkc-tools](../crates/zkc-tools/README.md): Entry, proof and joint invocation, authentication, preparation and reports |
| Backend integration | [zkc-backends](../crates/zkc-backends/README.md): installed types, codecs, services and kernel dispatch |
| Lean | [formal](../formal/README.md): independently built semantic models, proofs and model-specific tools |

The exported CMake components follow these responsibilities; the
[compiler package](../compiler/README.md#components-and-ownership) owns the exact installed API.
MLIR-free services sit below IR. Translation and Transforms depend on IR;
Compiler composes them. Driver code handles command-line I/O. Component
checks and installed consumers enforce this direction.

## Runtime and application authority

An Entry package retains the source interface, original mathematical program,
compilation choices and selected artifact. A trusted application supplies the
expected package digest. The Rust Host binds named inputs to the independently
admitted program; it trusts the compiler publication for source correspondence.
It does not interpret the retained MLIR.

The native proof policy covers flat, iterated, PCS and structured
programs on the shared executable and Runner. [Proof compilation](compiler/construction.md)
owns construction within the participant profile. [Exact identity](runtime/artifact-identity.md)
binds the authorized bytes and invocation context. No normalized identity policy
is supplied by this implementation.

Hosts prepare inputs and setup material before issuing execution resources.
The `--evaluators` manifest supplies application-authorized ring arenas; each
arena is admitted and matched to the content digest fixed by the program.
Arena bodies remain Host assets, outside the compiler's current IR analysis.
They retain actual message contents, reached failures, resource consumption and
cleanup outcomes. A validator's acceptance comes from its selected decision,
not from producer completion. Entry input associations and the Host registry
authorize setup material. Explicit verifier-key-consuming PCS operations enforce
the protocol's expected setup; an authorized receive may be observed before
that check. See the [setup boundary](spec/formats/messages.md#application-authorized-setups),
including unchecked returned PCS values.

## Formal models and extension boundaries

Lean models define complete execution, observations, conditional refinement and
selected protocol experiments. Their direct plans, finite tables and source
representations remain independent research subjects. They are not stages of
the native compiler, and their executable correspondence results do not validate
`zkc.program/0`. [Assurance](assurance.md) owns that distinction.

Extensions add ordinary mathematical operations, transparent local algorithms,
protocol libraries or backend kernels at the appropriate owner. A whole-protocol
runtime callback would hide the computation the compiler needs to analyze.
New formats, codecs, services and transformations need explicit contracts and
actual admission/behavior checks. The [extension guide](development/extensions.md)
explains the workflow and when to settle cross-component contracts. The
[system-boundary rationale](rationale/architecture.md) explains the language and
component split.
