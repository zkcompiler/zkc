# Architecture

The `.zkc` frontend checks application functions and participant protocols.
Entry control uses standard MLIR functions and structured control, with an
`entry` dialect for typed value assembly, numerical calls and deployments.
Protocol IR (PIR) retains participant mathematics and interaction. Both numerical
Entry helpers and participant computation use the existing Kernel, physical
lowering and VM; the Host does not implement a second arithmetic interpreter.

## System map

```text
explicit .zkc modules + Assets
              │
           frontend
              ├── Entry functions → func/scf + entry operations → zkc.host/0
              │                            │                         │
              │                      numerical helpers              │
              └── Protocol IR              │                  Entry Host
                    protocol               │                   ordered calls
                       ↓                   │                         │
                    participant            │                  proof / joint Host
                       ↓                   ↓                         │
                    exec / Kernel → physical → zkc.program/0 ────────┘
                                                    │
                                       interpreter + VM instance
                                                    │
                                       installed backend operations

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
| Entry control | Static application calls, ordinary data and ordered Host invocations; numerical islands remain separate |
| `protocol` | Mathematical values, joint actions, services, relation declarations and participant dependencies |
| `participant` | Role-specific values, actual sends/receives, ordered actions and optional transcript construction |
| `exec` | Demand-driven Kernel units and ordered Local calls; checked numerical realization |
| `physical` | Admitted representations, installed operations, conversions and storage handling |
| `zkc.program/0` | Closed participant or numerical function description admitted by C++ export and Rust loading |
| Host package | Application-authorized identity, input/result layout, setup authority, execution limits and publication |

PIR is the umbrella for these profiles and their cooperating dialects;
`protocol` names one profile and the interaction dialect, not the entire IR.
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
| IR | `compiler/include/zkc/Dialect`: mathematical and Entry dialects, interfaces and mandatory verification |
| Translation | `compiler/include/zkc/Translation`: Language emission/comparison, relation import and checked program export |
| Transforms and Target | `compiler/include/zkc/Transforms` and `Target`: preparation, projection, realization and physical selection |
| Compiler | `compiler/include/zkc/Compiler`: composed compilation, Entry packages, bundles and proof deployments |
| Driver | `compiler/include/zkc/Driver`: command parsing and file I/O; links the Compiler API |
| Rust VM | [zkc-runtime::vm](../crates/zkc-runtime/src/vm/README.md): admitted code, installed-call contracts, frames and capacity |
| Rust interpreter | `zkc-runtime::interpreter`: instruction walking, continuations and pending participant actions |
| Rust Hosts | [zkc-tools](../crates/zkc-tools/README.md): Entry, proof and joint invocation, authentication, preparation and reports |
| Backend integration | [zkc-backends](../crates/zkc-backends/README.md): installed types, codecs, services and kernel dispatch |
| Lean | [formal](../lean/README.md): independently built semantic models, proofs and model-specific tools |

The exported CMake components follow these responsibilities; the
[compiler package](../compiler/README.md#components-and-ownership) owns the exact installed API.
MLIR-free services sit below IR. Translation and Transforms depend on IR;
Compiler composes them. Driver code handles command-line I/O. Component
checks and installed consumers enforce this direction.

## Runtime and application authority

An Entry package retains the source interface, original checked IR,
compilation choices and selected artifact. Local source commands trust the
selected project and compiler and capture the returned package bytes. Deployed
applications supply an independently authorized expected package digest.
The Rust Host binds named inputs to the independently
admitted program; it trusts the compiler publication for source correspondence.
It does not interpret the retained MLIR. Structural admission produces an immutable
VM program without a backend. Each execution links its owned backend and uses a
VM instance for frames, calls, resource custody and budgets. The interpreter
walks structured instructions and manages value environments and continuations.
The [VM contract](spec/runtime/vm.md) defines their boundary. Entry control links those native numerical, proof and joint owners; it neither
interprets retained MLIR nor installs its own mathematical kernels. Its shared
ledger accounts for cumulative work and simultaneous parent/child value storage.

[Kernel IR](spec/ir/kernel.md) owns closed logical numerical units, using existing
mathematical operations and standard functions. Ordered Local calls invoke them;
physical planning retains their source and selected Local realization together.
Independent numerical and physical readers check the result before publication.
This boundary keeps the complete numerical body available independently of
participant control.
Normalization, analysis and recipe verification read standard-function bodies;
Local functions are the executable output. Source symbol context and output
binding allocation remain separate.
Numerical realization chooses native contractions, compact pointwise expressions,
bulk vector operations or a private standard SCF schedule before Local lowering.
The native expression handlers borrow typed columns and scalar captures,
evaluate bounded row chunks, and construct private results through the existing
numerical scope. They share provider-packed slice arithmetic with dense vector
kernels, without a new VM instruction or executable format. Compiler-generated
writable-buffer layouts and target vector IR remain future work.
Participant scheduling, transport and resource authority stay with their existing owners.
Installed numerical and effectful operations share the binding mechanism;
installation alone does not authorize extraction into a numerical unit.

The native proof policy covers flat, iterated, PCS and structured
programs on the shared executable and Runner. [Proof compilation](compiler/construction.md)
owns construction within the participant profile. [Exact identity](runtime/artifact-identity.md)
binds the authorized bytes and invocation context. No normalized identity policy
is supplied by this implementation.

Hosts prepare inputs and setup material before issuing execution resources.
The authenticated Entry package carries the ring arenas its program references;
each arena is admitted and matched to the content digest fixed by the program
before any invocation. The compiler also admits captured bodies and derives
static dimensions. Their arithmetic remains in assets referenced by IR;
generic IR transformations do not yet traverse those bodies.
They retain actual message contents, reached failures, resource consumption and
cleanup outcomes. A validator's acceptance comes from its selected decision,
not from producer completion. Entry input associations and the Host registry
authorize setup material. Explicit verifier-key-consuming PCS operations enforce
the protocol's expected setup; an authorized receive may be observed before
that check. See the [setup boundary](spec/formats/messages.md#application-authorized-setups),
including unchecked returned PCS values.

## Formal models and extension boundaries

Lean models define complete execution, observations, conditional refinement and
selected protocol experiments. Maintained native bridges check selected exported
subjects against these models. They are not stages of the native compiler and
do not establish general correctness of `zkc.program/0` execution or its backends.
[Formal support](../lean/docs/support.md) records their exact scope;
[assurance](assurance.md) owns the remaining trust boundaries.

Extensions add ordinary mathematical operations, transparent local algorithms,
protocol libraries or backend kernels at the appropriate owner. A whole-protocol
runtime callback would hide the computation the compiler needs to analyze.
New formats, codecs, services and transformations need explicit contracts and
actual admission/behavior checks. The [extension guide](development/extensions.md)
explains the workflow and when to settle cross-component contracts. The
[system-boundary rationale](rationale/architecture.md) explains the language and
component split.
