# Architecture

The `.zkc` frontend checks application functions and participant protocols.
Entry control uses standard MLIR functions and CFG branches, with Data for
logical value assembly and Exec for fallible numerical calls and deployments.
Exec outcomes explicitly distinguish returned values from terminal stops.
Protocol IR (PIR) retains participant mathematics and interaction. Both numerical
Entry helpers and participant computation use the existing numerical, physical
lowering and VM on CPU. The Host does not implement a second arithmetic
interpreter. The EVM target consumes the same checked verifier closure through
its own machine lowering and does not use the native VM.

## System map

```text
explicit .zkc modules + Assets
              │
           frontend
              ├── Entry functions → func/cf + Data/Exec boundaries → zkc.host/0
              │                            │                         │
              │                      numerical helpers              │
              └── Protocol IR              │                  Entry Host
                    protocol               │                   ordered calls
                       ↓                   │                         │
                    participant            │                  proof / joint Host
                       ↓                   ↓                         │
                    checked exec / runtime
                       ├── CPU → physical → zkc.program/0 ────────────┘
                       │                         │
                       │            interpreter + VM instance
                       │                         │
                       │            installed backend operations
                       └── EVM verifier → words/slices → Yul → solc → bytecode

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
| `exec` | Scoped Func/CF execution, explicit outcomes and typed mathematical requests; checked numerical realization |
| `physical` | Admitted representations, installed operations, conversions and storage handling |
| EVM target | Selected checked verifier closure, bounded words/slices, ordered effects, canonical ABI and Yul publication |
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
| Source and Syntax | `compiler/include/zkc/Source` and `Syntax`: immutable source revisions, lossless layout syntax and formatting |
| Language | `compiler/include/zkc/Language`: explicit modules/Assets, checked definitions, static application and Entry closure |
| Relation | `compiler/include/zkc/Relation`: R1CS/AIR data, relation bundles, staged predicates, normalization and evaluation |
| Program | `compiler/include/zkc/Program`: executable model, codec and structural admission |
| IR | `compiler/include/zkc/Dialect`: mathematical, Data and Exec dialects, interfaces and mandatory verification |
| Translation | `compiler/include/zkc/Translation`: Language emission/comparison, relation import and checked program export |
| Transforms and common Compiler | `compiler/include/zkc/Transforms` and `Compiler`: preparation, projection, realization, proof construction and checked endpoint closure |
| CPU target | `compiler/include/zkc/Target/Cpu`: physical selection, native compilation, Entry packages, bundles and proof deployments |
| EVM target | `compiler/include/zkc/Target/Evm`: verifier legality, word/slice lowering and Yul; independent of CPU selection |
| Driver | `compiler/include/zkc/Driver`: command parsing and file I/O; composes common Compiler and machine targets |
| Rust VM | [zkc-runtime::vm](../crates/zkc-runtime/src/vm/README.md): admitted code, installed-call contracts, frames and capacity |
| Rust interpreter | `zkc-runtime::interpreter`: instruction walking, continuations and pending participant actions |
| Portable formats | [zkc-format](../crates/zkc-format/README.md): canonical logical trees, lazy proof framing and immutable invocation bindings, without execution authority |
| Rust Host drivers | `zkc-runtime::host::{joint,proof,wire}`: ordered scheduling, proof transport, completion, cancellation and bounded reports |
| Rust command-line application | [zkc-cli](../crates/zkc-cli/README.md): arguments, presentation, command orchestration and manifest recipes |
| Rust application Hosts | [zkc](../crates/zkc/README.md): Entry, proof and joint authority, authentication, preparation and publication |
| Browser adapter | [zkc-web](../crates/zkc-web/README.md): in-memory SDK proof calls, Wasm bindings and a dedicated Worker boundary |
| Mathematical kernels | [zkc-kernels](../crates/zkc-kernels/README.md): typed arithmetic, transforms, commitments, curve operations and scoped numerical storage |
| Backend integration | [zkc-cpu](../crates/zkc-cpu/README.md): installed types, codecs, services and kernel dispatch |
| Lean | [formal](../lean/README.md): independently built semantic models, proofs and model-specific tools |

The exported CMake components follow these responsibilities; the
[compiler package](../compiler/README.md#components-and-ownership) owns the exact installed API.
MLIR-free services sit below IR. Translation and Transforms depend on IR;
Common Compiler composes them. CPU and EVM targets consume that boundary;
common compilation does not depend on either target. Driver code handles
command-line I/O. Component checks and installed consumers enforce this direction.

## Runtime and application authority

The Rust boundaries separate application policy, machine execution and
mathematical computation. Hosts own package and setup authorization, input
assembly, publication and transport outcomes. The VM owns frames, installed
call contracts, resource custody and execution budgets; the interpreter walks
its admitted instructions. The CPU backend owns concrete values, exact
physical ports, codecs and effectful services. Mathematical kernels receive
typed operands and explicit computation limits, without VM values, resource
stores, transcript sessions or Host authority. Independent kernel code and the
VM do not depend on each other; CPU adapters connect them.

`zkc-format` contains the syntax and immutable byte operations shared by metadata
consumers and execution. It has no runtime or kernel dependency. Selecting a
proof frame or parsing a logical tree grants no authority; native admission,
resource reservations and capability transitions stay with their existing owners.

The reusable drivers live in `zkc-runtime::host`, separately from the VM and
interpreter, without native or kernel dependencies. `host::wire::WireBackend`
supplies installed complete-type support, fixed widths, encoding/decoding bounds
and value codecs. `ProofBackend` adds borrowed raw bytes and Boolean acceptance
projection. `zkc-cpu` implements these contracts with a selected view of its compiled CPU catalog.
`CpuInstallation` fixes a provider subset before admission and keeps the same
catalog layout identities. The compiler's optional `CpuTarget` is a subtractive
selection constraint over independently known contracts. Neither descriptor
installs an operation or changes the VM's representation-neutral contracts.
The shared SDK owns memory document decoding and numerical material loading;
file/project adapters and browser transport sit outside that semantic path.

Artifacts cannot register codecs; the independently installed physical type
determines its admitted codec.

Host-owned `WireError` distinguishes invalid received data, capacity exhaustion
and trusted adapter failures. Invalid data is an accepted Decode stop; capacity
or adapter failure leaves the receive unaccepted. Unsupported measurement fails
closed. Applications supply authenticated bindings and acceptance selectors;
the drivers grant no package, deployment, setup or public-input authority.

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
interprets retained MLIR nor installs its own mathematical kernels. Admission
binds each target to its installed owner and result schema; deployment bindings
also retain setup authority and the selected proof operation. Execution uses
these bindings without reinterpreting the serialized carrier. Its shared ledger
accounts for cumulative work and simultaneous parent/child value storage.

[Numerical units](spec/ir/computation.md) use standard `builtin.module` and
`func.func` with the explicitly checked `exec.computation` profile and existing
mathematical operations. Ordered Local calls invoke them;
physical planning retains their source and selected scoped realization together.
Independent numerical and physical readers check the result before publication.
This boundary keeps the complete numerical body available independently of
participant control.
Normalization, analysis and recipe verification read standard-function bodies;
Scoped standard functions are the executable output. Source symbol context and output
binding allocation remain separate.
Numerical realization chooses native contractions, compact pointwise expressions,
bulk vector operations or a private standard SCF schedule before scoped CFG lowering.
Retained pointwise maps and selected sums first use standard Tensor/Linalg
computations with exact Algebra scalar regions. The IR Analysis component independently reads the
actual transformed packet and its source formula before the native handler
adapter consumes that packet; final numerical readback remains independent.
The native expression handlers borrow typed columns and scalar captures,
evaluate bounded row chunks, and construct private results through the existing
numerical scope. They share provider-packed slice arithmetic with dense vector
kernels, without a new VM instruction or executable format. Compiler-generated
writable-buffer layouts and target vector IR remain future work.
Participant scheduling, transport and resource authority stay with their existing owners.
The [IR ownership design](compiler/ir-design.md) explains current abstractions,
standard MLIR use and the semantic boundaries reserved for future work.
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
