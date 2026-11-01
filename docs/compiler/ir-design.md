# IR ownership and development direction

The design uses one mixed MLIR program at each semantic stage. zkc owns the
meaning standard MLIR does not supply; standard dialects own ordinary functions,
control, shaped iteration and, when admitted, machine storage and instructions.
A dialect is a vocabulary with one semantic owner. A profile is an admitted
combination of vocabularies. A checked transition relates two actual programs.
These are different boundaries, not three copies of the program.

The [architecture](../architecture.md) describes the implementation,
[status](../status.md) records its coverage, and the [roadmap](../roadmap.md)
orders further work. The future layers below are design commitments with entry
conditions, not registered dialects or supported protocol claims.

## Current semantic owners

| Owner | Abstraction and information retained |
|---|---|
| Protocol | Roles, source-relative action occurrences, communication, draws, statements, completion and repeated interaction |
| Algebra | Nominal field/group values, exact arithmetic and finite mathematical computations; machine integers do not substitute for field semantics |
| Poly | Formal polynomial and quotient-ring values, domains, bases and evaluation structure before concrete realization |
| Data | All logical collection types (bulk vectors, matrices, arrays, sequences and bytes), aggregates, variants, domains and explicit ordering; no authentication or oracle claim follows from a container |
| Relation | Relation declarations/assets, public/witness layout and deterministic interpretation; imported syntax remains an adapter concern |
| Commitment | Scheme-specific types and attributes with exact setup/domain parameters; installed commitment/opening actions use Exec bindings |
| Crypto | Cryptographic types and attributes, with installed primitive actions through Exec; a hash invocation is not itself a random-oracle security judgment |
| Exec | Ordered fallible numerical execution, explicit returned/stopped outcomes, scoped computation invocations and retained finite requests |
| Residue | Canonical modular representatives with exact modulus, word width, unsigned projection and lifts; distinct from nominal fields and strict byte codecs |
| Runtime | Logical binding declarations, resource custody and selected installed implementations/representations; Host authorization remains separate |

Computation units are standard modules/functions admitted by
[`exec.computation`](../spec/ir/computation.md), not another dialect. Their
formation, normalization, scoped realization and independent comparisons belong
to `Transforms/Computation`. Physical kernels are installed implementations,
not the owners of mathematical source semantics.

Keep Algebra and Poly distinct while polynomial identities, degrees, evaluation
bases and quotient laws have consumers that coefficient arrays cannot supply.
Keep Exec and Runtime distinct: ordered computation can be represented before a
target is installed, whereas physical bindings describe a selected execution
contract. Source-language `local fn` and `protocol.local_call` remain meaningful;
they do not imply a Local dialect or a second executable route.

## Use standard MLIR at its own abstraction

| Standard facility | Current use or condition for expansion |
|---|---|
| Builtin / Func | Symbols, isolated closed numerical units and ordinary function signatures; semantic profile admission checks the entire closure |
| SCF / CF | Checked structured numerical schedules followed by scoped control flow; explicit outcome values carry stops through nested regions |
| Arith | Admitted Boolean/index control and arithmetic with its declared widths; nominal field operations stay Algebra until representation is established |
| Tensor / Linalg | Private rank-one maps and selected exact sums with Algebra payloads, admitted indexing maps and explicit common-extent premises |
| Vector | Actual pointwise word candidates after exact widening; bounded independent interpretation of lane arithmetic and poison isolation |
| MemRef / Bufferization | Actual One-Shot private candidates, with independent bounds, initialization, alias, lifetime and fresh-return checks; reached allocation/publication stay in the numerical Call |
| Transform / PDL | Future transformation selection and matching over admitted payloads; scripts never become evidence that their output is correct |

The current [structured tensor profile](../spec/ir/mathematics.md#structured-tensor-computations)
uses upstream fusion and region CSE while an IR-level reader reconstructs the
actual candidate independently. The reader admits every operation, including
unused work, and returns a transient scalar interpretation. Source correspondence
compares that interpretation, retaining input coordinates, nominal fields and
ordered expression operands. Transforms cannot supply producer annotations as
proof of admission. Mutation requires a new read. Production lane realization consumes this profile
for row-bearing native maps and selected sums; product maps share it, while
row-free fills retain a separate scalar profile. Ordered length guards and the
final original-to-payload comparison remain at the execution boundary.

Standard [`linalg.generic`](https://mlir.llvm.org/docs/Dialects/Linalg/) exposes
iteration and indexing to upstream transformations. Extending the admitted
profile requires laws and reader support for the resulting forms. Passing
MLIR verification alone does not discharge equal-length premises or the
source-to-candidate relation.

Do not change upstream semantics with ignored attributes. A field residue is
not an integer merely because both occupy 64 bits. A source stop is not poison,
undefined behavior, or a return from inside an SCF region. Dynamic logical
indices have their declared widths and range checks; machine `index` width is a
target decision. Unknown effects stay conservative until a valid interface model
allows optimization. MLIR [effect/speculation interfaces](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
help generic passes reason about operations; protocol observations and affine
custody still need their own checks.

The admission boundary matters even for mathematical operations. A bounded read
can be speculatable only in the profile that has established its bound premises.
Structural formation alone must not let generic folding erase an inadmissible
dormant body before that check. Ordered invocations keep conservative effects;
introducing a more precise memory resource does not grant freedom to move a
challenge, change the first failure, or remove a reached charge. Use a shared
ordering resource alongside finer storage effects if a real consumer needs the
precision. A new effect-token dialect is not required.

Data owns both generic `data.sequence<T>` and specialized vectors, matrices and
arrays. These carry distinct observable admission and layout contracts: a
mathematical field array is not a private fixed vector, and a matrix retains
both extents. One collection interface exposes element/shape observations;
Algebra owns scalar domains and arithmetic on them. Runtime and targets select
physical storage without erasing mathematical distinctions. Old Algebra
collection classes, operation owners and parser aliases are removed.

## Transformation and component contracts

Use ODS for operation/type/property definitions, symbol interfaces for symbol
uses, and external interfaces when adding analysis behavior to standard
operations. Add an interface for a real shared consumer, with semantic
preconditions; a trait name cannot manufacture totality or erasability.
Mandatory profile admission and reusable actual-body interpretation belong to
IR. Transformation-specific comparisons may stay beside a transformation with
separate implementation and checked dependencies on its semantic readers. Producers,
heuristics and upstream rewrites belong to Transforms. Translation owns source
emission and artifact export. Compiler composes these components; none of their
lower layers calls the driver or backend to decide formation.

Each pass declares every dialect it may create, including temporary candidates,
and keeps invocation state local. Numerical selection has one typed option
schema shared by preparation, projection, demand formation, realization and
physical selection. Factory arguments, copied pipelines and textual pipelines
retain all fields. The [MLIR pass contract](https://mlir.llvm.org/docs/PassManagement/)
also constrains traversal/mutation under parallel execution. Optional trace and
statistics observers are caller-owned synchronous instrumentation, not a shared
analysis cache or an authorization channel.

Internal synchronous diagnostic captures and speculative suppressors handle
only the installing thread's emissions and forward diagnostics from sibling
invocations. A context-wide collector belongs to the owner of the entire
execution context, including any worker diagnostics it must collect.

Direct transformation APIs initialize the same dialect dependencies as their
pass wrappers, before parallel execution. Registered dialects need not already
be loaded. Symbol import uses collision-safe substitutions even when an existing
binding is reused; fresh final names alone do not prevent a replacement from
rewriting references introduced by another replacement.

Dialect dependencies also cover types and attributes constructed by verifiers,
so parsing in a lazily loaded context is sufficient. Internal diagnostic
capture is local to the invoking thread; unrelated diagnostics on a shared
context must pass through to their owner. A transformation cannot suppress a
sibling invocation's required error while testing an optional proposal.

A producer works on a private candidate; a separate comparison checks that
candidate against the retained source before publication. Analysis results bind
to their actual subjects and invalidate on mutation. Do not keep an editable
parallel graph, a persisted approval bit, or both old and new owners. For
representation lowering, use explicit
[conversion legality and type conversion](https://mlir.llvm.org/docs/DialectConversion/)
where applicable, followed by profile admission and semantic comparison. Full
conversion proves only that the declared conversion target was reached.

Prefer reusable expression, index, shape, region and occurrence relations as
checker coverage grows. Avoid recognizing one producer's exact instruction
spelling when the admitted semantics permit equivalent structure. Conversely,
do not silently enlarge the theorem or implementation profile to accept an
upstream rewrite that the reader does not understand.

### Infrastructure before widening optimization

Explicit stage admission and one stage pipeline builder are common to direct,
textual and production routes. An admitted
profile names its operation vocabulary, semantic attributes, premises and
comparison relation; enabling an entire standard dialect is too coarse.

| Mechanism | Adoption boundary |
|---|---|
| ODS, typed accessors, symbol/call/branch interfaces | Default structural implementation where the interface describes the actual ABI or successors |
| AnalysisManager | Owner-scoped reusable facts, with dependency-aware invalidation; direct calls compute fresh facts or explicitly invalidate |
| RewritePattern / PatternRewriter | Local transformations inside an admitted candidate profile |
| ConversionTarget / TypeConverter | Actual vocabulary or representation changes; never a substitute for read-only admission or correspondence |
| DataFlowSolver | Monotone availability/range problems with defined transfer functions; exact custody and resource roots keep their own validators |
| InferType / shape and integer-range interfaces | Derived result facts with concrete consumers; range facts do not manufacture source premises or security proofs |
| Transform / PDL | Reusable schedules over an independently admitted payload, when schedule reuse justifies the extra surface |
| BufferizableOpInterface / destination style | Used by admitted private tiles; broader forms require aliasing, allocation, refusal and custody relations |

Whole-module projection, protocol construction and realization remain structured
algorithms where their global obligations demand it. They still use standard
symbols, builders and pass orchestration. Adding interfaces with no truthful
model or consumer would increase maintenance without making the compiler more
native to MLIR.

Keep public native views separate from neutral export/comparison adapters as
those boundaries are retired. Analysis objects borrow actual IR; serialized
records own their data. Pointer-returning summaries require stable storage across
cache growth, and dependency depth is semantic path height rather than the order
in which a traversal happened to encounter cached nodes. Bound structure before
calling recursive upstream utilities. Split large files by semantic invariant
and consumer, not arbitrary line counts; preserve the acyclic Source/Contracts/
Program, IR, Translation/Transforms, Compiler component boundaries.

## Information that must survive future transitions

| Information | Required consumer and preservation boundary |
|---|---|
| Nominal fields, extension basis, polynomial degree/basis/axes | Algebra/Poly analysis, transcript encodings and physical representations |
| Statement and witness layouts, ordered children and variant alternatives | Source/IR comparison, commitment context, independent program readers and Host input binding |
| Actual receives, draw occurrences and dynamic iteration coordinates | Projection, transcript construction, observations and security interpretation |
| Ideal oracle identity, dynamic anchor and query order | Protocol oracle operations and current realization comparison; broader claim interpretation remains pending |
| Virtual oracle dependencies and authentication dominance | Planned realization records; every answer use is justified after its relevant check |
| Logical queries, unique openings, challenge blocks and primitive hash calls | Separate cost/security counts; batching must not identify these quantities |
| Lookup multiplicities, active masks, scope and table identity | Planned constraint interpretation; finite-field sums alone do not preserve natural multiplicity |
| Memory chronology, initialization and final-state conditions | Planned chronological-memory constraints; a generic bag of rows is insufficient |
| Exact encoding, domain separation, setup and challenge provenance | Codec/commitment/transcript consumers; canonical bytes and authority are distinct facts |
| Primitive dependencies and shared primitive identities | Required before admitting hashing relations/internal verifiers; transparent dependencies are derived and opaque assumptions are explicit |
| Centered representatives and norm bounds | Quotient/lattice operations; modular equality alone does not establish a norm bound |
| Accumulated residuals and final decider | Future folding/recursion contracts; an intermediate accumulator is not acceptance |
| Disclosure, observation and adversarial access | Future privacy/security analyses; sending an entire table is not private oracle access |
| Ordered refusals, resource roots and consumed prefixes | Exec, physical selection and runtime; equal results under sufficient capacity do not imply equal exhaustion |

Most of the oracle, lookup, memory and privacy consumers in this table are future
work. They must become typed operands, types, properties or checked immutable
records at the responsible stage before a transformation can erase their inputs.
Origin labels and free-form metadata cannot substitute for the actual relation.
A record names its producer, consumers, invalidation condition and lowering point.

Derive occurrence and interaction information from actual Protocol/control IR.
Source application paths, dynamic iteration coordinates, oracle instance identity,
SSA aliases and artifact digests are different identities. Shared extraction may
serve several consumers, but separate encoders and independently checked judgments
retain their contracts. The application map records associations; it is not a
second authored interaction graph or evidence of an admissible schedule.

Oracle integration must connect acceptance to the actual root/anchor, setup,
domain, position and authenticated answer. Recomputing an obligation report does
not discharge its predicates, and producing an ignored verification Boolean does
not establish a claim. A checked helper/body relation can enforce that connection;
introduce a typed authenticated result only if it has a complete producer and
consumer interpretation. Physical opening sharing must preserve logical query
multiplicity, dependencies, stopped prefixes and answer-publication rules.

## Target architecture and boundaries

The planned route is checked source → prepared mathematical protocol → checked
cryptographic realization → participant projection/construction → scoped
execution → target representation → checked artifact. Cryptographic realization
and target realization establish different relations. Exact mathematical
rewrites preserve values; relation encodings require all-assignment adequacy;
cryptographic replacements require a stated adversarial experiment and reduction.
No generic “verified” marker joins those obligations.

Each connection names its actual input/output subjects, independent reader or
regeneration check, formal consumer and remaining trust. Native implementation
completion and formal closure are separate milestones. A source export or a
byte digest binds a subject without proving the exporter or reader correct.
The [delivery plan](../roadmap.md#shared-interfaces-before-implementation) assigns
the compiler inputs and formal consumers for the source, realization and byte
connections.

Logical oracle kinds and operations belong to Protocol, generic containers to
Data, and concrete schemes to Commitment. Ideal data access, commitment opening,
and a random-oracle model are three different concepts. Initial oracle shape
admission should use static or initially bound statement/configuration counts
under an explicit maximum; challenge-adaptive shapes require a separately
specified extension and matching formal consumer. This restriction belongs to
that oracle profile, not to every Data domain or executable loop.

Residue is now a concrete owner with checked word/tile and CPU-plan consumers.
Two additional semantic owners have prospective consumers:

- **Constraint:** assignment predicates, lookup/multiset and chronological-memory
  structure. Move existing assignment-level ownership here when the encoding
  consumers land, retaining Relation as the statement/declaration interface.
  Do not keep two canonical AIR/R1CS representations. The migration includes
  complete declared Clean ensemble and LLZK executable profiles, all existing
  consumers, and the removal of replaced assignment implementations. Partial
  witness computation is separate from validity for arbitrary assignments.
  Public/fixed/witness/auxiliary projections, ensemble interactions, row scopes
  and padding remain semantic data, not adapter annotations.
- **Codec:** exact logical-value/byte relations shared by transcript, commitment,
  wire and recursive-verification consumers. Runtime still implements the
  independently installed physical codecs.

These are ownership decisions; a new dialect namespace requires an actual
operation set and checked consumers. The represented-execution decision keeps
Residue projection/lifts separate from strict codecs, whose current owners
remain the installed runtime and exact encoding contracts. A later Codec IR
requires a shared consumer of those relations, not wrappers around existing
bindings. Data owns logical collections; Poly retains nominal polynomial
domains and bases.

[Serialization boundaries](serialization.md) apply to every new owner. Native
Constraint analyses must consume assignment operations and typed facts directly;
Clean/LLZK adapters translate at their ingress, and independent consumers receive
explicit semantic projections. MLIR bytecode is the compiler checkpoint format.
An interchange report must not become a second canonical assignment program or
an input to a native optimization. Any new external format needs a named consumer,
strict admission and cross-boundary tests. Existing Bundle/runtime/formal contracts
are replaced only together with their consumers, without a fallback route.

Delivery order does not impose representation order. Constraints consume exact
logical assignments and relation assets before information-erasing physical
lowering even though their migration follows represented execution. The STARK
construction retains logical terms and public/witness maps at that ingress;
later encodings consume them directly instead of reconstructing them from
emitted machine programs.

Construction-specific encoding contracts are fixed when their first consumer
lands, including statement/root binding, witness framing and request/state
semantics. Later Codec ownership consolidates those exact meanings with their
consumers; it does not create a competing byte language.

Introduce these namespaces with operations and checked consumers, not empty
registrations. Per-algorithm Falcon, lattice, FRI, folding or transcript dialects
are unnecessary merely to name a library. A new family warrants a dialect when
it has distinct laws and a durable abstraction boundary that existing owners
cannot express without semantic ambiguity.

Target selection branches from a common checked closure before native resident
handles. Preserve domains, setup authority, widths, explicit outcomes and complete
layouts for EVM and later targets. Standard bufferization can inform private
storage lowering, but its [alias and ownership analysis](https://mlir.llvm.org/docs/Bufferization/)
does not establish zkc scope custody or observable resource refusal.

The [EVM target](../spec/targets/evm.md) reads the same Data collection types
through its native layout owner. Its word lanes, coefficient buffers and exact
wire permissions are target-specific interpretations of those logical values.
They do not consume CPU numerical plans or inherit the CPU tile limits. Keep
installed field facts and complete logical layouts common; keep storage,
instruction selection and reached resource accounting with each target.

A selected installation restricts independently known contracts throughout
compiler selection and final validation, including defaults, explicit choices,
fallback, conversions, table relayout, nested layouts and codecs. Candidate
preferences are separate from installation authority. Runtime owns the frozen
installation; compiler integration preserves its restrictions at every route.
The CPU implementation uses the immutable `CpuTarget` descriptor paired with
`CpuInstallation`. Its provider restrictions travel with the numerical policy
through pass cloning, proposal and independent final validation; selecting the
explicit-vector mode does not restore a withheld provider. See the
[CPU installation contract](../../crates/zkc-cpu/README.md#provider-composition).

External dialects remain useful at bounded adapters where their semantics match.
The [represented-arithmetic decision](../rationale/represented-arithmetic.md)
selects an owned Residue boundary after a bounded HEIR comparison;
Clean and LLZK are acceptance clients of the constraint/relation redesign;
CirC remains a comparison point. Clean's ensemble obligations must survive
extraction, and LLZK's mutable object identity cannot be treated as an immutable
logical aggregate. Reassess current upstream semantics and toolchains before
choosing direct dialect reuse or an adapter. Compare
conversion laws, pin/build costs, independent validation and performance with an
owned implementation. Learning from external designs does not remove maintenance
of our own implementation. Transform/PDL may later describe profitable schedules,
with [payload interpretation and handle validity](https://mlir.llvm.org/docs/Dialects/Transform/)
kept separate from semantic validation. AOT remains a separately researched target,
not a hidden prerequisite for this architecture.

## Alternatives and remaining cost

A standard-only IR would obscure nominal domains, cryptographic premises and
observable stops. A custom-only stack would duplicate well-supported control,
shape and transformation infrastructure. Separate editable protocol, numerical
and schedule graphs would add synchronization and invalidation obligations.
The mixed-profile design shares standard structure while preserving the facts
that each checked transition actually needs.

This choice still costs maintenance: actual-body readers must evolve with the
admitted rewrite space, retained sources consume memory, and strict admission
can refuse valid but unsupported forms. Lowering too early loses optimization
opportunities; retaining every abstraction indefinitely enlarges every consumer.
The lowering point is therefore the last consumer that needs the information,
with an explicit checked interpretation for later stages. The
[delivery criteria](../roadmap.md#acceptance-across-units) make these ownership,
invalidation and removal obligations explicit for each implementation unit.
Revisit a dialect split when its consumers and laws converge, and revisit
external reuse when measured benefit exceeds its conversion and dependency costs.
