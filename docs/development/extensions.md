# Compiler, runtime and integration maintenance

This guide maps an implementation change to its owners and checks. The
[specification](../spec/README.md) owns meaning; [status](../status.md) owns
support claims. Source-language authoring belongs to the
[language guide](../language/README.md).

Static contributions, concrete value variants and explicit dispatch are
deliberate. A new abstraction should remove a current
duplication or dependency problem. Use modules before new crates; group code by
its responsibility rather than creating a namespace for every protocol or
upstream library.

## Extend the built-in vocabulary

Most additions belong in the existing tree. Choose the smallest boundary that
expresses the change; a source module, a logical family and an MLIR dialect need
not have the same boundaries.

| Addition | Author here | Additional work |
|---|---|---|
| Helper composed from existing operations | An ordinary `.pir` library | Import it and check its body; no compiler registration |
| Primitive on existing types | The owning `Contracts/Declarations/*.td` and ODS operation | Independent runtime/Lean admission and a native signature/handler if executable |
| New logical type | A typed declaration and its domain's `TypeBindings.td` | Logical properties, representations, independent interpretation, and concrete value handling when needed |
| New nominal instance | The catalog in `lib/Contracts/Domains.cpp` | Independent identity/association/codec facts and provider support; a type declaration alone does not install a field |
| New native dialect | Per-dialect header/implementation and `BuiltinIR.cmake` | ODS subject inclusion, component source ownership and independent registration tests |
| Alternative implementation | Native bindings, kernels and physical selection | Same operation contract, exact nominal arguments, representation and security requirements |
| IR transformation | Analysis/conversion/transform implementation and pass factory | Input/output stage, retained observations and failure behavior |
| Host application or command | `zkc-tools` application module and thin binary | Explicit inputs, setup authority, checker and execution configuration |
| External formal correspondence | `formal/integrations` package | Exact upstream subject, theorem and hypotheses |

For example, a polynomial primitive normally extends
[`Declarations/Polynomial.td`](../../compiler/include/zkc/Contracts/Declarations/Polynomial.td),
its polynomial ODS operation, runtime
[`operations/poly.rs`](../../crates/zkc-runtime/src/interactive/operations/poly.rs),
backend [`bindings/poly.rs`](../../crates/zkc-backends/src/bindings/poly.rs) and the
appropriate kernel table/handler, and Lean
[`Bindings/Polynomial.lean`](../../formal/Tools/Interactive/Bindings/Polynomial.lean).
Each location owns a different interpretation. A provider-independent operation
does not need a new dialect or a provider-specific source API.

For a primitive, complete the following checks at the affected boundaries:

- Logical formation, source exports and native IR mappings, including unsupported
  domains and malformed arguments. These can succeed without an installed backend.
- Independent runtime and Lean interpretations, with accepted/refused conformance
  cases. Include the operation's numerical or state-transition behavior, beyond
  signature agreement.
- Exact physical selection and native execution, including default/alternative
  results and failures where executable support is claimed.
- Copy/drop/custody and resource lifecycle, public-operand premises, and applicable
  codec/transcript behavior. A new type or implementation grants none implicitly.

Generated metadata and matching signatures do not establish a numerical equation
or cryptographic security.

## Logical contracts and source exports

The neutral typed records under
[`include/zkc/Contracts/Declarations`](../../compiler/include/zkc/Contracts/Declarations)
own the installed logical declarations. `zkc-tblgen` generates the static
descriptor inventory exposed by
[`Declarations.h`](../../compiler/include/zkc/Contracts/Declarations.h).
The schema references typed roots, associated projections, type applications and
capability predicates; it does not parse signatures from an embedded string
language or define a second checker. Contracts and Frontend remain MLIR-free.

For a supported primitive or export:

1. Define its logical signature, ordered requirements, parameter schema and
   authoring stage in the owning contract records. Keep semantic equations and
   parameter validators in their reviewed implementations. Type records own
   copy/drop/custody permissions; history transitions are separate explicit
   input/output facts, including for copyable external schedule values. Operations
   retain the conservative `local` effect envelope, without a totality promise.
2. Add curated source exports that refer to that contract, with public argument
   labels. Type exports, sort-based associated `Element` projections and finite
   `Vector`/`Matrix` cases also use generated metadata. Add an installed operator
   binding only with an unambiguous constructor tuple and port bijection.
3. Connect the existing IR adapter, representations, independent admission and
   implementations at their owning boundaries. High-level algebra, polynomial
   and group operations retain their backend-independent contracts and bulk
   structure. Adding an export does not require inventing another dialect.
4. Check declaration conflicts and inventory agreement, source import/alias and
   stage refusals, IR mappings and the affected independent consumers. Generator
   agreement alone does not validate an interpreter or prove a semantic law.

Installed source modules use ordinary resolution under `zkc::algebra`, `poly`,
`curve`, `random`, `pcs`, `oracle`, `external`, `core` and `transcript`. A `use`
declaration exposes names from the static installation; it cannot install
semantics or native code. Transcript operations are construction-only and are
not source exports. Explicit `bind` applies the same stage restriction in an
authored module. Existing external schedule adapters remain source-callable;
their use alone does not establish construction provenance.

The installation retains its existing whole-installation identity. Domain
identities, raw sorts and capability predicates remain globally accepted; this
does not replace the domain catalog. Logical types support ordered Domain, Type
and Nat arguments through source checking, common admission and native MLIR.
The compiler, Rust runtime and Lean reader maintain independent interpretations.
Adding a declaration generates compiler metadata and source exports; it does not
generate a runtime kernel, a codec or a proof. No dynamic plugin loader or stable
plugin ABI is supplied.

Ordinary source helpers and `#[operator(...)]` functions on package-owned records
need no compiler registration. Their [source rules](../language/data.md#4-operators)
still check bodies, ownership and coherence.

### Add a logical type and operations

Use [FixedVector](../../examples/protocols/fixed-vector.pir) as a complete extension
example. `FixedVector<T, N>` is one bulk value with an exact-length invariant;
the source aggregate `[T; N]` still expands to N ports. The compiler's general
parser and operator dispatcher contain no fixed-vector case.

1. Add a `ZKC_Type` with typed parameters and explicit copy/drop/custody facts,
   plus `ZKC_Operation` signatures and curated exports in
   [the declaration directory](../../compiler/include/zkc/Contracts/Declarations).
   Nested applications use typed `ZKC_Apply` references in the existing scope
   DAG; natural constants use `ZKC_Natural`. Numerical parameter validators name
   the field term they use. Generator checks reject conflicting ownership,
   malformed references and kind mismatches.
   Applied constructors currently use private or affine custody; the generator
   refuses public custody without a complete-type codec model. A well-formed
   type need not have a constructor operation or a backend representation.
2. Define logical formation independently of representation. Atomic nominal
   pairs belong to `DomainCatalog`; structural applications are checked from
   constructor parameter kinds. Define the independent Rust and Lean type and
   signature interpretations. Preserve all arguments, canonical spelling,
   conditional resource permissions and shared parsing limits.
3. Add the useful native MLIR type and operations to their domain dialect. Bind
   ODS operations to exact logical declarations. Declare a direct, custom or
   unavailable type binding in the owning `TypeBindings.td`; generation checks
   complete coverage and creates registration. A direct helper declares its
   native type and parameter kinds, checked by C++ assertions. Custom codecs
   name their native heads and must preserve the complete type in both
   directions. Shared heads require unique runtime encoding; ambiguity refuses.
   `VariantSyntax` has separate explicit coverage. Registration cannot silently
   load a dialect or reinterpret an unknown type as PCS data.
4. Add exact representation support and implementation policy in Contracts, then
   runtime custody and native kernels. `TypeRepresentations` owns structural
   representation patterns; `ImplementationCatalog` owns selectable operations,
   provider applicability, layout overrides and defaults. Neither derives
   permission from a name prefix. Add codecs only when wire behavior is defined.
   Atomic catalog rows and structural representation patterns have disjoint
   keys. Both pass through common type admission. Structural patterns currently
   provide exact nested types and bounded natural ranges; arbitrary layout
   overrides and codecs for applied types require an explicit extension.
5. Extend independent conformance and execution cases. Test both an executable
   instance and a logically well-formed instance without a backend. Include
   wrong kinds, malformed naturals, length failures, resource permissions and
   unavailable observation. Test expected IR mappings independently of the
   generated mapping itself.

The example installs `fixed_vector.from_vector`, `fixed_vector.to_vector` and
`fixed_vector.dot`. Its KoalaBear implementation uses Plonky3 field arithmetic;
Lean independently computes the dot product. A BLS scalar vector is logically
admitted but has no fixed-vector implementation. Fixed vectors have no installed
codec, so protocols communicate supported outputs such as the scalar result,
not the bulk value. This boundary is deliberate and is checked at admission.

The declaration inventory is inert input to the conformance corpus. It cannot
teach the runtime or Lean a new contract. Those consumers resolve each request
through their own installed definitions. See
[the extension tests](../../tests/protocol/test_domain_extension.py) and
[contract conformance](../../tests/protocol/test_contract_conformance.py).
The [installed-domain example](../../compiler/examples/domain/README.md) checks
new source vocabulary, generic Type/Nat multi-results, domain bounds and nested
native types in a separately built compiler installation. The same consumer
against a base installation rejects the absent vocabulary. No catalog object is
replaced at link time.

### Compose a compiler installation

Keep an external contribution's neutral declarations, ODS, native helpers and
CMake file together. Configure the compiler with an explicit
`ZKC_CONTRIBUTION_FILES` list; each file calls `zkc_add_contribution` with its
identifier, dependencies, declaration/binding fragments, include roots and
native sources. It may also provide transform sources and generation targets.
Ordinary MLIR CMake handles dialect generation. Contributed IR sources join
`ZkcIR`; transform sources join `ZkcTransforms`. Neutral Contracts and Frontend
remain MLIR-free.

Use `ZKCDialect` for mapped operations and include `Properties.h` before generated
dialect declarations. The mapping generator rejects plain dialect registration,
replacement of its inherited strict registration hook, missing or mistyped
`site`, `parameters` and `binding` properties, and generated
`prop-dict` parsers that bypass strict property conversion. A handwritten parser
must preserve the same refusal behavior. A contributed kernel may override the
base coarse operand constraint, but must retain these properties and the shared
logical verifier. Use include guards on neutral fragments, which native ODS
includes again. Apply the operation-name filter to both ODS declaration and
definition generation; otherwise it redeclares base operations.
To extend a dialect's `extraClassDeclaration`, concatenate
`ZkcStrictPropertyRegistration` with the additional C++ declarations; replacing
the hook would restore MLIR's permissive property behavior.

`HEADERS` supplies declarations to the installation's dialect registration, not
to every base type consumer. Adapter fragments are generated privately as
`zkc/Dialect/TypeAdapters/<OwnerRecord>.inc`. Contribution sources inherit their
component's warnings-as-errors policy. Public headers must compile independently.

Source `.h`, `.hpp`, `.def`, `.inc` and `.td` files under each include root
form a finite public inventory. CMake reconfigures when that inventory changes. Public symlink headers retain
their include spelling while ownership follows the physical file.
Register generated `.h.inc` outputs in `PUBLIC_HEADERS` and uninstalled
`.cpp.inc` outputs in `GENERATED_SOURCES`, before generation. Register internal
headers outside the public include roots in `PRIVATE_HEADERS`; they are checked
but never installed. `TRANSFORM_HEADERS` assigns public, private or generated
files to Transforms; other files belong to IR. All paths participate in ownership
and collision checks. Use a contribution-owned include namespace: `zkc/` is
reserved for core headers and central generators. Installation copies only the
admitted public inventory. Generated files are selected only by the explicit
output lists; stale files in a reused build tree are ignored, and including an
unregistered generated file still fails the component check.

`LINK_LIBRARIES` and `TRANSFORM_LINK_LIBRARIES` assign private external
dependencies to the corresponding component. Use `PUBLIC_LINK_LIBRARIES` or
`PUBLIC_TRANSFORM_LINK_LIBRARIES` when a public API requires the dependency's
usage requirements. Each entry names an imported target; in-project
implementations belong in the source lists. Also list the packages that create
those targets in `FIND_DEPENDENCIES`. The installed configuration finds them
before loading the exported targets. Ordinary CMake search paths select the
installed dependency prefixes. Static archives retain their private link
requirements; shared libraries do not expose them as public API dependencies.

Visible imported link interfaces cannot introduce core compiler/LLVM/MLIR
targets or locally built helper targets. The bounded interface accepts nested
`LINK_ONLY`, `BUILD_INTERFACE` and `INSTALL_INTERFACE` wrappers, configuration
branches, existing library files and ordinary transitive platform libraries.
Unsupported expressions refuse. This checks declared interfaces, not external
binary contents or later deliberate target mutations. The component checks
inspect contribution sources, public/private headers and generated includes;
cross-contribution C++ includes require a declared transitive dependency.
Contribution CMake is trusted build code, not a sandbox.

Assembly preserves the base inventory order, then orders contributions by
`DEPENDS` and identifier, and their declarations by semantic keys. Missing or
cyclic dependencies, duplicate owners and undeclared neutral declaration or
C++ include dependencies refuse. `DEPENDS` governs this assembly; contribution
CMake files still execute in the configured list order. Native TableGen commands
use ordinary CMake include roots and generation-target dependencies, which their
authors must specify. This API does not infer build order or ownership of
arbitrary upstream ODS records. Source text cannot request a new installation.
Extending an installation changes its captured declaration environment; this
is not a new cross-installation identity scheme.

There is one generated declaration object and one native adapter assembly per
installation, with the same ownership under static and shared linkage. Installed
`zkc-tblgen` and relocatable TableGen inputs can validate further declarations.
Adding native code requires building a new installation, then consuming that
prefix. This is a same-version build integration mechanism; it does not graft
registrations onto an already linked compiler.

Run `just test-install-domain` for the opt-in base/extended installation check,
or `just test-install-domain shared` for shared linkage. It uses fresh installation
and consumer directories, checks exact test completion, and confirms that the
same checked library captures different declaration environments in the two
installations. It also checks component ownership on both actual compiler builds,
including contributed sources, without enabling the complete test graph. This
focused check is separate from the default test suite. Pass both `--runtime`
(the native `zkc` executable) and `--checker` (Lean `interactive-protocol`) to
include restored participant admission, correspondence and execution in the
consumer CTest inventory. Missing explicitly requested tools fail the check.

### Independent execution and reference owners

Rust runtime operation families under
[`interactive/operations`](../../crates/zkc-runtime/src/interactive/operations)
and Lean families under
[`Interactive/Bindings`](../../formal/Tools/Interactive/Bindings) author their
own admission equations. Each assembles an immutable exact registry and rejects
duplicate owners. Compiler TableGen does not generate either interpretation.
Runtime families own their domain restrictions and physical selection callbacks;
shared support constructs typed ports without dispatching on family-name prefixes.
For example, polynomial domain restrictions live in `operations/poly.rs`, and
transcript payload and codec restrictions live in `operations/transcript.rs`.
Native backend entries separately bind an implementation identity to its
signature, installed security requirements and handler. Dispatch selects that
exact identity after common validation; identical ports need not imply the same
algorithm. `arkworks-pairwise/vector.dot` is an explicitly selected example,
with unchanged default selection. Layout aliases inherit the original handler
and security requirements; an algorithm change supplies a different handler.
Every installed alternative has an execution witness against its original.

Backend kernel tables keep one authored port shape per row, alongside its
execution owner. A family constructor attaches the independent signature
resolver from `zkc-backends/src/bindings`; a mixed arithmetic kernel table need
not become a new domain abstraction. The backend does not call the runtime's
admission equations. Field-literal validation is likewise maintained independently.

Alternative eligibility is explicit per contract and defaults to fixed. Both
registries reject alternatives without an eligible exact owner. Runtime assembly
resolves ownership after collecting all contributions, so declaration order is
irrelevant. Backend alternatives inherit their original resolver and restrictive
public-operand requirements; an alternative cannot become another alternative's
original. Transcript observations remain eligible and retain suite/payload/codec
checks. Both registries compare an alternative's exact first domain argument:
field, group, commitment scheme or transcript suite, rather than just its scalar
field. Representation transforms apply to every matching port, including an
observation's table payload. Challenge derivation, random operations, pairing and embeddings remain
fixed. A new implementation requires reviewing these policies in each reader;
matching port shapes alone do not grant permission.

The backend value remains a flat typed sum. A new payload must add exhaustive
identity, representation, accounting and authority behavior; a new kernel over
existing values does not. One resource store remains authoritative across
families. This mechanism does not make arbitrary Rust/Lean value families or
nominal domains an out-of-tree plugin API.

Source helpers over admitted operations need no primitive registration. An
IR-only specialization may decompose back to those operations. A *new source
primitive* still needs independent source admission and correspondence support;
retained participant binding declarations also require physical admission even
when no invocation remains. Decomposition does not waive those obligations.


## Dialects and operations

[IR.td](../../compiler/include/zkc/Dialect/IR.td) includes the maintained ODS
subjects. Each dialect owns its public `<Name>/IR/<Name>Dialect.h` and its
initialization file under [`lib/Dialect`](../../compiler/lib/Dialect).
[IR.h](../../compiler/include/zkc/Dialect/IR.h) collects shared generated operation
declarations; dialect class declarations live in the per-dialect headers.
Registration and mandatory verification belong to `Zkc::IR`; dialect-local
transformation passes belong to `Zkc::Transforms`; aggregate pass registration
belongs to `Zkc::CompilerCore`. See the [checking boundaries](../compiler/ir-verification.md).
Generated operation declarations stay shared because parent traits cross dialect
boundaries; definitions and registration lists are generated per dialect.
Public dialect queries and verifiers remain extension APIs. Raw construction
helpers under `Dialect/detail/Builders.h` are unsupported same-version details
and do not establish admission. Claim IR structure belongs to IR; the optional
`Zkc::ClaimTranslation` bridge owns source-bound claim import and checking.

For an operation in an existing dialect, edit its ODS definition and verifier.
The generated registration list follows the definition. Bound kernel operations
also declare their logical contract keys on the actual ODS operation record.
`KernelOp` generates forwarding to the shared logical verifier. Coarse native
carrier membership is an explicit list, independent of this registration; new
operations must declare appropriate native constraints.
`zkc-tblgen` generates the contract-to-operation adapter used by IR; Contracts
remains MLIR-free and independently owns signature and implementation legality.
Observation operations enumerate exact typed contract references; a prefix such
as `transcript.observe.*` grants no mapping. Add independent expected mapping and discriminating behavior checks
when extending it: importer/verifier agreement through the same generated map
cannot detect a shared wrong mapping. No purity or cryptographic law is inferred
from this metadata.

A new base dialect also needs:

1. Its public dialect header and initialization implementation.
2. One `namespace|CppOwner|types` (or `none`) record in
   [BuiltinIR.cmake](../../compiler/cmake/BuiltinIR.cmake). Generation, C++ dialect
   registration and loaded-context checks consume that record. Type-adapter
   owner/output pairs live in the same descriptor; an adapter owner need not
   correspond to a dialect.
3. Its ODS subject included by `IR.td`, and an independent namespace/membership
   expectation in [dialect_registration.cpp](../../compiler/test/dialect_registration.cpp).
4. Its source assigned to `ZkcIR` in
   [Components.cmake](../../compiler/cmake/Components.cmake).

The descriptor contains build facts, not semantic support or source eligibility.
It also reserves built-in class names and adapter output names during contribution
assembly, including standalone CMake checks. Empty, duplicate and malformed
records refuse. Generated base/contribution registration fragments are private
to `Registry.cpp` and are not installed; public dialect headers remain installed.

An explicitly assembled contribution adds its dialect classes to both
registration and the installation's loaded-context precondition. Unrelated
optional dialects can still register in a caller's registry without joining that
precondition. Keep reusable public headers under `include/zkc`
and implementations under the matching `lib` area.

An operation's mathematical contract, nominal binding and implementation are
separate. Follow [protocol libraries](../compiler/protocol-libraries.md) for the
interactive contract/physical catalogue. The older closed-source
[SourceLibraryInterface](../compiler/libraries.md) is a different carrier; its
independent [service consumer](../../compiler/examples/service/CMakeLists.txt)
demonstrates that specific extension boundary. Neither mechanism loads arbitrary
code named by an input artifact.

## Passes and pipelines

All built-in factories are declared in
[Passes.h](../../compiler/include/zkc/Transforms/Passes.h); tools call
`registerCompilerPasses()` from `Compiler/Passes.h` explicitly. Each implementation owns its name, options,
description, dialect dependencies and statistics. With this small pass set,
ordinary MLIR C++ definitions remain sufficient; there is no second metadata
catalogue or custom registration framework.

[Pipeline builders](../../compiler/include/zkc/Compiler/Pipelines.h) assemble
passes for both `zkc-compile` and `zkc-opt`. The named optimizer pipelines are:

| Pipeline | Input and result | Options |
|---|---|---|
| `zkc-table-pipeline` | Closed-source logical program to direct/physical table plan | `simplify`, `physical=lazy` or `physical=materialized`; absent physical selection keeps logical values |
| `zkc-participant-pipeline` | Common protocol to projected/physical participants | `project-only`, `linear-contractions`, `release-storage` |

Existing individual pass names remain available. Library callers can build a
pipeline without registering global command-line names. Source-bound explicit
implementation selections are validated against the retained common source
before projection; the builder receives the validated choices. The textual
pipeline uses installed defaults, while its C++ builder also accepts those
caller-selected choices.

When adding a pass:

1. Implement the transformation in its owning conversion, analysis or transform
   area and expose a factory in `Passes.h`.
2. Add that factory to [Passes.cpp](../../compiler/lib/Compiler/Passes.cpp) and
   its implementation to the build. Declare any dialects it can create.
3. State the accepted stage, preconditions, observations and failure behavior
   beside the implementation. Preserve or invalidate analyses explicitly if the
   pass uses MLIR's analysis cache.
4. Change [Pipelines.cpp](../../compiler/lib/Compiler/Pipelines.cpp) when the pass
   belongs in a standard route. Keep file I/O and artifact assembly in the host.
5. Test the transformation, an invalid input/precondition, and affected pipeline
   options. [pass_pipelines.py](../../compiler/test/pass_pipelines.py) checks the
   named routes against the driver, including wrong-stage refusal.

Arithmetic equality does not establish preservation of allocation failures,
resource consumption, messages, challenge order or source-bound evidence.
Operation verification and a successful pass run do not prove these laws. Use
the existing [transformation contracts](../compiler/README.md) for such changes.

Compiler tests remain under CTest: small C++ API tests and Python tool checks.
The existing runner already handles IR input, refusal diagnostics and retained
outputs. A separate lit/FileCheck dependency is deferred until a body of static
IR rewrite cases justifies another test surface.

## Runtime and native implementation

The runtime owns admitted control and backend custody. It has no compiler,
cryptographic-library or subprocess dependency. Its two public execution surfaces
remain distinct: finite `Bindings` execution and interactive `Backend` execution.
See the [runtime map](../../crates/zkc-runtime/README.md).

Within [`zkc-backends`](../../crates/zkc-backends/README.md):

| Module | Responsibility |
|---|---|
| `backend/policy.rs` | Explicit host entry and public-input policy |
| `backend/validation.rs` | Shared entry, operand, attribute and output checks |
| `backend/registry.rs` | Exact implementation assembly and handler ownership |
| `backend/execute.rs`, kernel/provider owners | Standard handlers and module-owned alternative rows |
| `bindings/`, `domains.rs` | Native signature construction and nominal associations |
| `kernels/`, `plonky3/`, `matrix.rs`, `oracle.rs` | Concrete mathematical operations |
| `codec/`, `value.rs` | Canonical wire representation and concrete in-memory values |
| `resource.rs`, `setups.rs`, `transcript.rs` | Authoritative capabilities, setup permission and transcript state |

`NativeBackend::apply` performs common admission, checks public-operand policy,
executes the selected operation, then validates every successful output through
one shared boundary. Kernels still check dependent shapes and preflight expensive
allocations. Failed consumption retains its actual state; frame cleanup runs even
when output validation fails.

An additional implementation supplies a row in its owner module, including
applicability, representation policy and security requirements. A new
mathematical domain can also require changes to the
independent compiler/runtime/Lean catalogues. Do not generate all independent
checks from the native implementation. Retain the concrete `Value` enum and opaque
resource handles unless an actual consumer requires a different representation.

### Add an implementation of an existing contract

1. Confirm that the operation's logical signature and nominal associations already
   exist. A new contract is a coordinated compiler/runtime/Lean change, not just
   another dispatch arm.
2. Put the concrete implementation in the existing kernel or provider module.
   Preserve input validation, output preflight and actual resource consumption
   on refusal or exhaustion.
3. For an alternative, add a native `ALTERNATIVES` row beside its handler. The
   installed registry and native signature construction consume that same row.
   Independently add runtime admission in `interactive/operations/<family>.rs`
   and Lean admission in `Interactive/Bindings/<Family>.lean`; neither imports
   the native row. `backend/validation.rs` remains the shared entry/result
   boundary, and the selected row's public-operand gate runs before its handler.
4. Update the compiler's physical catalogue/selection and representation
   conversions where needed. Update `codec/` only when the representation needs
   a new wire encoding; an alternative algorithm using the same values does not.
5. Run the affected kernel and backend contract tests, then a source-to-physical
   selection/execution test. Include invalid signatures, representation or
   resource limits relevant to the change. Independent reference comparisons
   remain separate evidence from the native implementation's own checks.

Do not introduce an upstream-specific runtime trait or a new crate solely to
follow this sequence. The current backend trait already isolates execution from
native providers; the concrete modules organize its installed implementation.

## Host tools and external integrations

[`zkc-tools`](../../crates/zkc-tools/README.md) separates application modules from
shared `host` mechanics. `host::io` provides bounded reads; `host::process` owns
one-shot child polling, output bounds and direct-child cleanup. Each checker or
application retains its own command arguments, response decoder, limits and error
codes. Cleanup does not establish descendant isolation or a hard disk quota.

The native workspace's [Cargo.toml](../../Cargo.toml) owns dependency versions;
member manifests select their required features. [Cargo.lock](../../Cargo.lock)
locks resolution. Arkworks helpers, native Plonky3 operations, import adapters and
ArkLib formal correspondence retain separate responsibilities. The
[ArkLib package](../../formal/integrations/arklib/README.md) owns its exact theorem
subjects and premises; it is not a native runtime backend.

[Maintenance](maintenance.md) identifies the owning Lake, Cargo, source and Nix
manifests, including independent benchmark workspaces. Version updates need the
checks for the affected integration; changing a transport hash does not change a
mathematical or cryptographic claim. Runtime settings are explicit host inputs;
[environment configuration](configuration.md) owns development paths and tools.

| Integration | Adapter and pin owner | Relevant validation |
|---|---|---|
| Arkworks | `zkc-arkworks`, native kernels; workspace Cargo manifest/lock | Adapter controls, native backend tests, affected host protocol checks |
| Plonky3 | `zkc-backends/src/plonky3`; workspace Cargo manifest/lock | Numerical/codec controls, nominal bindings and physical selection checks |
| ArkLib / VCVio | `formal/integrations/arklib`; its Lake manifest/lock and matching Nix source pins | Separate integration build and theorem consumers, under their stated premises |

Native changes do not require rebuilding the unchanged optional formal package.
An upstream formal pin or adapter theorem change does require that package's
own checks. Likewise, a native library upgrade needs its affected native and
cross-language controls rather than an unrelated formal rebuild.
