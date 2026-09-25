# Operation catalog and domain extensions

This guide describes the selected library and domain-extension boundaries. A
supported declaration alone is not an executed protocol.
[Protocol compilation](protocol-pipeline.md) defines the representation stages,
and the [semantic domains](../spec/domains/values.md) define meanings.

## Library definitions versus operations

An authored protocol owns roles, messages, challenge positions, public loop
counts, dependencies and acceptance. A local function owns one participant's
calculation. A dependency instantiates a protocol definition; an invocation
connects ordered inputs and results at a particular call site. An IPA is a
protocol dependency because it exchanges commitments and challenges. Computing
its cross terms is a local function, and the resulting MSM is a domain operation.

The trace and aggregated-range sources use this same distinction. There is no
trace-proof, range-proof or whole-IPA runtime kernel. Their claim connections,
degree checks, range equation and final opening/IPA checks remain inspectable.
A verifier's two Boolean results must both reach acceptance; merely placing two
protocol calls beside one another does not connect their subjects or conclusions.

Choose the extension level by the information its consumers need:

| Addition | Appropriate carrier | Reason |
|---|---|---|
| Another sumcheck or interactive opening algorithm | Source functions and protocol dependencies | Preserve its rounds, challenges and terminal obligations |
| A matrix contraction, polynomial object or group MSM | Domain operation and mathematical contract | Preserve bulk structure for checking and kernel selection |
| A compatible implementation or storage representation | Physical binding and Rust adapter | Keep the mathematical operation and observation contract fixed |
| Another proof scheme or transcript construction | Explicit semantic choice | Its assumptions, evidence and interaction can differ |
| An optimization fact | Optional operation interface and a consuming analysis | Unknown operations retain their original implementation |

Local functions contain domain operations, nested helper calls and
[structured local control](local-control.md). Helper expansion preserves branches
and loop-carried state; it does not turn a participant-local branch into a global
protocol choice. Public protocol counts and local runtime bounds remain distinct.
These features do not imply an unrestricted dependent shape system.

## Separately checked component interfaces

A reusable component interface needs its actual definition/dependency subject,
ordinary signature and domain requirements. Local computation may be hidden from
a caller analysis that has an established summary. Communication and control must
remain available to participant projection and transcript construction unless a
separate endpoint correspondence supplies that information. Meeting a weak
pre/postcondition alone does not authorize replacing one implementation with
another; replacement needs the selected observation and state relation.

Optional phase, request-count or representation facts are conclusions of a
producer with explicit meaning, not unchecked attributes. Missing facts grant no
optimization; body-aware analysis or ordinary execution can remain available.
Mathematical and security laws use the same actual subjects but retain their own
premises and [execution binding](claim-composition.md). A logical request count
does not bound provider-internal rejection sampling or establish independence.

These are the design boundaries for separate checking. The current compiler
still uses admitted definitions and body-aware consumers; it does not load a
general opaque component-export format. Static proof erasure must retain dynamic
checks and subject associations unless a separate preservation law permits their
removal. In particular, a checked-data wrapper does not prove that arbitrary host
key material belongs to its advertised relation.

A published export and its selected implementation are distinct subjects.
Changing a hidden body requires new conformance evidence, even when its public
signature and promises stay fixed. Interface-only caller reasoning may then be
reused; body-dependent optimization and property evidence require their own
preservation or invalidation. Exact source binding validates which body a fact
concerns; it is not a replacement for checking that body against an export.
Internal analysis DAGs may retain helper dependencies without exposing those
helpers as part of the public signature.

## Dialect boundaries

`pir` carries common interaction and participant execution, including explicit
resource transitions. `algebra` carries field and group operations and finite
linear algebra. `poly` carries polynomial tables, evaluation points, bounded
rounds and general univariate polynomials. `pcs` carries a resolved polynomial
commitment scheme's local contracts. `oracle` carries authenticated table access;
`relation` carries relation declarations, and `claim` carries separately checked
evidence tied to source execution. `plan` records physical choices. These
namespaces are independent of the common, participant and physical compilation
stages.

Logical field/group sequences use dynamic rank-one builtin tensors with nominal
element types. They are not SIMD vectors. Polynomial tables and points retain
distinct types and explicit conversions. Sequence lengths are checked by the
operation contracts; equal tensor ranks do not imply equal lengths. See
[vector semantics](../spec/domains/vectors.md) and MLIR's
[builtin tensor types](https://mlir.llvm.org/docs/Dialects/Builtin/#rankedtensortype).

A new dialect needs a coherent mathematical vocabulary and compiler consumers.
A protocol family or backend name alone is insufficient. Conversely, a domain
operation need not immediately expand into scalar instructions if an installed
cryptographic library implements its full contract efficiently.

## Adding an operation or implementation

This checklist owns cross-layer contract obligations. The
[extension guide](../development/extensions.md) owns file locations, pass
registration and build/test commands.

1. Define the mathematical inputs, results, associated domains, attribute
   meanings and failure conditions. Include shape checks, canonical encodings,
   resource transitions and evidence/assumption boundaries where applicable.
2. Install the source binding signature and typed MLIR operation. The
   [kernel declarations](../../compiler/include/zkc/Dialect/Kernels.td) supply ODS
   structure; the binding/verifier layer checks resolved contracts. A same-named
   operation or same-width representation does not establish compatibility.
3. Install nominal facts, codecs and applicable representations in the immutable
   [domain catalog](../../compiler/include/zkc/Protocol/Domains.h). Catalog
   membership is separate from a kernel implementation and its semantics.
4. If the operation or a new logical type has authoring notation, add its
   operator spelling to
   [`Operators.h`](../../compiler/lib/Frontend/Semantics/Operators.h) and its type name to
   [`Types.h`](../../compiler/lib/Frontend/Semantics/Types.h). Notation belongs to the
   domain's definition; these frontend tables are its temporary home until the
   catalog is grouped by domain. A spelling is compared with the installed
   signature where it is used, and
   [`frontend_data.py`](../../compiler/test/frontend_data.py) compares every
   entry with its named call.
5. Implement Rust admission, native advertisement, checked operands/results and
   external-library execution. Bound sizes before allocation and reject length
   mismatch instead of silently truncating iteration. Private resource handles
   retain actual frame, generation, domain and budget checks.
6. Add the independent Lean signature/interpretation and reference behavior at
   the promised scope. Field/vector arithmetic can execute directly; a trusted
   group or PCS primitive requires an explicit typed request/reply contract.
   Unknown physical accounting must refuse rather than inherit a nearby case.
7. Run positive and hostile examples through actual source, construction,
   participant checking and execution. Compare independent contract inventories
   and observations. A declaration test does not establish executed coverage.

The maintained `tests/physical/test_physical_bindings.py` exercises alternate table
representations through all three consumers, including operations that have no
table input. `tests/artifact/test_composable_domains.py` joins that inventory check
to domain, resource and artifact execution; both state cases over the one
comparison in `tests/support/binding_comparison.py`. Test public primitive configuration separately:
an operation's mathematical domain need not consume every setup key authorized
by the enclosing artifact. Unused authorized keys remain validated; their presence
must not select another curve or disable an unrelated operation.

The interactive protocol catalog and the finite closed-source
[`SourceLibraryInterface`](libraries.md) serve different source carriers. They
do not become interchangeable by sharing terminology. Domain metadata is owned
installation data; it does not load arbitrary plugins from an artifact. C++,
Rust and Lean retain independent validation rather than generating every checker
from one executable implementation.

## Optional shared analysis

The first consumer recognizes a diagonal map followed by linear contractions:
componentwise field multiplication followed by dot products, or scaling group
bases followed by MSMs. The same finite module law moves factors into the scalar
coefficients. Its implementation queries
[operation interfaces](../../compiler/include/zkc/Interfaces/LinearContraction.td),
not protocol names. This follows MLIR's
[interface-based extension mechanism](https://mlir.llvm.org/docs/Interfaces/).

Eligibility requires every use of the diagonal result to be a compatible values
operand in the same local block, with exact nominal domains and no escape or
nested diagonal representation. Physical selection retains the producer,
consumers, checks and operation origins. Explicit incompatible choices and
unsupported interfaces retain materialization. Construction must preserve local
computation boundaries sufficiently for the analysis to reach executed code.

The algebraic justification is
[`linearCombination_smul`](../../formal/Zkc/Algebra/LinearCombination.lean).
Ordered matrix and Kronecker laws cover related contractions. They do not prove
allocation or failure equivalence. Current diagonal accounting charges factors,
backing and the view, which exceeds the dense result's charged size. Selection
is opt-in, and comparisons require sufficient capacity. Exhaustion is tested
separately; no reduced-memory claim follows from avoiding an allocation.

Mathematical purity also does not imply safe speculation: failed checks,
allocation, transcript transitions and foreign stops remain observable. The
operations therefore do not acquire MLIR purity/speculation traits from their
algebra alone. See the [MLIR effect rationale](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/).

## Assumptions and remaining extensions

The [folded-contraction example](../../examples/protocols/folded-contraction.pir)
adds a numerical-only contrast. Its generic functions spell out folding and
weighted contraction using existing field/vector operations. Configurations
select `koala-bear`; the functions do not select a provider. Physical planning
resolves the installed `plonky3/<contract>` implementations. The same definitions
are exercised at BLS and Ristretto scalar fields. Changing the field changes the
mathematical instance; it is not a drop-in replacement of a commitment or
transcript scheme.

KoalaBear supports scalar arithmetic, vectors, matrices, coefficient polynomials and
quadratic rounds. Its field identity does not supply an MLE table, point, group,
PCS or diagonal representation. Authenticated tables use separately named
commitment domains. The Rust domain catalogue has optional group/transcript
associations, and the Lean executable separates arithmetic domains from service
domains. Plonky3 implements the numerical kernels;
independent Lean `ZMod` and Python integer calculations check this bounded path.
No generic interaction/projection change or new dialect was necessary.

The nominal octic extension `koala-bear.ext8-binomial3` reuses these five arithmetic
carriers with explicit `field.embed<E>` from `E.BaseField`, requiring
`ExtensionField(E)`. It has no `PrimeField` capability. Its independent Lean
coordinate interpreter is separate from the prime-only `ZMod` reference and
asserts no new field instance. See the [field contract](../spec/domains/values.md#nominal-field-extensions)
and [canonical eight-coordinate codec](artifact-format.md#octic-koalabear-extension).
The current installation also supplies Merkle row commitments over the base and
extension fields, an extension-field Merlin transcript with bounded-index draws,
and an extension-field index-randomness capability. These are explicit catalog
contracts, not consequences of being a field. FRI is authored from protocol and
domain operations rather than installed as an opaque service.

The BLS path uses Arkworks and the Ristretto path uses curve25519-dalek. The host
authorizes actual setup material, generator suites, statement values and context.
Binding arbitrary generator bytes does not establish unknown discrete-log
relations. The artifact transcript has zkc framing; upstream Bulletproofs byte
interoperability is a separate native experiment.

Broader shape inference, structured PCS alternatives,
cross-call representation lifetime analysis, secrecy-aware kernel selection and
cost-guided search remain extensions. Add them around a demonstrated consumer and
their corresponding laws. A new domain or protocol should not require changes
to generic role projection, loop execution or dependency binding.

## Executed extension costs

The committed linear-relation component adds constrained source algorithms and
protocol composition over the existing matrix/vector/group interfaces. The same
generic bodies run over BLS12-381 and Ristretto255. It adds no primitive catalog
entry and changes no generic pass.
Its Lean laws use a fixed linear map and an explicit MSM/matrix product map;
source/native adequacy and probabilistic security remain separate.

The [public MSM implementation](../runtime/public-msm.md) changes a physical
choice in the same Ristretto domain. Its explicit public-operand premise is
checked at the artifact role boundary; it is not inferred from the spelling `V`.
The second transcript construction changes the nominal suite over the existing
BLS scalar field, with independent framing and new artifact identity. These are
three distinct extension levels.

The three-role component experiment also records a current source limitation:
child call signatures are checked against their declared roles before instance
mapping. A sole child-role renaming through the instance map therefore refuses;
a separately declared child with the intended role works while sharing all local
algorithms. This is bounded three-role support, not arbitrary role substitution.
General role substitution requires a capture/availability and resource-scope law
and independent source/projection tests before relaxing admission.
