# Executable interactive reference

`Tools.Interactive` is the independent portable source interpreter and concrete
candidate checker. It is tooling, outside the reusable `Zkc` library. Lake builds
it as `interactive-protocol`; the whole-package declaration audit explicitly
includes its types and bodies. `Zkc` never imports this consumer.

## Components

| Modules | Responsibility |
|---|---|
| `Syntax`, `Decode`, `Encode` | Bounded portable records, exact shape parsing and response encoding |
| `Admission`, `ReferenceAdmission`, `Requirements`, `Configuration` | Declaration, instance, ownership, type and affine checks; logical resource admission at source boundaries; bounded requirement search; immutable partial configurations |
| `GenericTypes`, `GenericSource`, `GenericModule`, `Specialization`, `Bindings`, `Explicit`, `TypedLocal`, `VariantDescriptor`, `Algorithms` | Formation of the original generic local declarations and their nominal specialization; the installed full-type vocabulary for explicit bindings and its local syntax; reification into the typed region; local sum descriptors; canonical local expansion |
| `Projection`, `GenericValidation`, `LocalValidation`, `PhysicalFormation` | Structural translation validation of a candidate against the source: common-control projection, selected local bodies and selected physical locals |
| `Control`, `ReferenceControl`, `ReferenceRuntime`, `ReferenceValue`, `ReferenceState`, `ReferenceResources`, `GenericReference`, `PhysicalLocal` | Reference execution: source control traversal, resumable role advancement at source cuts, typed local execution, logical values, service state, resource transitions and the bounded physical interpretation of a checked local plan |
| `Field`, `ScalarReference`, `ExtensionReference`, `Sampling`, `MatrixIdentity`, `ServiceDomain` | Executable arithmetic: modular fields and table kernels, the installed prime-field domains, the octic extension, sampling equations, canonical matrix content and installed service domains |
| `ReferenceCommitment`, `CommitmentCodec`, `ReferenceSetups`, `ReferenceOracle`, `OracleReference`, `ReferenceGroups`, `ReferenceTranscript`, `ExternalReference` | Services as logical contracts: commitment custody and scheme identity, setup authority, authenticated rows and the Merkle row reference, group sequences, transcripts and external data-state transitions |
| `Main` | Command interface |

Each command prints one JSON record. A refusal is `["refused", code]` with exit
status 1; a completed check or run exits 0.

| Command | Checks or runs | Record |
|---|---|---|
| `--admit SOURCE` | Source admission with executable bodies | `["checked", "explicit-source-admission", "no-elaboration-adequacy-proof"]` |
| `--declarations SOURCE` | Declaration admission; external signatures are allowed | `["checked", "explicit-declaration-admission", "not-executable-admission"]` |
| `--generic-declarations SOURCE` | Formation of the original generic local declarations | `["checked", "generic-local-formation", "not-whole-source-admission"]` |
| `--check SOURCE CANDIDATE` | Structural correspondence of an exported candidate with the source | `["checked", "generic-structural-correspondence", "no-elaboration-adequacy-proof"]` |
| `--check-generic SOURCE CANDIDATE` | The same correspondence, also returning the port and call mapping | `["checked", "generic-structural-correspondence", PORTS, CALLS, "no-elaboration-adequacy-proof"]` |
| `--check-local SOURCE CONFIGURATION CANDIDATE FUNCTION` | One selected local body against the generic source | `["checked", "generic-local-correspondence", "not-whole-source-admission"]` |
| `--reference SOURCE INPUTS`, `--generic-reference SOURCE INPUTS` | Common-source execution; both spellings run the same interpreter | observation |
| `--generic-role SOURCE INPUTS ROLE` | One role's execution with its ingress taken from the inputs | observation |
| `--physical-local-reference SOURCE CANDIDATE INPUTS STORAGE` | Bounded physical interpretation of a source-checked local plan | observation |

The Rust host's participant checker calls `--check-generic` with the compiler's
exported candidate and uses the returned mapping. The comparison admits both
records and checks independent projection with alpha normalization of SSA names
and participant symbols. Instance, role, function, entry, schema, public
parameter and action-site identities stay exact. Physical representation and
kernel selection are fixed by the installed profile. This checker accepts
structural lowering; it is not an optimization checker. The reference commands
execute actual local bodies; none calls the native compiler, the Rust runner or
a whole-prover callback.

## Input and observation contracts

Inputs are `["zkc.reference-inputs/1", entry, session, supplied, resources,
answers, replies]`, optionally followed by setup selections. The session is
explicit. Keys, fields, tables, points and deterministic test resources use
bounded tagged values; private opening state is issued by actual interpreted
commit and cannot be forged through entry JSON.

Observations are `zkc.reference-observation/1` records: entry, selected role or
joint mode, outcome, ordered events, residual resources, unused reply count and
proof scope.
Every event retains its actual session, instance, call/iteration path, role and
site. The native suite compares the first nine fields exactly, sorting only the
resource map without deduplication. It preserves the proof-scope labels separately.
Executed failure is an observation, not a process error; callers inspect its
outcome even when the command exits zero.

The native test observer translates a small declared diagnostic vocabulary:
`control.require` rejection becomes `require-false`, exhausted test draws become
`challenge-tape-exhausted`, `poly.product_round` positive-rank/arity refusal becomes
`round-shape`, `poly.fold` positive-rank refusal becomes `fold-exhausted`, and
`pcs.open` arity refusal becomes `opening-shape`. These classify the same primitive
precondition, using the actually invoked kernel. Raw adapter codes are retained;
other details are not rewritten. Dedicated mismatched-rank controls compare the
whole preceding event sequence and stopped resource state.

RNG and nonce generations advance before failed consumes. Nonces additionally
follow Issued → Ready → Spent: first commit requires Issued; response requires
Ready; a stage error leaves Spent. The reference retains the same failure prefix
and counters as the installed native reference-group service. Runtime work
meters and native memory policies are separate; tests use their admitted overlap.

## Assurance boundary

The arithmetic identities are kernel-checked theorems. Portable decoding,
admission, projection comparison and interpretation are executable definitions;
there is no theorem proving checker soundness or elaboration to the separate
typed `Zkc.Source.Protocol`/`Compiler.Role` languages. The native comparison is
implementation evidence under a selected observer and shared service contract.

The symbolic PCS checks exact issued subject/point/value records. The real PCS
verifies a mathematical opening relation and can accept an honestly issued proof
at another point with that point's correct value. Thus arbitrary proof/query
mutations need not agree with the symbolic oracle. The maintained differential
suite preserves this concrete counterexample and refuses to claim general
equivalence. Honest authored flows compare actual query issuance and verification
at the same point; real native proof bytes still pass native serialization and
verification. Supplying actual verification replies as reference assumptions
would check surrounding control conditionally; that mode is not implemented.

See [interactive execution](../../docs/compiler/interactive-execution.md)
for the compiler/runtime route. Typed role projection, scoped source-cut/resource
laws, this executable reference, and protocol security retain separate claims.
