# Explicit verification specifications

## What the author supplies

A native DSL `spec` clause records intended relations and port/role selectors.
It does not select a security experiment or prove a property. A verification
specification supplies the additional information: contract, properties,
experiment, verifier/prover roles, semantic input bindings, effect sites and
mathematical domains. A relation adapter connects an authored target proposition
to the chosen contract. No security result is selected from a clause's name.

`bridges/common/requests/schnorr-dsl.json` is an executable example of
`zkc.verification-spec/0`. It binds named DSL inputs and the challenge service,
selects the `knowledge` target, and asks for the discrete-log relation adapter.
The current named target adapter supports scalar Schnorr/discrete-log. Other
contracts use the lower-level `zkc.proof-request/0` schema. Additional named
relation adapters need proved body/selector connections; an opaque relation
cannot pass by claiming that it is discrete-log.

The current constructor renderer accepts nonempty printable ASCII identifiers
and strings up to 512 bytes and checks exact constructor arities. Native and
Lean JSON interfaces can admit a wider string repertoire; that does not imply
the bounded proof generator supports it.

The named resolver checks interface/source/symbol identity, the selected target
and Boolean decision, role-local base/key selectors, witness purpose/type, and
scalar native layouts. It exports the relation's actual formula function from
the same retained native source. Lean proves that admitted function denotes
`key = secret • base`. The generated `target_special_soundness` theorem then
connects two accepting executions of the actual imported verifier to a witness
accepted by the actual imported relation. Native name/selector resolution is a
reviewed and tested boundary, not a kernel proof of the DSL compiler.

## Contract proof and property application

The bounded generator symbolically expands the selected role and proposes pure
source and process expressions. A restricted vocabulary admits constructor and
scalar terms, with no commands, comments, imports, macros or tactics. The reviewed
renderer owns the Lean declarations, subject bindings, normalization proofs and
audits. Lean checks admission and the verifier-contract equality.
A separate request interpreter reconstructs the inputs, role, sites and actual
program denotation. It checks the candidate contract against that subject and
re-derives the requested properties. A separate relation-subject check does the
same for the authored predicate. Copying a hash, proving a lookalike experiment,
or returning success text is insufficient. Each generator receives disposable
copies; the checker and receipt retain independent source/request snapshots.

Registered properties include Schnorr perfect completeness and special soundness,
VCVio honest-verifier simulation, finite two-round Sumcheck completeness/soundness,
ArkLib interactive soundness, and public-factor-opening completeness/soundness.
Experiments are exact identifiers: causal transcripts, independent full-field
coins, reached-query uniform sampling and the honest-verifier view are distinct.
They cannot be substituted on the basis of similar names or matching types.

Lean checks proof terms and the transitive axiom closure of every accepted
subject/property theorem. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. `sorryAx`, extra assumptions introduced as axioms, a valid proof
about another program, timeout and unsupported input all leave an unresolved
receipt. The registry, expression validator, renderer and request interpreter are
reviewed code. Python execution and the selected Lean toolchain are trusted;
this interface does not sandbox a malicious Python process. Requests cannot
supply Lean snippets, imports, tactics or arbitrary theorem names.

## Composition and extensions

The typed `Zkc.Verification` API is more general than the bounded generator.
An author can define a new contract, property, consumer or proved adapter in a
Lean module. `ZkcExamples.NativePrograms.CustomProperty` applies a new rejection
consumer to an actual imported source via `Certificate.verify`, without changing
the compiler or existing contract. CLI support for an extension registers its
reviewed input schema and consumer; automatic correspondence may require new
normalization lemmas. Failure to find a proof is not a counterexample to safety.

Open-process refinement composes through continuations and preserves shared state.
Residual contracts connect rounds to downstream checks. Security composition
uses an explicit bad-event implication and bound under one joint experiment;
it does not infer independent randomness from separate service handles.

## Receipts and scope

`zkc.proof-receipt/0` distinguishes `verified-in-model` and `unresolved`. It records
source export, request, certificate and dependency-manifest identities, the exact
properties/consumers/experiments, premises, target correspondence where present,
and remaining external boundaries. Receipts are reproducibility records, not
signed proof objects or runtime authorization. Recheck retained Lean certificates
with the recorded manifests. Source hashes identify inputs; they establish no
compiler, cryptographic-provider, Fiat–Shamir, PCS or whole-prover correctness.

## Constructed Fiat–Shamir subjects

The [constructed-program verification specification](fs-verification.md) owns
`zkc.fs-verification-spec/0`: actual checked native construction, fixed ideal
primitive interpretation, complete denotation, independently selected security
consumer and exact requested-subject checks. Its receipts retain the native Merlin
descriptor separately from the conditional ideal model and identify the remaining
provider, encoding, compiler and runtime boundaries.
