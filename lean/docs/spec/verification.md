# Explicit verification specifications

## Structured contracts

The structured path retains contracts on original protocol declarations and
formula links on relation declarations. One typed `Region` denotes the program
in `PIR.Proc`. Proof construction uses that body, its actual calls and its
actual returned observations. It does not introduce a second executable model.
The bounded scalar request generator described later is a separate client.

### Source association and logical interpretation

`ContractBinding` selects a retained contract owner and its checked protocol
from one `Imported snapshot`. `ApplicationBinding` carries typed selectors
whose erasure equals the retained relation application, in the same order.
Each selector identifies direction, port and participant. A shared source name
or equal type does not identify different participant copies.

A component theorem may select any retained clause explicitly. An
`EntryContractBinding` additionally ties the owner to the actual admitted root
and recovers the exact target name retained in its statement. A `run` Entry
has no selected proof target; its component clauses remain available for an
explicit property request. Identical output indices at different participants
do not identify an Entry selection.

`FormulaBinding` resolves a relation's explicit formula symbol to the original
Math function and its admitted helper body, with the complete ABI. Formula
truth means that invocation of this actual linked helper returns `true`.
A proposed mathematical predicate is usable through a local adequacy law and
its domain premise at the actual arguments. Refusal remains a stopped process;
it is not silently interpreted as a completed false result.

For opaque relations, one `RelationEnvironment` fixes a predicate per retained
relation declaration for the chosen experiment. All occurrences retrieve that
meaning. Different experiments may use different environments, but composing
proofs across them requires an explicit correspondence. Formula truth remains
actual invocation, independent of the opaque environment.

`LogicalAssignments` is indexed by the contract owner and a logical invocation
coordinate.
It supplies typed parameter and witness values. Statement selectors read the
role-local execution boundary. Repeated uses in one invocation share the same
assignments. Different owners and coordinates require explicit transport or
repacking; this type discipline does not prove that an invocation was reached.
A coordinate can record call occurrences and repeat iterations.
An explicit instantiation maps callee logical parameters and witnesses to caller
values, supplied mathematical values or unavailable slots. This mapping does
not prove that a claimed loop iteration was reached.

Purpose labels do not choose quantifiers, secrecy, randomness or an adversary
model. Honest completeness can require a witness to agree with the prover's
input. Extraction supplies a newly computed witness. Sumcheck soundness fixes
one mathematical table independently of the adversary's runtime table operand.
These choices belong to the selected property and its experiment.

### Authoring boundary

The maintained Schnorr library expresses its intent with an ordinary relation
and a target clause:

```zkc
pub relation DLog<G: Group>(parameter base: G, statement point: G,
                           witness scalar: G::Scalar) {
  return point == base * scalar;
}

// Inside the protocol declaration:
spec {
  target knowledge = DLog<G>(in.base@V, in.point@V, in.scalar)
    accept out.accepted;
}
```

The exact formula, selectors and target clause survive into the admitted
subject. A proof Entry additionally records which target it selects. A Lean
adapter then chooses a property: for special soundness, it uses
two actual accepting verifier executions, constructs a witness, and proves that
the linked formula accepts that witness. Honest completeness instead relates
the original witness and prover execution to the verifier. The same source
clause supports both; it does not choose either theorem automatically.

For a new component, the author supplies relations and relevant boundaries in
`.zkc`, reusable local mathematical/process laws in Lean, and an explicit
property adapter when an existing one does not fit. Structural derivation and
call substitution reuse the common machinery. The structured interfaces are
Lean APIs; the bounded CLI generator below has its own smaller supported profile.

### Recovering structural bindings

`ContractElaboration` recovers binding records from concrete admitted metadata.
`bind_contract` follows the admitted component root, resolves unique relation and
formula references, and reconstructs ordered selectors with their types, roles,
ports and scopes. Named component and clause constructors reject missing or
ambiguous references. The actual source and helper bodies remain projections
from the imported subject.

For example, the Schnorr adapter recovers these records:

```lean
def owner : ContractBinding imported := by bind_contract
def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "knowledge"
def application : ApplicationBinding owner (owner.clause clauseIndex).subject := by
  bind_contract
def formulaBinding : FormulaBinding imported application.relation := by
  bind_contract
```

The tactic produces ordinary kernel-checked evidence. It does not prove formula
adequacy, choose logical values or an experiment, or manufacture a selected proof
target for a run Entry. A same-symbol, same-ABI formula mutation may still bind;
its old mathematical adequacy theorem must be checked again. Ordinary constructors
remain available for abstract metadata and explicit binding evidence.

### Structural proof construction

`CheckedApplication` identifies an occurrence in the actual checked caller
body, with exact SSA operands, result signature, site and role map. Its local
substitution laws preserve masks and distinct participant copies. Generic
call-composition laws replace the actual callee process with a proved local
law and derive the caller's continuation. A stopped callee does not run that
continuation; returned values and residual handler state are preserved.

`callInventory` enumerates every lexical protocol application, including calls
inside callbacks and repeats. Its completeness theorem covers every canonical
occurrence in the body. A call with no declared clauses still needs a local
resolution or inspection of its actual body. Repeats contribute one lexical
body; its semantic proof must cover all relevant iterations, not a finite
sample of unrolled executions.

`Region.Derivation` constructs process correspondence from the source tree,
local operation laws and callback derivations. The `derive_region` tactic walks
that typed tree and leaves mathematical laws as ordinary Lean goals. Callback
rules quantify over their inputs. `region_view%` projects a constructor view
from an admitted body; the kernel checks its definitional equality to that body.
Neither mechanism proves the frontend or exporter correct. Simple definitional
equalities can continue to use `rfl` without a derivation tree.

After process correspondence, deterministic handler simulation or optional
VCVio coupling transports execution properties. The maintained local coupling
relates the same process under two handlers/views with paired exact replies
and outcomes. Its premises concern all required states, replies and events. Receiving, sampling, sending and
stopping remain distinct. Shared service handles do not imply independent coins.

### Selected requests and actual observations

A `ContractInterpretation` interprets every retained subject and residual and
recovers each exact Boolean decision selector. It declares no theorem.
`ApplicationUse` records a successful ordered argument read; its `Translation`
requires both formula adequacy and the actual domain premise. The equivalence
law consumes both. An assertion or refutation request then uses the resulting
mathematical fact. In particular, an `input` clause does not automatically
become a hypothesis: false-claim soundness can require its refutation.

`ContractRequests` is a nonempty tree of selected relation uses and explicit
external terminal requests. A selected residual must be present in the retained
clause. An external terminal names its typed inputs, nonempty output selection
and meaning; it is explicitly an additional property request, not an invented
source clause. Each leaf needs a proof. `SelectedObligations` also records
requests for every lexical call. These records organize proof construction;
completeness of an inventory alone proves no security property. An identity call
specification can satisfy the inventory without abstracting behavior, and an
external terminal whose predicate is `True` establishes only output availability.

`ComponentInput` fixes the actual checked invocation, context, participant and
inputs. Its execution uses the existing process and handler. Boundary projection
reads the real outcome, masks inputs and leaves other participants' copies
absent. Stopped outcomes have no returned outputs. Selected-decision laws
connect a role-local Boolean read to a returned execution event. A security
consumer must use this reached observation, rather than an arbitrary supplied
result tuple.

The property consumer owns quantifiers, probability, extraction, simulation and
terminal discharge. A local law about an arbitrary boundary becomes a protocol
result only through that consumer's actual execution proof. Obligations are
complete relative to the selected construction and supported fragment; syntax
cannot discover undeclared security intentions or arbitrary invariants.

The optional `VCVio.Composition.acceptance_bind_le` rule composes a child
residual bound with a continuation. It requires every accepting continuation
execution to imply the child's residual predicate, for every returned child
value and every intermediate state. Initial-state checks alone are insufficient
because the child may change state. Stops on either side contribute no acceptance;
the rule needs no losslessness assumption. Its events currently depend on returned
values; state- or trace-dependent events need a corresponding stronger rule.

The maintained Sumcheck caller uses this rule on its actual linked child and
terminal, without unfolding the child's body. Its terminal law covers arbitrary
returned tuples, including missing values, malformed lengths and capacity stops.
The child implementation proves its own residual bound separately. A replacement
child satisfying that same bound can reuse the caller theorem unchanged.

### Trust boundary

Lean checks source admission, proof terms and the stated mathematical assumptions.
Retained original-PIR data identifies the model being proved about. Native
source comparison and regeneration are tested boundaries, not a universal Lean
proof of the frontend or exporter. Compilation, physical layouts, providers,
encoding, Fiat–Shamir and PCS composition need separate correspondence results
when a claim includes them. This architecture supports those connections
without asserting that every compiler transformation is already verified.

## Bounded scalar requests

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
