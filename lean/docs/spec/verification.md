# Explicit verification specifications

This page specifies how authored intent, retained contracts and Lean property
consumers combine into theorems about imported subjects. Lean checks admission,
proof terms and the stated mathematical assumptions; native name and selector
resolution, source comparison and regeneration are tested boundaries, and
compilation, physical layouts, providers, encoding, Fiat–Shamir and PCS
composition need separate correspondence results when a claim includes them.

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
repacking. A coordinate can record call occurrences and repeat iterations.
An explicit instantiation maps callee logical parameters and witnesses to caller
values, supplied mathematical values or unavailable slots. Neither a coordinate
nor an instantiation proves that the invocation or iteration it names was
reached.

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
property adapter when no available one fits. Structural derivation and
call substitution reuse the common machinery. The structured interfaces are
Lean APIs; the bounded CLI generator below has its own smaller supported profile.

### Recovering structural bindings

`ContractElaboration` recovers binding records from concrete admitted metadata.
`bind_contract` follows the admitted component root, resolves unique relation and
formula references, and reconstructs ordered selectors with their types, roles,
ports and scopes. Named component and clause constructors reject missing or
ambiguous references. The actual source and helper bodies remain projections
from the imported subject.

For example, the Schnorr adapter in `ZkcExamples.Structured.SchnorrBinding`
recovers these records:

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
Simple definitional equalities can use `rfl` without a derivation tree.

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
inputs. Its execution uses the ordinary participant process and handler. Boundary projection
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
the rule needs no losslessness assumption. Its events depend on returned
values; state- or trace-dependent events need a corresponding stronger rule.

The maintained Sumcheck caller uses this rule on its actual linked child and
terminal, without unfolding the child's body. Its terminal law covers arbitrary
returned tuples, including missing values, malformed lengths and capacity stops.
The child implementation proves its own residual bound separately. A replacement
child satisfying that same bound can reuse the caller theorem unchanged.

### Prover strategies from checked sends

An honest-prover property can take its messages from the actual checked prover
process instead of a handwritten strategy. For Interactive Schnorr,
`SchnorrHonestProver.replyHandler` runs the prover's participant process with
`PIR.Proc.run`. It answers the nonce query and the challenge receive with fixed
replies, acknowledges the commitment and response sends, checks the domain,
site, peer and service handle of every action, refuses any other action, and
logs each action in order. The handler is deterministic for its fixed inputs:
any sampling happens outside the run, and the nonce reply does not depend on the
challenge.

`extract` accepts only a successful run whose log is exactly a query, a send, a
receive and a send at the expected sites, and returns the two sent values. It
neither checks nor recomputes the response formula. A stopped, reordered or
extended trace yields no messages, and no message is decoded from a prefix.

`strategyOf` packages these observations as a `Common.Strategy`: the commitment
observed in the run with challenge zero and, for each challenge, the response
observed in the run with that challenge. All these runs receive the same nonce
reply. It requires successful extraction for
every challenge and supplies no fallback value. The constructor alone asserts
neither causal timing nor that every run sends the same commitment. Using it as
an honest strategy requires theorems about the actual source showing that the
commitment is sent before the challenge is received, that the run prefix
through that receive does not depend on the reply, and that every fixed
challenge completes.

`Common.run` executes the actual checked verifier under
`Common.transcriptHandler`, which answers the verifier's query with the fixed
challenge and each receive with the strategy's commitment or response according
to its type. Prover and verifier inputs are separate arguments, and no
mechanism makes the participants' copies equal. The optional
`StructuredSchnorrHonestView.sourceView` is the resulting public view: the
observed commitment and response, the fixed challenge and the verifier's actual
outcome under honest delivery.

For the imported Sumcheck pair, `SumcheckHonestExecution` runs both actual
participants instead of extracting a strategy. `Source.PeerExecution.peerHandler`
keeps the prover's actual residual process in the handler state: a verifier
receive takes the value of the prover's next send, a verifier send is consumed
by the prover's next receive, and the verifier's queries go to a challenge tape.
A mismatched type, site or endpoint refuses. Both participants receive the same
inputs as explicit arguments, and completeness is an equation for the run of the
actual roots for every tape that supplies the rounds; the
[support matrix](../support.md#honest-sumcheck-prover) lists its premises.

## Source claim requests

A source claim explicitly selects a property/version, model and arguments,
retained target or registered imported language, typed acceptance selector,
stage, quantity and capability requirements. The frontend exports constructor
data; the Lean property/model registry fixes its interpretation before a proof
route is chosen. Attachments and proposed methods do not determine the meaning.

`Zkc.Claims.Resolved` records checked registry lookup, subject association and
elaboration. `Evaluated` records that the registered meaning evaluates to its
proposition. A `Receipt` proves exactly that proposition; endpoint, theorem and
derivation routes share the same type. Every kernel-checked proof of that fixed
meaning is evidence. Final assurance-report status depends on exact admission,
remaining statement binders, standard axioms and every request-owned required
link, rather than internal proof use. The core `Receipt.status` only checks
whether its registered links have proofs; `.certified` there is not final report
certification. It cannot check security-layer admission or independently recover
mandatory stage links. Charged soundness additionally requires
the charged reduction at the requested prices. A successful scalar bound does
not imply that capability. Registry-owned obligations determine required links;
provenance cannot remove them.

The [assurance report](assurance-report.md) compares actual emitted typed indices
and wire data against each bound source request and the pipeline's artifact
bytes. Only structured registered-but-undefined interpretations are incomplete;
resolution refusal and normalization/resource failure remain open regardless of
diagnostic text. The selected canonical property and model elaborator are
compared after lookup, allowing unrelated appended exports. Capabilities require
a recognized checked consumer; a matching argument type is insufficient.
Parameter application coverage requires the actual interpreted application to
equal the designated free request binder. Fixed models retain concrete scope.
Missing proofs or required
stage links are open, and only checked requested claims can be
certified. Failed attempts remain separate. All source claims are reported,
including unsupported interactive models. Reports remain IR-relative with an
explicit `source.correspondence` premise; interpreted executable-byte claims
never establish native executable conformance by themselves.

For compiled ideal, the actual subject's construction check, selection and
public schema discharge `construction.checked`. Interpreted bytes also require
`lowering.interpreted_bytes`, pinning that subject's actual program, checked
lowering, helper interpretation and public admission. Reporting reconstructs
these goals from the typed subject and compares them with each registered
obligation and its proof. Direct lower-stage proofs can certify that interpreted
endpoint while native closure stays open; native realization is a separate
claim. A matching label or a different subject's link cannot supply these proofs.

Security receipt reporting also checks the exact subject's target/acceptance
and actual full model elaboration. `ZkcSecurity.Claims.AdmittedReceipt` (module `Claims.ReceiptAdmission`)
provides a typed association between a selected model registry and the exact
request/subject/evaluated receipt, including manually authored extensions. The
extractor recomputes these admission operations. A blocked symbolic model
computation can use the typed certificate's actual witness and a kernel-checked
equation for the exact reconstructed call; concrete refusal and undefined
results remain failures. A property elaborator that
ignores the model cannot establish admission. Internal Evidence notes and method
provenance are best-effort attribution only; missing or failed attribution can
report `unattributed` without leaving a proved receipt open. Provenance strings
cannot add assumptions. Claims endpoint adapters require every legacy Evidence
hypothesis to carry `.proved` by type (`HypothesesProved`); an `.assumed` note
cannot pass that boundary. The legacy manifest audit keeps its strict Evidence
shape and hypothesis checks. Actual remaining binders and registry-owned links
supply obligations. Declaration provenance and axiom closure use
checked stored ConstantInfo bodies, including opaque proofs, rather than
imported axiom caches. These checks do not add native correspondence premises.

The version-zero knowledge meaning quantifies one `ReplayClass` before its
statements, histories, adversaries and query counts. The class includes the
compiled-verifier equation, the retained application relation, special
soundness and the transcript shape used by the fixed VCVio replay extractor.
An endpoint method supplies a witness of that class; it does not define the
requested relation. Different valid witnesses may expose different family or
witness representations. An arbitrary extraction theorem does not by itself
establish this particular Sigma replay property. The registered two-run form
selects the replay guarantee, whose proposition is a probability inequality;
there is no formal running-time bound in this meaning.

Public reports retain the selected whole-Entry scope and separately audit other
compiled Entry trials. Undefined interactive meanings remain visible as
incomplete trials; missing trial records remain unaudited/open. Neither changes
the outcome of the explicitly selected Entry scope.

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
The named target adapter covers scalar Schnorr/discrete-log. Other
contracts use the lower-level `zkc.proof-request/0` schema. Additional named
relation adapters need proved body/selector connections; an opaque relation
cannot pass by claiming that it is discrete-log.

The constructor renderer accepts nonempty printable ASCII identifiers
and strings up to 512 bytes and checks exact constructor arities. Native and
Lean JSON interfaces can admit a wider string repertoire; that does not imply
the bounded proof generator supports it.

The named resolver checks interface/source/symbol identity, the selected target
and Boolean decision, role-local base/key selectors, witness purpose/type, and
scalar native layouts. It exports the relation's actual formula function from
the same retained native source. Lean proves that admitted function denotes
`key = secret • base`. The generated `target_special_soundness` theorem then
connects two accepting executions of the actual imported verifier to a witness
accepted by the actual imported relation.

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
the compiler or the contract it consumes. CLI support for an extension registers its
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
with the recorded manifests. Source hashes identify inputs.
