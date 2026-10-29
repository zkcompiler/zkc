# Assurance reports

`zkc.assurance-report/0` records every bound source request and the evidence
actually checked for it. `lean/checks/check_records.py` generates one report per
subject. A successful source compilation does not establish a requested claim.
The manifest supplies input/output configuration and generated file ownership;
it does not choose properties, models, target relations or proof routes.

The source request fixes the meaning before evidence is selected. A report
compares that request with emitted `Zkc.Claims.Wire.Request` data and the actual
indices of `Resolved`, `Evaluated` and `Receipt`. The kernel checks registration,
elaboration, evaluated meaning and proof typing. The frontend associates those
values with captured source nodes and pipeline artifact bytes. These are
separate boundaries, and the report names both.

## Inputs

| Input | Format and role |
|---|---|
| Subject manifest | `zkc.subject/0`: subject name, Entry selection and generated file paths |
| Pipeline evidence | `zkc.subject-evidence/0`: artifacts, regenerated module digests, check outcomes, bound source requests and receipt associations |
| Bound source requests | `zkc.bound-source-claims/0` in `source_claims`: every request, digest, attachment, proposed method and source site bindings |
| Declaration records | `zkc.declarations/0`: actual elaborated declarations, premise telescopes, axiom closures and typed receipt extraction |
| Mathematical ledger | `lean/checks/claims.toml` and `claims.lock.json`: maintained mathematical results, audited independently of source requests |

The security and optional integration packages contribute compatible registry
and endpoint tables. Conflicting identifiers, schemas and endpoint registrations
are errors. A name or provenance string never constructs a proposition.

## Pipeline association

Each `claim_receipts` entry names one exact `attachment.node` in the bound
source export:

```json
{
  "node": {"kind":"source-claim","owner":"demo::Claims","block":0,"claim":0},
  "request_digest": "sha256:<canonical request digest>",
  "request_declaration": "Demo.request0Data",
  "receipt_declaration": "Demo.request0Receipt",
  "resolution": {"status":"open"},
  "attempts": []
}
```

A missing receipt is represented by a null or absent `receipt_declaration`.
Missing interpretations may be diagnosed with
`resolution: {status: "incomplete", kind: "registered-undefined", definitions: [...]}`,
where the nonempty string list comes from the typed resolver's incomplete
constructor. The kind annotation is optional for the existing typed producer;
if present it must be `registered-undefined`. Only structured status `incomplete`
with a nonempty string list is incomplete. Unknown versions use
`status: "refused", kind: "resolution-refusal"`; normalization/resource failures
use `status: "open", kind: "normalization-failure"`. They remain open even if a
legacy producer places diagnostic text in `definitions`. Such diagnostics are
never positive proof evidence. A missing definition and a failed proof attempt
are different facts. Every bound request receives a report row, including
interactive claims and requests without an association. Duplicate nodes,
ambiguous associations, stale digests and associations to absent nodes are
errors.

`source_claims.entries` lists the selected author-facing proof or interactive
Entries; older exports fall back to `[source_claims.entry]`. Each item's
`source_entry` must be selected. Its `entry_association` records the exact
checked native interface digest, source Entry and admitted protocol symbol;
the symbol must equal `request.subject.entry`. This remains trusted frontend
attribution, separate from kernel correspondence. Crossed, malformed or missing
alias associations refuse. Without an association only exactly equal
source/request Entries are supported. The unit digest still matches the stage's
original or interactive export independently.

`source_claim_scope` retains the exact whole-Entry selection: `entries` and
`selection` (`proof-entry` or `explicit`). It must agree with the bound Entries
and all selected requests; the default selects the manifest's proof Entry.
`source_claim_trials` exposes other compiled Entries separately, including their
bound claims, declaration associations, structured resolutions and attempts.
Each trial uses the same receipt audit and has its own claims, status, outcome,
reasons and `audit_status`. Missing declaration records leave a trial
`unaudited` and `open`. A trial does not change the selected Entry aggregate.

The canonical request digest hashes sorted, compact ASCII JSON with finite
numbers. Attachments and method plans are outside that digest. Renaming a label
or selecting another method changes neither request meaning nor its identity.
Changing a target, quantity, registry version, stage or artifact does.

A checked receipt additionally requires this pipeline check:

```json
{
  "name":"claim-receipt", "outcome":"accepted",
  "module":"ZkcArkLib.Examples.Subjects.Demo.Claims",
  "request":"Demo.request0Data", "receipt":"Demo.request0Receipt"
}
```

Both declarations must belong to this subject's freshly regenerated modules.
Module paths use actual package providers, independently of declaration
namespaces: a `ZkcSecurity.*` declaration may live in a `ZkcArkLib.*` module.
A generated module must match the pipeline's recorded bytes, and every artifact
digest attached to that module must be among the pipeline's outputs.

## Declaration extraction

Each ordinary record retains `name`, `module`, `kind`, structural and explicit
statement hashes, transitive `axioms`, documentation and tags. The premise
telescope includes explicit, implicit and instance binders. Detailed records
also retain pretty-printed statements, actual dependency identities and the
existing endpoint evidence's named hypotheses. Requests, receipts and endpoint
evidence are detailed automatically; `--detail` selects other declarations.

`detail.claim_data.wire_request` serializes the actual typed request by reducing
data constructors. It does not parse pretty-printed Lean. Imported-language
requests preserve the protocol and complete versioned language application,
including arguments. The maintained security resolver currently refuses language
arguments; reporting never erases them to turn a different request into a match.

`detail.claim_data.receipt` contains:

| Field | Meaning |
|---|---|
| `wire_request`, `request_head`, `resolved_head`, `evaluated_head` | Actual typed indices, including the complete request data |
| `indices_checked`, `proof_type_matches`, `proposition` | Extracted typed resolution/evaluation and the proof's checked type |
| `registered_property`, `registered_schema`, `canonical_registry`, `registry_checks` | Actual selected export, checked lookup and kernel comparisons of selected property, export and model elaborator with canonical definitions |
| `authority` | Closed subject shape, product, canonical/author/reserved classification and kernel-checked selected-export association |
| `telescope` | Lean-owned classification of every remaining binder, authorization result and conditional premises with their typed arguments |
| `capability_consumer` | Diagnostic attribution of the canonical capability consumer; Python does not recognize consumer names |
| `application_coverage` | Actual model context, interpreted application value and checked designated free binder, or concrete fixed scope |
| `honest_input` | Retained source input clauses and source-sort ABI admission; both selected participants are prepared from the same source inputs, with the retained target relation as a separate premise |
| `admission` | Actual Subject.check result and full resolveModel result, with the typed model association and explicit admitted/registered-undefined/refused outcome |
| `evidence_attribution` | Best-effort referenced Evidence declarations; attribution only, never receipt obligations |
| `subject` | Actual typed security subject's artifacts declaration, snapshot source/Entry and participant source/candidate identities |
| `quantity_kind`, `exported_capabilities` | Argument quantity classification; capability exports require the checked canonical consumer and its actual charged meaning |
| `root_route`, `discharger` | Checked route attribution and actual proof root; missing or inconsistent attribution reports `unattributed` |
| `proof_dependencies`, `dependencies` | Actual proof/index closure and complete receipt closure, each with declaration, module, ownership and statement identity |
| `required_links` | Registry-owned dependent goals and actual proof presence; remaining telescope conditions are audited separately |
| `stage_links` | Actual-subject stage obligations and physical artifact roles, with kernel goal comparisons and explicit subject-index comparisons against registered links |
| `provenance`, `provenance_error` | Optional route/method notes and extraction diagnostics; strings cannot introduce assumptions |

A failure to extract authoritative semantic fields is explicit and leaves the
request open. Optional attribution failures are diagnostic only. A matching
string alone cannot establish semantic facts. A request declaration alias
is allowed when its full emitted data equals the actual request index data.

## Audit

Lean classifies every leading binder of the request and receipt, including
implicit and instance binders. Receipt parameters must use the actual subject's
carriers, their supported instances, or the designated application context.
Dependencies of carrier instances must themselves be admitted parameters.
`Inhabited False`, `Inhabited (PLift P)`, extra carrier variables and unsupported
Type-valued proof wrappers are refused. Python consumes this classification;
its legacy endpoint audit retains its separate policy until those clients move.

A recognized premise additionally needs explicit authorization in the model
application's `assumptions` argument: a list of closed versioned applications.
`assumptions.faithful_scalar_action@0` fixes the scalar-action law on the selected
field and group. `assumptions.dlog_search@0` fixes worst-case recovery resistance
for finite scalar equality-query decision trees at the selected model's fixed
query limit. This narrow search game is not general computational discrete-log
hardness. Each admitted condition reports its actual typed arguments. Symbolic
limits without a fixed typed instantiation remain unsupported. Arbitrary
propositions, substituted carriers or limits, budget inequalities, target truth,
helper correspondence, local-event bounds and required stage links cannot enter
through these schemas. Registration in the legacy assumption ledger alone does
not authorize a receipt premise.

Receipt authority is the exact request-fixed evaluated proposition and typed
admission, its remaining request/receipt telescope, standard axioms, and a proof
of every request-side required stage/property link. Any kernel-checked proof of
the same meaning is evidence. Internal proof structure and method choice cannot
change status. Generic functions applied to concrete arguments do not introduce
free assumptions into their callers.

The old endpoint theorem, evidence telescope, named-hypothesis/schema and axiom
audits remain strict for the mathematical ledger and legacy manifest endpoints.
For receipts, internal Evidence searches are best-effort attribution only. The
emitter records referenced Evidence declarations without interpreting arbitrary
callback consumers. An absent attribution, optional provenance extraction error,
or unrecognized proof route is legal; the report uses `root_route: unattributed`
and optional attribution diagnostics. Provenance premise strings and Evidence
notes never become actual assumptions. Actual dependency and axiom closures are
still recorded and audited independently of route attribution.

Claims endpoint adapters require `HypothesesProved evidence.hypotheses` by type.
Each list element must contain `.proved` with a proof of its actual proposition;
`.assumed` cannot satisfy this boundary. All six maintained subjects use an empty
list. The legacy Evidence shape, including its hypotheses field, is retained so
the existing manifest endpoint audit keeps its meaning. Proved note identifiers
need no registry meaning in the receipt path. Genuine external conditions belong
in the remaining statement telescope or registry-owned required links.

Every security receipt must independently pass `Subject.check` and full actual
`resolveModel` elaboration for its exact typed subject, request, field, original
snapshot and endpoint. The extractor checks the resulting success expressions
by kernel definitional equality. When symbolic model computation is blocked,
an exact typed certificate may prove existence of a successful elaboration
whose type is compared with that same reconstructed full call. A witness may
be extracted for diagnostics, but proof-body visibility is not admission.
This cannot override an actual refusal or registered-undefined result. The
emitted admission `success_authority` distinguishes `definitional-evaluation`
and `kernel-equation` (or `kernel-existence` when the witness is opaque).
Looking up a model identifier is insufficient.
`ZkcSecurity.Claims.AdmittedReceipt` in `Claims.ReceiptAdmission` associates a
model registry with the exact `Evaluated` indices and enclosed core receipt,
requiring checked subject and model admission equations. Manual extensions can
construct this certificate directly. Bare canonical built-ins remain supported
when their selected checked property supplies the actual model registry;
extension core receipts without a typed association remain open. An extension
whose elaborator returns `True` cannot bypass target, acceptance or model
admission. Registered undefined is distinct from outer resolution refusal.
No generated admission theorem name is privileged.

`CanonicalReceipt` associates the complete selected property export with the
fixed `CanonicalAuthority.propertyEntry`, and shares a `CanonicalModelAdmission` certificate
for the complete selected model export and its successful elaboration.
`CanonicalAdmission.meaning` derives the semantic argument and link association
from the existing `Resolved` and `Evaluated` equations. The generator reuses a
model certificate for requests with the same model application. For migrating
bare receipts the exporter constructs and kernel-checks the same association.
Neither proof-body attribution nor a property name can supply this certificate. Unrelated exports appended to either registry are allowed;
duplicate keys and replacement definitions fail. The whole registry's name or
container expression is not semantic authority.

`CanonicalAuthority` is a closed family indexed by the supported subject type.
Its uniform constructor uses the existing uniform verifier implementation;
the other constructors use the actual nominal-domain compiled verifier and
the actual compiled honest pair. Dispatch contains no protocol names,
author-selected propositions or extensible policy instances. The core
`Zkc.Claims.Receipt` stays generic. Pair subjects use a universe lift only;
their fixed meaning calls the honest model's `CanonicalCompleteness` directly.
Uniform completeness remains undefined. Domain verifiers support fixed and
adaptive scalar or charged soundness; honest pairs support scalar completeness under the exact
argument-free honest model, without an adversary query parameter.

The domain subject interprets its retained target on the actual model's
typed source values, statements and witness selectors. Its preselected
capabilities supply laws for the actual catalogue, finite instances only at
admitted field identities, and sampling at the actual event-dependent reply
types. Cardinality reads these carriers; unknown identities refuse. Evidence
cannot replace this interpretation. Domain construction links include the
source-occurrence check. Pair links require exact pair admission, retained
target and source input association, selected validator admission, and both
source-occurrence equations.

`RetainedTarget` selects one actual Boolean target clause, its ordered selectors,
publication layout and exact acceptance output. Interpretation is selected
separately by the request-owned subject: `RelationMeaning.formula` contains a
`FormulaBinding`, and `RelationMeaning.opaque` contains an exact binding in the
subject's admitted `RegisteredRelations` registry. Every opaque declaration in
the original relation table must resolve before evidence. Family kind, key,
revision, typed ordered static arguments, input/output sorts and logical purposes
are all fixed by that lookup. Source supplies family identities and arguments,
not Lean declaration names. Evidence cannot supply an unregistered predicate.

Both domain and actual authored-pair subjects use this same meaning. All actual
input clauses remain mandatory, with each formula or opaque interpretation bound
to that same registry. The pair's validator projection transports the selected
target and meaning along the checked policy equality. Domain and uniform readers
share publication decoding and witness selection; all clause consumers share the
ordered application reader. The formula equivalences
`Domain.Subject.holds_formula_iff`, `HonestPair.Subject.relation_formula_iff` and
`HonestPair.Subject.inputClause_formula_iff` retain the previous invocation
propositions exactly. `HonestPair.Subject.honestInput_formula_iff` additionally
preserves all input clauses, representability, preparation and both ABI checks.
Truth requires a completed `true` result; a stop does not satisfy the relation. The existing uniform formula adapter additionally has
`RetainedTarget.holds_formula_iff` against the canonical model reading. Its
retained constructor now receives the exact source formula binding explicitly.

Formula dependency admission retains `checkDefaultRelation` over the actual
helper closure. Registered opaque meanings are mathematical registry entries;
they introduce no executable helper or separate checker root. Registration does
not prove a security or completeness property, nor a native correspondence.

Adaptive domain adversaries return the actual statement and proof after their
oracle queries. The typed public codec injectively binds every raw public value,
including malformed vector widths and counts, in the selected application
namespace. Charged quantities select retained native challenge templates before
evidence; matching retains every dynamic coordinate. Unknown/malformed keys pay
the maximum declared price. The meaning requires both the actual weighted
endpoint bound and a checked existing typed reduction at exactly those prices,
with complete execution reading, coherence, false-state membership and validator
cost. This does not change the oracle's keys, cache or query order.

Honest completeness includes a nonvacuity witness. Its input admission combines
all retained source input clauses, executable ABI representability, and successful
preparation of both selected participants from those same inputs. The retained
target relation remains a separate premise. Completeness admits no property
parameters; the former `honest.input_policy` descriptor is refused. The report's
`honest_input` field identifies the clauses, ABI admission and preparation
boundary, alongside the product `compiled_ideal_completeness`. This product does
not assert native correspondence or a general security result for the pair.

Declaration extraction reconstructs this closed authority from checked type
indices. One Lean telescope policy classifies remaining binders and exports
authorization facts, required links, artifact roles, coverage and product.
Python consumes these facts without a parallel property or binder registry.
Unknown shapes refuse. Standard model laws must be closed in concrete clients;
arbitrary capability or law binders cannot authorize a receipt. Direct opaque
proofs retain checked status even when attribution is unavailable.
Uniform manual author receipts without unused sampling binders derive their
sampler from the actual finite field; selected canonical meanings retain their
actual sampling arguments. This introduces no additional premise schema.

`AuthorExtensionReceipt` has a distinct checked admission and proves its
identifier is outside the reserved set. All root names and infrastructure
namespaces are reserved at every version, including undefined completeness.
Reports retain all requests in `claims`, expose `security_claims`,
`author_claims` and `generic_claims` separately, and aggregate only security
claims. Generic core receipts do not establish a canonical security headline;
changing the subject type cannot authorize a reserved key. A failed or unresolved
explicit author request stays visible with its own reasons and attempts.
An author equation cannot establish a canonical security headline.

The actual exported property/version, quantity, requested capabilities, typed
subject, retained/imported target, acceptance, stage and artifacts must match.
A charged receipt proves both its ordinary property and its charged export;
a scalar receipt does not acquire that export by a provenance label. An arbitrary
extension using `SoundnessRequest` arguments and interpreting them as `True`
cannot export the capability. Until general typed capability consumers exist,
nonempty capabilities require the recognized checked built-in consumer.

For adaptive application models, parameter coverage requires the interpreted
application value to equal the receipt's free String binder designated by the
actual request's application reference. The emitter checks the unique binder's
name, position and definitional identity, as well as agreement between the
selected model context and interpreted model. Constants, prefix transforms and
unrelated String binders do not establish parameter coverage. Fixed application
models report their concrete value and cannot silently narrow a designated free
application binder. Fixed statement models report `fixed-statement` coverage.
This check introduces no general coverage transport framework.

The only allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
Every selected declaration's axiom closure is computed from actual ConstantInfo
types, bodies, opaque proofs and inductive/recursor dependencies. Imported
`collectAxioms` caches are not used. Before registry evaluation or expression
inspection, capture checks every reachable stored provider against the resolved
declaration. Identical duplicate reexports are accepted only after complete
stored-field and exact expression equality, including proof bodies and binder
annotations. Conflicting stored providers, missing providers and ambiguous name
renderings refuse capture. Completed closures alone are cached. Headers declare
`axiom_provenance=resolved-constant-info/0` and
`reference_provenance=checked-stored-module/0`. Requested-receipt auditing refuses
older captures without both provenance attestations. An additional axiom, `sorryAx`,
omitted premise or hidden parameter leaves the request open.

### Required interpreted-stage links

The selected claim covers its interpreted endpoint. Extraction applies
`Subject.stageLinks` to the actual typed subject index, independently of the
registry's chosen list. The report validates these emitted obligations:

| Requested stage | Required checked links | Covered interpreted endpoint |
|---|---|---|
| `compiled-ideal` | `construction.checked` | `ideal-meaning` |
| `executable-bytes` | `construction.checked`, `lowering.interpreted_bytes` | `interpreted-executable-bytes` |

`Subject.ConstructionChecked` pins the generic `checkCompiled`, selection,
selection check, public schema and source-occurrence check, and requires the
actual subject's `Compiled.SourceConnection`. The connection's target is fixed
by the admitted artifacts: actual Domain execution with the fixed scalar ABI
and the admitted source's transform, for all typed public values, proofs,
initial histories and lawful challenge handlers. It is separate from static
admission and cannot choose the meaning or extractor.

`Subject.LoweringChecked` additionally pins the actual program and
`checkLowering` result, helper preparation and sorting, and public admission of
the interpreted validator. It requires `BytePruning` from that validator's
actual byte execution to complete acceptance of the same fixed Domain verifier,
at every decoder, budget and framing header. This link does not replace byte
completeness or full execution observations. Admission supplies their
dependent proofs through `Subject.stageLinkProofs`, independently of the family
method that proves the requested property.

Each expected obligation must match exactly one registered obligation. Its goal
must be kernel definitionally equal to the reconstructed goal, and its checked
schema's subject argument must match the actual subject before goal reduction.
The subject comparison matters even when closed checker equations normalize
alike. A `True` goal with the same label, another subject's valid link, a
polymorphic native-link schema or an absent proof
cannot discharge it. An unrecognized compiled subject remains open. Property
and model names alone cannot authorize stage evidence.

When the subject comparison fails, `goal_defeq: null` records that normalization
of the unrelated goal was skipped. Only explicit successful subject and goal
comparisons can discharge a link.

The registry-owned `Resolved.requiredLinks` and indexed `Receipt.linkProofs`
keep every extra registered obligation auditable. Extraction's independent list
also detects omitted construction or lowering obligations. Missing required
links remain open; they are never renamed model or hardness assumptions.

The legacy endpoint audit retains its native implementation-link metadata.
Those native links are not prerequisites of a direct theorem about the selected
interpreted endpoint. Such a theorem cannot certify another stage or native
execution. The report records its `covered_endpoint` explicitly, and lists
successfully checked stage links in `checked_correspondences`.

Model and hardness premises can remain explicitly conditional. Until source
correspondence has its own checked bridge, reports retain
`source.correspondence` as a trusted link and `scope: "ir-relative"`.
Interpreted-byte semantics is distinct from native executable conformance.
`native_closure` remains `open`. The closed verifier shapes report
`certified_verifier`; the honest pair reports `compiled_ideal_completeness`
with `honest-inputs` coverage. Mixed or empty aggregate products report
`assurance_report`. These products do not assert `certified_authored_pair`.

### Semantic dependency identity

Each request records `semantic_dependencies`: byte hashes of every owned module
in the actual closure, emitted declaration identities, toolchains, manifests,
verified dependency revisions and compatibility records. Dependency verification
is read-only: it checks actual Git HEAD, undeclared changes, patch digests and
the recorded patched file contents. Reporting never applies a patch or fetches
a dependency. Missing or unverified dependencies leave the request open.

Changing a referenced definition body changes the dependency digest even if the
theorem's structural statement hash stays identical. An optional
`claim_receipts[].semantic_dependency_digest` supplies a prior cache identity;
a mismatch leaves the request open. Digests are audit/cache
identities, not preservation proofs; the kernel check of the actual proof type
is authority. Saved records supplied with `--records` remain unconnected to the
current source build and cannot certify a request.

## Status and report fields

`Zkc.Claims.ReceiptAudit` owns the total finite receipt classifier and the
whole-scope aggregate. Its input distinguishes kernel observations, external
admissions, and resolver diagnostics. The production `declaration-records
--receipt-status` command imports the stored providers, re-extracts the named
request and receipt facts and actual axiom closures, and checks the mandatory
export against those fresh observations. Optional method attribution is absent
from this comparison. A supplied proof flag cannot replace the extraction.

Each request/receipt root is imported using its physical provider's own Lake
search path. Independent package groups are checked in separate environments;
their paths are never concatenated to choose whichever module happens to win.
Aggregating their status records does not construct a theorem across those
environments. The exchange carries a fresh invocation identifier and the digest
of its complete input, including the provider partition. A mismatched response
is a transport failure. These identifiers bind the reporting exchange; they
are not kernel proofs of filesystem identity.

The positive characterization theorem states exactly which audit conditions
certification requires. It proves the finite policy, not the correctness of
external hashing, source-to-IR correspondence, or filesystem-to-built-object
association. Those admissions remain visible. Python supplies byte identities
and joins and renders the Lean export; it has no fallback receipt classifier.
Each requested source occurrence must have exactly one associated status row.
The report renders the same dependency observation that the Lean audit received,
without taking a second potentially different filesystem snapshot. An unaudited
scope cannot contain a certified item, even when its aggregate status is open.
Missing, corrupt, stale or inconsistent exports produce `transport-failure` and
`outcome: unresolved`, with the transport diagnostic. This is a reporting failure,
not a Lean decision that a mathematical interpretation is incomplete.

| Per-request `status` | Meaning |
|---|---|
| `incomplete` | A required interpretation is reported missing; no checked receipt proves it |
| `open` | A proof, required link, artifact association or audit check is missing or invalid |
| `certified` | The exact requested meaning and capabilities have checked receipts, with all required stage links and audits |
| `transport-failure` | No valid, freshly checked Lean status export was received for the request |

Proof attempts retain their method, result and diagnostics separately;
`unsupported`, `timeout` and `refused` are attempt results, not semantic states.
The top-level `outcome: established` projects only a nonempty set of certified
requested claims. Otherwise it is `unresolved`. An explicit empty source export
has `status: no-claim`, never fabricated success.

The report retains its subject/manifest identity, attached and connected
artifacts, checker environment, claims, allowed axioms and independently audited
ledger context. Each claim retains the full request/digest, attachment,
resolution, attempts, method plan/version, actual root/discharger/dependencies,
semantic dependency identity, assumptions, discharged links, bound, status and
reasons. `matching.kernel` and `matching.frontend` identify the distinct matching
boundaries. The rendered subject table has one row per requested claim.

## Maintained controls and mathematical ledger

`Tests.ClaimReporting` supplies actual Lean-emitted request/receipt controls for
clean proofs, explicit/implicit false hypotheses, proof-carrying instances,
Type-valued proof wrappers and unverifiable optional provenance attribution. The downstream report audit
must accept the clean control before its negative controls count as evidence.
Existing endpoint and hidden-assumption controls remain maintained separately.
`TestsSecurity.ClaimReporting` supplies fresh admitted compiled-ideal and
interpreted-byte positives, omitted/conditional stage proofs, wrong-goal and
foreign-subject or foreign-artifact links, abstract native schemas, and hidden
False/Fact/Inhabited/proof-wrapper refusals.
Both interpreted endpoints must pass before their negative controls count.
A generic-wrapper proof of the fixed meaning also passes with unattributed route;
an additional unregistered premise binder refuses and a missing stage-link proof
remains open. Internal proved or assumed Evidence notes, projected/opaque
callbacks and choice functions do not change receipt status. Link proof presence
is checked by its dependent type; conditionality comes from the remaining
statement telescope, never from internal occurrence of a proof parameter.
Focused Python controls cover request substitutions, stale definition bodies,
required-link omission, registry ambiguity, incomplete requests, failed attempts
and explicit no-claim reports.

The mathematical ledger retains all maintained theorem rows and their statement
locks. Missing theorem names, changed statements and forbidden axioms fail its
check. Rendering and document-name auditing continue independently of source
request certification. `--write` updates generated regions and locks; it is not
a proof or approval of a new semantic claim.

### Independently selected consumer requirements

The frontend-owned [consumer requirements contract](../../../docs/spec/language/companions.md#consumer-requirements-transport)
adds `consumer_requirements` and `consumer_context` to the existing
`zkc.receipt-audit-input/0` scope operation. `ReceiptAudit.consumerReasons`
checks exact expected occurrence/request coverage and the selected context before
classifying rows. The final scope also requires certified receipts for every
required occurrence, including any required author or generic item. These items
do not become canonical security claims by being required.

The scope export and `zkc.assurance-report/0` retain `consumer_requirements`
(`null` when absent). Missing requirements keep even an empty provider scope
open. No separate security-status classifier or proof admission path is added.
`check_records.py --subject NAME --requirements PATH` accepts one independently
chosen file for one selected subject; it fails if the audited outcome remains
unresolved. Existing reports without a consumer file retain their declared-scope
meaning, which does not assert that every external consumer need was requested.
