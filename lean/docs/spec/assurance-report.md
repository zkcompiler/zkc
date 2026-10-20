# Assurance reports

An assurance report states, for one subject, what a security claim about its
compiled verifier rests on. It records a checked application of a registered
endpoint to artifact-indexed evidence. Completeness of the reported premises is
audited against the elaborated endpoint and its evidence context; correspondence
to native execution is either explicit evidence or an explicitly reported
assumption. The format is `zkc.assurance-report/0`. `lean/checks/check_records.py`
generates one report per subject manifest; the generator is fail-closed, so
anything it cannot classify or connect makes a claim `unresolved`, with the
reason.

A report is assembled from four inputs, each with its own format:

| Input | Format | Producer |
|---|---|---|
| Subject manifest `lean/subjects/<name>.toml` | `zkc.subject/0` | the author |
| Declaration records, one JSON line per owned declaration | `zkc.declarations/0` | `lean/checks/DeclarationRecords.lean` |
| Registry and registered endpoints | Lean tables in `ZkcSecurity.Registry` | the security package, checked by its audit |
| Pipeline evidence `<name>.json` | `zkc.subject-evidence/0` | the subject pipeline's run for the subject |

## Declaration records

The header line names the format, the Lean version, the selected module
families, the module and declaration counts, and, for the security package, the
registry and the registered endpoints. Every following line is one declaration
written in the source of the selected families, sorted by name and module:

| Field | Content |
|---|---|
| `name`, `module`, `kind` | The declaration (a private name without its module prefix), its module, and theorem, definition, opaque, axiom, inductive, constructor or quotient |
| `statement` | `structural` and `explicit` hashes of the elaborated type. The structural hash ignores binder names and metadata and unfolds nothing; the explicit hash also omits implicit and instance arguments of applied constants. Equal hashes are regression evidence, not semantic preservation |
| `axioms` | The transitive axiom closure, opaque proof bodies included |
| `doc`, `tags` | The docstring, and `private`, `class`, `structure`, `instance` or `proposition-valued` |
| `premises` | For a theorem, its leading binders in order, implicit and instance binders included: binder information, whether the binder is a premise (a proof of a proposition), and the premise's head constant after its own leading binders |
| `detail` | For requested declarations and registered endpoints: the pretty-printed statement and premises, the premise telescope whatever the declaration's kind, and the registered constants reached through the types and bodies of repository declarations |

The records are deterministic for fixed sources and toolchain; the emitter's
`--check` mode compares fresh records with an earlier output and names every
added, removed or changed declaration.

## Registry

Every assumption a report names is a registry identifier. A registry entry has a
stable identifier, a category, a one-line statement and a schema: a constant
that, applied to the claim's own data, is the proposition actually assumed. A
model entry's schema is the definition that embodies the idealization.

| Category | Meaning |
|---|---|
| `library-hypothesis` | An open mathematical statement, owned by a named library or by this package |
| `model` | A cryptographic model or idealization: the random oracle on typed histories, exactly uniform challenges, commitments read in the clear |
| `law` | The realized law of a challenge decoder relative to the ideal sampler |
| `trusted-link` | An implementation correspondence outside Lean, stated over the uninterpreted native component |
| `binding/<obligation>` | Statement determination, the serialization of the typed representation, its native absorption, collision-bounded identity, authenticated configuration, verification-key correctness |
| `budget` | A bound on adversary resources |
| `family-property` | An obligation a protocol family proves: a certificate step, a doomed set, a property of a Sigma protocol |
| `event` | A condition on a claim's statement or outcome |
| `well-formedness` | A structural condition or invariant of a lemma's data |

The declaration audit checks the registry: identifiers are distinct, every
schema constant exists, a proposition schema is proposition-valued, and every
proposition-valued declaration of the security package that heads a premise of
one of its theorems, at any binder, is registered.

A registered endpoint maps a covered semantic endpoint, a property and a
statement form to the endpoint theorem that states the property for
artifact-indexed evidence.

## Subject manifest

The generator reads, and otherwise ignores, these manifest fields: `name`;
`entries.proof`; `generated`, the generated Lean modules the subject owns;
`claims.endpoint` (`ideal-meaning` or `executable-bytes`), `claims.properties`,
`claims.statement` (`fixed` or `adaptive`) and `claims.regime`;
`claims.namespace`, the namespace of the subject's generated claims, from which
the claim's declarations are named; and `assumptions.requested`, the registry
identifiers the author expects. In a claims namespace `N`, the artifacts are
`N.artifacts`, the contract is `N.Contract.falseStatement` for ordinary
soundness and `N.Contract.holds` for knowledge soundness, the evidence instance
is `N.evidence` and the application is `N.<endpoint theorem>`. These names
derive from `N` alone: a manifest field that names one of them otherwise
(`claims.artifacts`, `claims.contract`, `claims.application`,
`family.instance`) is a conflicting override, and the pipeline's manifest
schema rejects those fields.

## Pipeline evidence

The subject pipeline writes one JSON document per subject, `<name>.json` or
`<name>/evidence.json` in the evidence directory given to the generator:

| Field | Content |
|---|---|
| `format` | `zkc.subject-evidence/0` |
| `subject` | The manifest's name |
| `manifest_sha256` | SHA-256 of the manifest the run read |
| `artifacts` | Each artifact the run produced from the source, by role, as `sha256:<hex>` (source, original export, constructed export, program, deployment, package) |
| `generated` | For each generated module path, `{"sha256": <hex>}`: the digest of the module the run regenerated from those artifacts and compared with the committed one |
| `checks` | The kernel and native checks of the run, each `{"name", "outcome"}` with outcome `accepted`, `refused` or `unsupported`, and the refused obligation when there is one |

Other fields are kept as provenance and do not affect the outcome.

## Report

| Field | Content |
|---|---|
| `format`, `subject` | `zkc.assurance-report/0` and the manifest's name |
| `outcome`, `reasons` | The report's outcome and any report-level reasons |
| `manifest` | Path, SHA-256, schema and entries of the manifest |
| `artifacts.attached` | For each generated module: path, SHA-256, and the digests the module records about the bytes it was rendered from |
| `artifacts.connected` | Whether pipeline evidence connects the generated data to the artifacts: `connected`, `mismatched` or `unresolved`, with the evidence path, its digest and the artifact digests |
| `checker` | Lean version, Lake manifest digests, dependency pins, and every declared compatibility patch with its upstream revision and patch digest |
| `claims[]` | One claim per property, with the fields below |
| `context` | The theorems the claims ledger cites for this subject, with their statement hashes, axiom closures and classified premises. Context never establishes a claim |
| `allowed_axioms` | `propext`, `Classical.choice`, `Quot.sound` |

Each claim keeps its outcome fields separate, so a single status word cannot
erase its conditions:

| Field | Content |
|---|---|
| `property`, `covered_endpoint`, `statement` | The claimed property, the semantic endpoint it covers and the statement form |
| `validation` | The pipeline's validation outcome as the checks emitted it: `accepted`, `refused`, `unsupported` or `unresolved` |
| `endpoint` | The registered endpoint theorem: name, module, statement hashes, axiom closure and statement |
| `application` | The application declaration, with the same facts |
| `evidence` | The evidence instance, with the same facts |
| `contract`, `artifacts_declaration` | The contract and artifacts declarations the claim must be stated at |
| `assumptions[]` | Every remaining assumption: registry identifier, category, schema, statement, the instantiated statement when the assumption is a premise, its discharge (`assumed`, or a proof) and where it comes from; a named hypothesis also lists its recorded arguments |
| `discharged[]` | The named hypotheses the evidence proves, with their arguments |
| `requested_assumptions` | The identifiers the manifest requested |
| `models[]` | The registered model definitions the endpoint and the evidence reach |
| `regime` | The expected parameter regime and the regime the evidence states |
| `bound` | The application declaration, its statement and the property's instantiated statement: the bound the claim states |
| `outcome`, `reasons` | The claim's outcome and every reason it is not established |

## Generation

1. **Endpoint.** The manifest's covered endpoint, property and statement form
   select a registered endpoint. A covered endpoint outside `ideal-meaning` and
   `executable-bytes`, an unknown statement form, or a combination with no
   registered endpoint is an unsupported endpoint claim.
2. **Application.** The claim is established only through its application
   declaration, which the subject driver generates: its type must be the
   registered endpoint's property, its value the registered endpoint applied to
   the manifest's evidence instance, and its type must name the subject's
   artifacts, contract and, for ordinary soundness, the manifest's regime. A
   declaration that applies the endpoint to other evidence, states the claim at
   other artifacts or at another relation, or applies another theorem leaves
   the claim unresolved (wrong evidence, mismatched artifact, substituted
   relation, wrong endpoint). A missing application, instance or endpoint
   theorem leaves the claim unresolved.
3. **Evidence.** The evidence instance must be the property's evidence
   structure indexed by the subject's artifacts and contract.
4. **Join.** The claim's declarations must belong to this subject's validated
   artifacts: the manifest's generated `artifacts` and `claims` modules are the
   `Artifacts` and `Claims` modules of its claims namespace, both among the
   modules the pipeline regenerated and compared for this subject (see
   *Connection*); the application and the evidence instance are declared in that
   `Claims` module; and the pipeline's evidence records an accepted
   `claim-application` check that built that module with that application. A
   manifest without a claims namespace, a conflicting override, a claims
   namespace whose generated modules are not this subject's, a declaration in
   another module, or evidence without that check leaves the claim unresolved.
   Without the join, a mutually consistent application, evidence, artifacts and
   contract of one subject could be reported for another whose own generated
   modules are connected.
5. **Telescope audit.** Every premise of the application declaration itself,
   of its property and of the evidence instance, read from their fully
   elaborated telescopes with implicit and instance binders, is classified by
   the registry through its head constant. A generated application has no
   premise of its own, so one it states is an assumption like any other. A premise that is not a registered assumption is an omitted
   premise. Every other binder must be a type, an allowed instance or the
   application context; any other parameter, such as a structure bundling
   assumptions, is a hidden parameter. Classified premises become assumptions
   with their instantiated statements.
6. **Named hypotheses.** Each hypothesis the evidence lists cites a registry
   identifier; its proposition must be an instance of that entry's schema (a
   proposition of the same category under another schema is a wrong schema),
   and its status is a proof, a premise of the evidence, or an assumption
   citing the same entry. A premise of the evidence that no hypothesis names is
   an omitted assumption.
7. **Required links.** The trusted links every claim about the covered endpoint
   rests on are listed as assumptions unless a premise already carries them:

   | Covered endpoint | Required trusted links |
   |---|---|
   | `ideal-meaning` | `exporter.structured-denotation`, `exporter.checked-candidate`, `transport.canonical-decoding`, `transcript.encoding-injective`, `binding.native-absorption` |
   | `executable-bytes` | `exporter.structured-denotation`, `runtime.program-reader`, `runtime.acceptance-inclusion`, `runtime.installed-kernels`, `runtime.codec-function`, `transcript.encoding-injective`, `binding.native-absorption` |

8. **Models.** The registered model definitions the endpoint, the application
   and the evidence reach are recorded.
9. **Artifacts.** A digest attached to generated data is not evidence that the
   data came from the source, export and program bytes. The connection holds
   when the pipeline evidence is for this subject and this manifest, every
   generated module equals the module the run regenerated, and every digest a
   module records is one the run produced. Anything else is a mismatched
   artifact, or unresolved without evidence.
10. **Axioms.** An endpoint theorem, application or evidence instance whose
   closure leaves the allowed set, for example one that depends on `sorryAx`,
   leaves the claim unresolved. Dependency and axiom audits are secondary
   checks; the telescope audit decides premise completeness.
11. **Outcome.** A refused or unsupported validation is reported as such.
    Otherwise the claim is `established` only when validation accepted and no
    reason remains; it is `unresolved` otherwise. A report is `established`
    when every claim is.

Two rules decide which equations and bindings a report may count:

- An Entry equation about a compiled meaning is allowed when it is derived from
  checked stage evidence, generated and kernel-checked; a hand-written trusted
  correspondence about a compiled meaning is refused.
- A typed public-value binding discharges statement determination only. Native
  absorption of the public values remains the trusted link
  `binding.native-absorption` until a theorem about native transcript bytes
  discharges it.

## Outcomes

| Outcome | Meaning |
|---|---|
| `established` | Validation accepted; the application declaration applies the registered endpoint to the subject's evidence at its artifacts, contract and regime; every premise is a registered assumption and every named hypothesis an instance of its schema; the artifacts are connected; closures are clean |
| `refused` | A check refused, with a named obligation |
| `unsupported` | A check emitted an outside-fragment refusal |
| `unresolved` | Checking itself could not conclude: an unsupported endpoint claim, an omitted premise, a mismatched or unconnected artifact, a missing endpoint or instance, a forbidden axiom |

Whether a refusal detects a real divergence is an evaluation label, not an
outcome.

The generator's controls require these reactions: an omitted premise, a
mismatched artifact, an unsupported endpoint claim, an unregistered endpoint, a
dependency on `sorryAx`, absent pipeline evidence, valid evidence of another
subject, an application at other artifacts or at a substituted relation, an
application of another theorem, a hypothesis under the wrong schema of its
category, an assumption bundled into the evidence's parameters and a premise
no hypothesis names each make a report `unresolved`, and a refused check makes
it `refused`. An established control report lists its assumptions and models
and renders the instantiated bound.

## Claims ledger and generated tables

`lean/checks/claims.toml` holds the rows of the "What is proved" table of the
[formal guide](../../README.md#what-is-proved), each with the theorems that
carry it; `lean/checks/claims.lock.json` records their packages, modules and
statement hashes. The check fails when a cited theorem is missing, when its
statement hashes differ from the lock, or when it depends on an axiom outside
the allowed set; a reviewed row is accepted by rewriting the lock. The table,
and one row per subject manifest summarizing its report, are rendered between
`<!-- BEGIN GENERATED ... -->` and `<!-- END GENERATED ... -->` markers; the
check fails when a document's region differs from the rendering, and `--write`
rewrites it. Prose stays hand-written elsewhere: every qualified Lean name
that `docs/status.md`, the formal guide, these documents or an integration guide
cites must still be a declaration, a namespace of declarations or a module.
Theorem-name and statement-hash checks catch renames and changed statements, not
semantic drift of the definitions a statement mentions.
