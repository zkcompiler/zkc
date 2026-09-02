# F0-V Owner-View Publication Repair Design

> **Kind:** Temporary reopened-F0 architecture selection and repair contract
> **State:** F0-V0 candidate comparison and F0-V1 publication-topology
> feasibility complete. The selected architecture compiles identically through
> both publication implementations and survives its bounded mutations; F0-V2
> exact grammar and target migration remain open. No target source, profile
> revision, identity table, evaluator, or Analysis profile has changed
> **Authority:** None. Names and encodings below are research coordinates until
> the PIR owner contract is changed and independently republished.
> **Input:** The
> [`F1-R1C0 source-determinacy audit`](f1r1c-owner-view-source-determinacy.md)
> returns `CannotAnswer/F1R1C-C-SOURCE-DETERMINACY`.

## 1. Outcome

F0-V selects an in-place PIR-owner repair with a stricter separation between
owner facts and consumer reads:

```text
exact admitted Core or Protocol handle
  -> complete immutable PIR-owned static-view snapshot
  -> exact profile-local view-schema declaration
  -> complete owner binding plus fresh local capability
  -> consumer-owned question-relative field selection
  -> PIR-owned closure/adequacy check over that selection
```

The immediate F1 pilot uses the complete-view manifest. Proper-subset
projections remain fail-closed until their constructor-specific dependency
graph is published and independently implemented. This lets formal-source
reification test the exact owner boundary without making an unreviewed partial
closure algorithm part of the trusted claim.

The selected repair also splits the current shared source-authority body route:

- consumer and purpose role bodies remain common PIR vocabulary and may be
  imported from Interaction;
- binding payload, capability requirement, no-policy declaration, and policy
  closure bodies are profile-local, closed, and family-tagged; and
- no imported compiler claims to interpret payload bodies defined only on a
  dependent profile's page.

This changes neither `InteractiveCore` nor `Protocol`. It changes the profile
contract governing views of those owners and therefore rotates semantic
profile identities and their dependency cone.

The executable F0-V1 gate under
[`evaluation/formal-source-owner-view-repair-f0v/`](../../../../evaluation/formal-source-owner-view-repair-f0v/README.md)
now establishes that this topology fits the existing publication mechanism.
Two independently implemented compilers agree on all eighteen synthetic
profile bodies and identities; the repair rotates exactly the predicted
sixteen-profile cone and leaves `analysis-kernel` and `oir-endpoint-graph`
stable. Its 18/18 frozen findings include ten dual-path mutation refusals.
Canonical body grammar and proper-subset closure intentionally remain
`CannotAnswer`, so this result is permission to design F0-V2 precisely, not a
claim that the target has already been repaired.

## 2. Constraints recovered from the live target

The repair must satisfy all of the following at once:

1. PIR remains the sole owner of Core/Protocol view facts, derivation, schema,
   read closure, binding, and live capability.
2. A consumer selects fields and a purpose but cannot define a PIR body,
   resolver, closure edge, or authority payload.
3. A profile-local view kind resolves through an authenticated declaration
   reference, never a display name, open callback, or ambient registry.
4. Foundation continues to own canonical values, profile publication,
   profiled IDs, generic inert bindings, and generic capability-requirement
   wrappers; it does not learn PIR view semantics.
5. Analysis may state and check a question-relative read proposition, but it
   cannot repair an absent PIR schema or treat its own field list as source
   authority.
6. A serialized view, digest, package, or structurally equal local object never
   recreates an admitted owner handle or live capability.
7. Missing exact schema or closure premises produce `CannotAnswer`,
   `Unsupported`, or another qualified noncompletion branch, not an invented
   affirmative or semantic negative.
8. The design must permit a clean-room evaluator and two independent profile
   compilers to reconstruct the same declaration coordinates and identities.

## 3. The gap is wider than one absent catalog

### 3.1 Static-view declarations

Interaction source names five Core views and one Protocol `ExecutionView` and
claims a closed `PIRViewSchemaCatalog`. The published profile has no such
owner-local catalog and no declaration selector for any of the six schemas.
Canonical-framed and duplex source pages use the same profile-local-kind idea
for their construction and checked-result views, but their manifests likewise
publish no static-view schema catalog. The Interaction repair should therefore
define a reusable profile pattern, not a one-off hidden table.

### 3.2 Source-authority body routing

The current Interaction profile maps all six `pir.source-*` subject kinds to
one `source-authority-envelope-body-v0` declaration selected by
`PIRSourceConsumerRoleBody(x) = R`. Canonical-framed FS, duplex FS, and public
setup import that same declaration for family-local payload, requirement,
no-policy, and closure bodies that the Interaction source fragment does not
contain. Endpoint and Interface already show the safer direction by owning
most family-specific envelope bodies locally and importing only common roles.

One generic compiler could be repaired with an open `MetaValue` payload, but
that would move exact family shape from the compiler into an admission
side-condition and make independent body reconstruction less direct. F0-V
instead chooses exact per-kind compilers and profile-local family variants.

### 3.3 Complete owner facts versus consumer reads

The existing issuance operation internally derives a complete view and then
returns a caller-selected closed projection. That is a valid attenuation model,
but the written contract currently couples three different obligations:

```text
complete owner-view derivation
atomic schema and field resolution
question-relative least read closure
```

Formal reification does not need all three to mature simultaneously. Once the
complete schema is exact, the complete leaf manifest is canonical and is
trivially closed. The F1 pilot can therefore validate full owner derivation and
source authority first. A later proper-subset projection gate can then test the
dependency graph without weakening or blocking the full-view result.

## 4. Candidate comparison

| Candidate | Main advantage | Dominant problem | F0-V disposition |
|---|---|---|---|
| **V-A: repair Interaction in place** | Preserves one owner/profile coordinate, existing handle lifecycle, and exact dependency rotation | Requires explicit catalog, grammars, envelope split, and profile migration | **Select**, with complete-view-first staging |
| **V-B: separate static-view profile importing Interaction** | Could preserve the old Core-profile body | Creates two profile coordinates for one owner, weakens the current equality law, and needs a new compatibility/selection authority | Reject unless a later compatibility requirement justifies it |
| **V-C: portable identified full-view subjects** | Easy cold transport and direct package roots | Adds a second durable identity family for derived facts and still needs an owner correspondence check; unnecessary before a real portability trigger | Defer; the neutral formal-source package is the current portability experiment |
| **V-D: derive directly from Core/Protocol in Analysis** | Avoids PIR view declarations | Makes every Analysis consumer reimplement PIR derivation and turns omission bugs into cross-owner disagreement | Reject |
| **V-E: Analysis-owned shadow view schema** | Fast local unblock | Assigns source meaning to the consumer and can affirm a non-target projection | Reject |
| **V-F: Foundation-wide generic view kernel** | Uniform mechanism across domains | Moves PIR body and closure meaning into Foundation before cross-domain repetition is demonstrated | Reject |

V-A wins on authority, identity clarity, clean-room implementability, and
failure locality. Its profile rotation is not a reason to choose a weaker
model: the target tree has no historical compatibility promise, and the view
contract is identity-bearing semantic meaning.

## 5. Selected profile contract

### 5.1 Catalog shape

Interaction adds one owner-local declaration kind, provisionally
`pir.static-view-schema`, with exactly these six entries in fixed manifest
order:

```text
public-binding-view-v0
strategy-decision-view-v0
public-coin-view-v0
effect-view-v0
claim-reduction-view-v0
execution-view-v0
```

Each source-bound declaration denotes this complete semantic record:

```text
PIRStaticViewSchemaDeclaration = {
  view_kind,
  owner_subject_kind: pir.interactive-core | pir.protocol,
  complete_body_schema,
  complete_body_compiler: ProfileDeclarationRef<"pir.body-compiler">,
  full_snapshot_derivation_law: ProfileDeclarationRef<"pir.semantic-law">,
  atomic_field_resolver_law: ProfileDeclarationRef<"pir.semantic-law">,
  required_read_closure_law: ProfileDeclarationRef<"pir.semantic-law">,
  binding_payload_compiler: ProfileDeclarationRef<"pir.body-compiler">,
  capability_requirement_compiler:
    ProfileDeclarationRef<"pir.body-compiler">,
  no_policy_compiler: ProfileDeclarationRef<"pir.body-compiler">,
  policy_closure_compiler: ProfileDeclarationRef<"pir.body-compiler">,
  law_field_bindings:
    CanonicalMap<exact field path,ProfileDeclarationRef<"pir.semantic-law">>
}
```

This is a profile declaration, not a new semantic subject, module root, or
runtime registry. Its catalog body remains the existing source-bound
`DefinitionBodyV0`; the selector and exact dependency refs authenticate the
owner source implementing the displayed contract.

Canonical-framed and duplex profiles should later publish entries of the same
catalog kind for their own four view schemas. Their entries remain local to
their exact profiles and cannot substitute for Interaction entries.

### 5.2 Exact body and coordinate grammar

The Interaction source must supply one closed body compiler for the common
coordinate/path/boundary/manifest algebra and exact functions for all six
complete view bodies. A compiler declaration may select one closed tagged
dispatcher, but every arm and every nested aggregate must be present in the
authenticated source. A display record with phrases such as “exact producer
edges” is not the compiler.

The grammar may reuse existing Appendix-A body functions by exact declaration
reference. It must state whether an imported body is traversed recursively or
is one permitted atomic `PIRReference` boundary. No implementation reflection,
field-name lookup, wildcard, or host-language dataclass shape participates.

For v0, map entries resolve through their canonical sequence-of-entry encoding;
paths use only the already selected `Field`, `VariantCase`, and
`SequenceElement` steps. Empty and nonempty sequence behavior, map key/value
fields, optional arms, and repeated equal-valued occurrences must be explicit.

### 5.3 Law-valued fields

The first Interaction mapping is explicit rather than inferred from names:

| View field | Exact profile law declaration |
|---|---|
| `StrategyDecisionView.prover_view_formation` | `core-admission-v0` |
| `ExecutionView.visible_history_law` | `execution-and-replay-v0` |
| `ExecutionView.generated_execution_law` | `execution-and-replay-v0` |
| `ExecutionView.replay_qualification_law` | `execution-and-replay-v0` |
| `ExecutionView.relation_run_view_issuance_law` | `run-view-issuance-v0` |

The schema types `prover_view_formation` as a
`PIRProfileLawReference` despite its historical name. The nested Challenge
field `fresh_law` is not in this table: it retains the exact Core
`ProtocolDeclarationRef<"pir.public-coin-law">` type and is not a profile-law
proposition.

If a narrower dedicated law is later preferred to `core-admission-v0`, it must
be published and referenced explicitly; an evaluator may not invent that split.

### 5.4 Complete-view-first issuance

F1-R1C uses:

```text
DeriveCompletePIRStaticView(exact admitted owner handle, exact schema entry)
  -> complete immutable owner view

CompletePIRStaticViewManifest(schema,concrete_view) =
  ascending unique sequence of every atomic leaf coordinate in concrete_view
```

The bounded evaluator accepts only a requested manifest equal to that complete
manifest. A well-formed proper subset returns `Unsupported` until the exact
constructor-specific dependency relation is implemented; malformed, duplicate,
reordered, interior, wrong-boundary, or cross-view paths retain their ordinary
qualified failures.

This is not a claim that proper-subset projections are undesirable. It is a
proof-ordering decision: first establish exact complete source reification,
then optimize attenuation behind a separate falsifiable gate. Analysis may
still declare a question-relative read set over the complete owner view; its
checker must show which available fields it actually consumed.

### 5.5 Source-authority compiler split

The common Interaction declarations become two exact role compilers:

```text
source-consumer-role-body-v0 -> PIRSourceConsumerRoleBody
source-purpose-role-body-v0  -> PIRSourcePurposeRoleBody
```

Every profile routes the other four subject kinds to exact local compilers:

```text
pir.source-binding-payload       -> local closed family-tagged body compiler
pir.source-capability-requirement -> local closed family-tagged body compiler
pir.source-no-policy             -> local closed family-tagged body compiler
pir.source-policy-closure        -> local closed family-tagged body compiler
```

Interaction's local variants must cover at least static-view issuance,
relation-run-view issuance, and confidential-initial-Oracle issuance wherever
that subject kind is used. A policy-bearing confidential family does not gain
a fabricated no-policy arm. Canonical-framed, duplex, public-setup, endpoint,
and Interface profiles own their own family variants. Common roles are imported
only because their physical body is genuinely identical.

One compiler per subject kind is preferred over one selector claiming six
unrelated bodies. A profile may use a closed family-tagged sum within one
subject kind when it owns several families.

## 6. Identity and migration cone

Changing the Interaction source or manifest rotates the Interaction profile
and every profile whose exact import closure contains it. The current
publication graph gives this sixteen-profile cone:

```text
interaction
canonical-framed-fiat-shamir
duplex-sponge-fiat-shamir
public-setup
commitment-opening
oracle-commitment
verifier-derived-query-plan
interface-plan
endpoint-source-view
oir-projection-relation
relations
analysis-cryptographic-property
analysis-afk-transport
analysis-afk-theorem-source-validation
analysis-incremental-composition
analysis-incremental-composition-source-validation
```

The migration must not rewrite old bodies under new meanings. Before changing
the target, the publication pass must decide and record:

1. which locally changed profiles increment their human syntax-dispatch
   `revision` field;
2. how the old frozen Interaction row remains available as historical evidence;
3. which F1-R1A/R1B fixtures are regenerated under the new profile and which
   remain old-profile refusal controls;
4. that unchanged Core domain bytes receive new profiled IDs rather than being
   relabelled in place; and
5. that no equality or compatibility edge exists unless PIR later checks one
   explicitly.

The large cone is expected semantic dependency, not collateral implementation
damage. It is also why the repair should be one reviewed checkpoint rather than
piecemeal source edits that leave dependent profiles incoherent.

## 7. Execution program

### F0-V1 — publication-topology feasibility

- form the six-entry extension catalog through both publication compilers;
- split common role and family-local envelope compiler routing;
- freeze exact dependency and selector inventories;
- measure the sixteen-profile rotation cone; and
- reject missing/extra schema entries, wrong owners, wrong law refs, old shared
  envelope routing, and unreachable declarations.

This phase may use in-memory manifest/page overrides. It does not claim the
complete target grammar has landed.

**Result:** complete at research resolution with
`Affirmative/F0V1-A-PUBLICATION-TOPOLOGY`. The synthetic candidate repairs
Interaction and the five direct users of its catch-all compiler together,
advances those six local revisions, reconstructs through both publication
implementations, rotates exactly sixteen profile identities, retains two
outside-cone identities, and refuses ten topology mutations. The complete
canonical grammar and proper-subset closure are still classified
`CannotAnswer`.

### F0-V2 — exact target source and identity migration

- write and review all complete body, coordinate, path, boundary, manifest,
  law-map, and authority-envelope grammars;
- update Interaction and directly affected dependent manifests coherently;
- choose explicit revisions and regenerate identities through both compilers;
- retain old-profile substitution controls; and
- run publication, link, public-tree, and mutation gates.

Only F0-V2 changes the target.

### F1-R1C1 — complete-view evaluator

- reuse the exact R1B admitted Core and Fresh Protocol lifecycle;
- derive all six complete views independently of caller data;
- enumerate and resolve every concrete atomic leaf;
- require the exact complete manifest;
- form the exact local binding payload, requirement, no-policy, and closure
  values; and
- issue process-local nonserializable research capabilities.

R1C1 remains offline research authority. F1-I later binds the same contract to
the live implementation owner.

### F1-R1C2 — proper-subset closure

Only after R1C1 succeeds, publish and implement the exact per-constructor
dependency relation. Mutations must cover omission, phantom reads, equal-value
coordinate aliasing, wrong boundary, cross-view paths, law substitution, and
non-minimal but closed supersets. Enabling partial projection is an affirmative
result of this gate, not an assumption inherited from prose.

### F0-V3 — sibling-profile completion

Canonical-framed and duplex static-view catalogs and every directly affected
profile-local source-authority body family receive the same treatment before
their views support a formal-source or theorem-applicability claim. Their work
does not block the Fresh Interaction R1C1 pilot once the common imports are
coherent and fail closed for unsupported sibling views.

## 8. Decision and reversal conditions

Proceed with V-A and complete-view-first staging unless one of these is shown:

- a static Interaction view contains confidential value material that makes a
  complete view unavailable to an authorized F1 consumer;
- the complete canonical body cannot fit constitutional limits even with
  existing owner-reference reuse;
- a real independent consumer requires a stable portable PIR view identity
  rather than the neutral formal-source package; or
- the profile publication mechanism cannot express the selected catalog and
  exact imports without a new common PIR profile.

The first two would change the attenuation strategy. The third would reopen
portable identified snapshots. The fourth would reopen profile placement, not
PIR ownership.

## 9. Non-claims

This selection does not yet provide the canonical grammar, rotate a profile,
admit a new Core, derive a view, establish Q1, validate a formal provider,
prove a theorem, or verify an implementation. It selects the repair boundary
and the order in which those claims may be attempted without guessing.
