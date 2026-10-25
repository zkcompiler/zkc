# Subject manifests

Each `<name>.toml` here describes one verification subject: the sources it is
compiled from, its Entries, which profiles apply, which Lean modules the
pipeline generates for it, and the data later stages consume. The subject
driver, `python3 lean/bridges/subject.py`, reads only these manifests: adding a
subject is adding physical configuration and typed Lean exports, with no
Python edit. `lean/bridges/pipeline/manifest.py` loads and validates them.

The composed-Sumcheck manifest route has been retired. The same source project
is the `TwoSums` selection in `ZkcSecurity.Generation.Roots.Catalogue`; its
generated subject, soundness requests and completeness receipt are checked by
`python3 lean/checks/check_subject_roots.py --exports DIRECTORY`. Use that root's
exact requests and receipts, rather than the former manifest's unresolved
report. Historical reports remain historical. The old construction modules
remain audited regression clients until their separate retirement.

The line between data and code is deliberate. Python holds the pipeline and
the generic mutation kinds; it names no subject. A manifest holds per-subject
data: paths, Entry names, profile switches, which mutation kinds apply, the
names of maintained regression theorems and the assumption identifiers the author
requests. Nothing in a manifest is Lean source except a model term in
`[construction] model`, which the generated glue states as a definitional
equation that the kernel checks.

## Schema `zkc.subject/0`

Unknown tables and fields are refused. Paths are relative to the repository
root.

| Table | Field | Meaning |
|---|---|---|
| top | `schema` | `"zkc.subject/0"` (required) |
| top | `name` | subject name; equals the file name (required) |
| `source` | `modules` | module map `{ name = "path.zkc" }` |
| `source` | `project` | project directory; its `zkc.toml` and dependencies supply modules and assets |
| `source` | `compiler_options` | extra options for every compiler command |
| `entries` | `proof` | the compiled Proof Entry |
| `entries` | `interactive` | the explicitly selected closed interactive protocol |
| `entries` | `instantiation` | the static instantiation, recorded for reports |
| `profiles` | `structured` | export, Data, Bodies and Views of the interactive protocol |
| `profiles` | `construction` | original Data, constructed participant, generated glue, kernel checks |
| `profiles` | `executable` | program data, executable facts, Lean lowering rule, runtime differential |
| `profiles` | `scalar` | the scalar common-source contract in `[scalar]` |
| `generated` | `data`, `bodies`, `participant`, `glue`, `program`, `facts` | generated modules of the Proof Entry |
| `generated` | `interactive_data`, `interactive_bodies`, `interactive_views` | generated modules of the interactive protocol |
| `generated` | `interactive_export`, `interactive_source` | retained JSON and MLIR of the interactive protocol |
| `generated` | `original_export` | retained original JSON of the Proof Entry, before preparation or projection |
| `generated` | `artifacts`, `claims` | physical generated modules: artifact/compilation facts and exact source Wire.Request data with typed Lean resolution, evaluation and receipts |
| `normal_forms` | `request` | normal-form request checked with `normal_forms.py --check` |
| `lean` | `namespace`, `imports` | generated declaration namespace and maintained Lean registration imports; physical configuration only |
| `assumptions` | `requested` | identifiers of the assumption registry (`ZkcSecurity.Registry`) the author expects; the driver refuses others |
| `mutations` | `kinds` | generic mutation kinds the driver applies (see below) |
| `executable` | `threshold` | `"derived"`: the acceptance threshold comes from the Lean charge |
| `executable` | `public`, `witness` | runtime inputs; default `<project>/inputs/<Entry>/{public,witness}.json` |
| `executable` | `variants` | other compilations of the Entry, `{ Name = [options] }` |
| `executable` | `exact` | expected exactness of the lowering reading per program (`actual` and variants) |
| `executable` | `charge`, `charge_arguments`, `completeness_module` | Lean charge function, the public inputs it takes, and its module |
| `executable` | `namespace` | namespace of the generated facts (default: the facts module's name); a hand executable module of the Entry continues it |

Every generated path is owned by this subject: `--write` rewrites it and
`--check` compares it. Generated paths that another subject or a structured
suite also produces must agree byte for byte.

`[claims]` and `[family]` are rejected, including empty tables. A manifest
cannot request a property, choose a model, set a bound or authorize a receipt.
Source `spec` fixes requests; source `verify` proposes a separately versioned
method. A source with no claims has no source receipt, even if maintained
endpoint theorems exist. The separate scalar bridge remains selected by
`scalar.properties`; it does not authorize source requests.

For a configured Lean namespace, `Artifacts.lean` contains the freshly exported
original, participant and optional program, plus checked compilation/lowering
facts. `Contract.lean` pins the actual retained application or an explicit
registered imported language. `Registration.lean` supplies typed subjects,
property/model registries and small author-library proof exports. Python emits
only Wire.Request and method data and generic Lean construction calls in
`Claims.lean`; it never prints a proposition. Lean computes the meaning before
applying any method, and every receipt proves that computed proposition.
Each generated receipt is an `AdmittedReceipt`: it also carries the exact
subject check and an actual model-resolution witness for the selected typed
model registry. Method consumers use its enclosed generic receipt.

`Endpoints.lean` maintains the prior endpoint theorem APIs as independent
regression clients. Generated Claims imports it for API continuity. Those
statements are not rebuilt from source labels and never authorize source
receipts. The six split modules are Schnorr, ChaumPedersen, SchnorrAnd, Okamoto
in the generic security package and Sumcheck, Guess in optional ArkLib. Their
declaration namespaces remain `ZkcSecurity.Examples.Subjects.*`.

Each source node enters `evidence.source_claims` and `claim_receipts`, including
incomplete meanings and unsupported attempts. A successful physical module
check records the exact request and receipt declaration and generated bytes.
Reports audit actual declaration indices, proof dependencies, assumptions and
fixed stage obligations; provenance strings and receipt status are insufficient.
Full native site paths are walked through the actual original call tree and
matched against the constructed policy; Lean checks actual site membership.
Digest and source-site attribution remain frontend links, with explicit
`source.correspondence` and IR-relative scope. Interpreted program-byte proofs
remain distinct from native runtime/provider correspondence.

Reports select whole compiled subjects. The default scope is the proof Entry;
`--claim-entry 'sigma::Schnorr<example::G>' --subject schnorr` runs the genuine
interactive trial independently. Both runs generate the same declarations.
Requests and actual declaration associations for other compiled Entries remain
visible in `source_claim_trials`. Schnorr's interactive completeness and special
soundness meanings are registered incomplete; their separate report remains
incomplete while the supported proof Entry has its own report.

`source_claim_inventory` lists every source claim node in the checked project,
including claims on subjects that this run did not select. Its `selection` is
`selected` or `unselected-subject`; it is diagnostic inventory, not a request or
proof. Structured-only subjects retain the inventory too. Explicitly selecting
an Entry without matching source claims leaves the report unresolved, even when
another selected Entry has a valid receipt.

Physical Lean file checks use `lake lean`, which applies package options and
builds imported modules. No-build exporters and the already-built Clean control
use `lake env lean` with the same `autoImplicit=false` and `warningAsError=true`
options explicitly. Generated proof-view checks retain the module header and
public exposure used by the installed generated modules.

### Optional extensions

| Table | Field | Meaning |
|---|---|---|
| `construction` | `admission` | how the glue admits the original: `views` (default: from the printed Bodies, which `generated.bodies` must name) or `external` (an existing Views module) |
| `construction` | `views` | the Views module for `external` admission |
| `construction` | `inputs` | `values` (default) or `payloads`: the form of the generated `inputs` |
| `construction` | `names` | binder names of the published inputs (default: source names) |
| `construction` | `model`, `model_imports` | a Lean term the original validator's process is definitionally equal to, and its modules |
| `construction` | `rule` | `compiled` (default: construction and projection) or `construction` (construction rule only) |
| `construction` | `doc` | module documentation of the generated glue |
| `construction` | `omit` | generated declarations not emitted because a hand module in the glue's namespace declares them |
| `bodies` | `entry`, `interactive_entry` | local name of the Entry protocol in the printed Bodies; a unique relation formula is named `formula` |
| `bodies` | `closed` | print the closed-profile root as well |
| `receipt` | `theorem`, `security_module`, `completeness_module`, `chain`, `used`, `unused` | theorems whose axiom closures and dependencies the executable receipt checks |
| `scalar` | `contract`, `namespace`, `module`, `binders`, `arguments`, `inputs`, `unfold`, `properties`, `group`, `composed` | the scalar contract that proof requests select (`lean/bridges/common/registry.py`) |

## Mutation kinds

Each kind is a structural edit applied to whatever the export contains, never
to a compiler-generated symbol. A kind states where it applies; the driver
verifies that the edit changes the export and that the result still renders,
and reports a kind with no target as not applicable, never as a pass. The kinds
and their expected refusals are listed by `python3 lean/bridges/subject.py
--list-mutations`.

## Files

- `fixtures/`: sources of subjects that exist only as verification fixtures.
