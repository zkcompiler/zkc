# Subject manifests

Each `<name>.toml` here describes one verification subject: the sources it is
compiled from, its Entries, which profiles apply, which Lean modules the
pipeline generates for it, and the data later stages consume. The subject
driver, `python3 lean/bridges/subject.py`, reads only these manifests: adding a
subject is adding a manifest (and its family mathematics in Lean), with no
Python edit. `lean/bridges/pipeline/manifest.py` loads and validates them.

The line between data and code is deliberate. Python holds the pipeline and
the generic mutation kinds; it names no subject. A manifest holds per-subject
data: paths, Entry names, profile switches, which mutation kinds apply, the
names of theorems a receipt checks and the assumption identifiers the author
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
| `entries` | `interactive` | the structured interactive Entry |
| `entries` | `instantiation` | the static instantiation, recorded for reports |
| `profiles` | `structured` | export, Data, Bodies and Views of the interactive Entry |
| `profiles` | `construction` | original Data, constructed participant, generated glue, kernel checks |
| `profiles` | `executable` | program data, executable facts, Lean lowering rule, runtime differential |
| `profiles` | `scalar` | the scalar common-source contract in `[scalar]` |
| `generated` | `data`, `bodies`, `participant`, `glue`, `program`, `facts` | generated modules of the Proof Entry |
| `generated` | `interactive_data`, `interactive_bodies`, `interactive_views` | generated modules of the interactive Entry |
| `generated` | `interactive_export`, `interactive_source` | retained JSON and MLIR of the interactive Entry |
| `generated` | `original_export` | retained original JSON of the Proof Entry, before preparation or projection |
| `normal_forms` | `request` | normal-form request checked with `normal_forms.py --check` |
| `family` | `module`, `instance`, `kind` | family package, its concrete instance, `sigma`, `certificate` or `upstream` |
| `claims` | `endpoint` | `ideal-meaning`, `executable-bytes`, `transform-equation` or `admission` |
| `claims` | `properties`, `statement`, `regime` | claimed properties, `fixed` or `adaptive`, expected parameter regime |
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
