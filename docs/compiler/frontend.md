# Frontend analysis and lowering

The frontend is a typed construction layer above PIR. It retains declaration
identity, nominal source types and static selections while authors build a
protocol. It emits the ordinary common PIR model for independent admission,
construction and compiler lowering. Its selected source judgments are defined in
[resolved authoring](../spec/profiles/source/authoring.md).

```text
captured project sources and relation assets
                │
       syntax and diagnostics
                │
   exact project names / public interfaces
                │
   interfaces / abstract component checking
                │
     coherent linking / typed layouts
                │
   static constants / protocol selections
                │
   retained source analysis + ordered body plans
                ├──────── semantic inspection
                │
       explicit common PIR
                │
    independent admission and construction
                │
        MLIR / backend execution
```

This source model is not another protocol execution dialect. Source records and
static construction need distinctions that common PIR does not carry. Common PIR
continues to own explicit interaction and executable operation contracts.

Authoring rules for components, families, products and constants are in the
[language guide](../language/README.md). This page owns retained analysis,
erasure and implementation responsibilities.

## An owned analysis boundary

[`Frontend/Analysis.h`](../../compiler/include/zkc/Frontend/Analysis.h) exposes an
immutable snapshot. It owns the spelling and resolved model; copying a snapshot
shares that storage. It contains scoped declaration references, structured domain
terms, logical types, nominal records, products, lexical bindings and scopes,
authored signatures, resolved uses and
specialization provenance. Source IDs are local to the snapshot. They are not
stable package IDs, hashes or transcript identities.

Successfully evaluated natural constants retain their values in the snapshot.
Failed static construction retains declaration names and diagnostics, without
claiming that their signatures or values were checked.

Library inspection reads retained immutable interfaces, checked component
templates, abstract bodies and linked representation plans. It does not rerun
checking to reconstruct a successful result. JSON rendering belongs to tooling;
the semantic checker and lowering operate on typed records.

```cpp
const zkc::frontend::Input input(text, filename);
auto analysis = zkc::frontend::analyzeProtocol(input);
// Tooling can inspect diagnostics and retained declarations even on failure.
if (!analysis.complete())
  return report(analysis.diagnostics());
auto checked = analysis.checkedModule(); // Handle llvm::Expected errors.
auto content = zkc::frontend::lower(*checked);
// Independently admit the resulting common document.
```

`CheckedModule` can be obtained only from successful analysis and owns the same
immutable snapshot. It remains valid after the `Analysis` is destroyed. The
`SourceChecked` state describes source formation, not common admission.
`Analysis::lower()` is a convenience route through that same gate.

Successful analysis finalizes common records once from resolved signatures and
ordered body plans and checks their structure. `lower()` returns an owned copy of
that finalized content; changing it cannot change subsequent queries. It refuses
incomplete/failed analysis. Source formation is
not PIR admission: clients must still call `checkProtocolDocument` or an entry
point that performs common admission. Text, portable JSON and programmatic common
records all meet that same downstream boundary.

`zkc-compile protocol-analyze source.pir` presents the retained model. It returns a
diagnostic report even for incomplete text, with an explicit state and diagnostics;
it never outputs an accepted program. `protocol-source` performs common admission
after source elaboration, then emits the common carrier. `protocol-inspect`
remains the admitted common/compiler view. The CLI therefore performs an extra
check beyond the pure `Analysis::lower()` API. These reports have different
subjects.

The pure `analyzeProtocol` API does not open relation assets: uncaptured imports
report `relation-unresolved`. `analyzeProject` accepts immutable captured files and
assets. File-based CLI queries and compilation use `captureProject` first, with
explicit `--library=FILE` roots and bounded relative asset loading. All then use
the same semantic pipeline; `protocol-resolve` exports the frozen relation snapshot.

Library checking returns linked programs, their environment and aliases, and an
immutable inspection report. The coordinator then asks Lowering to prepare common
library functions and typed entry adapters before static selection and ordinary
source checking. Semantics never invokes Lowering. A checked source product is
required for final emission; successful emission keeps its model, actual emitted
names and common content together. Only that paired result can become a completed
analysis. A later failure retains earlier library judgments and diagnostics;
partial recovery cannot expose a `CheckedModule` or final common output.

[`inspectDependencies`](../../compiler/include/zkc/Frontend/Dependencies.h) is a
pure query for owned module, library and relation declarations, source spans and
parse diagnostics. It performs no asset decoding or resolution. Loading consumes
that public result rather than private parser records. Strict loading refuses
incomplete declarations before invoking an asset resolver. Recovering project
capture may discover fully recognized dependencies in partial text; this does not
authorize compilation. Both paths preflight logical requests before reads, and
repeated aliases still consume the relation dependency allowance.

Recovery is at module declaration boundaries. It can retain usable declarations
before and after a malformed declaration; it is not a complete IDE, incremental
database or a guarantee that every unfinished expression has a type.

## Source abstraction and erasure

Records retain nominal type identity and source field structure in analysis.
Their authored-position signatures feed lowering; common PIR receives flat leaf
ports in declaration order. Field initializers still evaluate once in written
order. Two records with identical layouts do not become interchangeable at the
source boundary merely because their emitted leaf types match.

Checked records add constructor authority, not automatic validation of a logical
predicate. Both external functions and external protocols are forbidden from
returning such values without a supported validation route, including nested
checked records. Host inputs selected by an entry have the same restriction.

The frontend does not repeat PIR's cryptographic or affine-resource engine.
Resolved source information gives earlier structural checks and useful queries;
common admission still checks the emitted roles, messages, values and resources.
Imported interfaces and source-only assurance would need their own retained
checking subject. Common JSON alone cannot reconstruct an erased nominal type.

Closed aggregate library entries retain an authored header and a typed forwarding
plan. The ordinary source checker forms the header, preserving nominal records,
zero-length array element types and formation limits. It then checks the plan's
leaf paths, types, target, order and forwarding shape against that formed header
and the checked library function. Checked-record constructor authority also
applies to nested results. This avoids reconstructing aggregate source expressions
only to flatten them again. Variant ports retain the existing flat boundary.

Inspection reports a generated forwarding call at its alias's source location;
it does not invent authored constructions or local bindings for that adapter.
Generated forwarding bodies do not consume the static evaluator's authored
syntax budget. They do consume generated-source and output work; library
linking/layout and ordinary header limits still apply.

## Compiler work limits

[`WorkLimits`](../../compiler/include/zkc/Frontend/Work.h) separates authored
static evaluation, library formation, generated source and final output.
One invocation owns its counters across links and aliases; charges occur before
expansion. Empty layouts still charge their declarations, and caches do not erase
logical obligations. `Analysis::workUsage()` retains completed charges on success
or failure. Callers may inject smaller limits for bounded work and focused tests.

These limits cover selected formation and expansion work, not all compiler time
or allocation. They are separate from protocol runtime resources and portable
admission limits. Exhaustion reports a resource stop with the exhausted account;
it does not refute the source semantics. The [accounting contract](frontend-budgets.md)
defines charged work, omitted work and artifact monotonicity under larger limits.

## Engineering boundaries and assurance

| Component | Responsibility |
|---|---|
| `Syntax/` | Tokens, parser tree, spans, formatting, lexical capture discovery and bounded recovery; no retained semantic model |
| `Model/` | Owned analysis and phase products, typed body plans, immutable reports and paired final content; no retained parser tree or MLIR pointers |
| `Resolution/` | Exact project names, public exports, captured dependencies and lexical lookup |
| `Library/` | Checked interface/component formation, conformance and static linking |
| `Static/` | Pure bounded natural evaluation and domain-term formation rules |
| `Semantics/` | Source typing, requirements, nominal construction, local SSA/control and participant ownership |
| `Instantiation/` | Closed selection, substitution, child/helper generation, provenance and authored construction-selector binding |
| `Lowering/` | Library emission/entry adapters and common headers/bodies from checked types and resolved declaration references |
| `Tooling/` | Inspection and presentation of syntax or immutable semantic snapshots; no independent inference engine |
| `Loading/` | Optional bounded file capture and relation-asset loading; pure analysis never calls this layer |
| `Input.cpp`, `Analysis.cpp`, `Compile.cpp` | Immutable input, explicit phase orchestration and public compile/lower entry points |
| Common source / MLIR | Independent admission, transformations, construction and realization |

Abstract families and concrete protocols share one source checker. Its typed
environments produce concrete protocol body plans directly. Each selected
protocol interface is also compared with typed substitution of its family
interface before emission, including nominal record identity. Local algorithms
reuse the existing bounded inference and SSA-construction algorithms, with leaf
signatures projected from retained authored types. This is one pipeline; it is
not a claim that every useful parsing or inference algorithm was rewritten.

`Zkc::Frontend` links the MLIR-free common services. `Zkc::FrontendLoading` adds
external input capture; neither library depends on IR or CompilerCore. Private
layer dependencies are checked alongside the component DAG. Mutable builders are
consumed when publishing a snapshot, so consumers cannot retain a mutable alias
to the analysis they query.

For the two supported closed module profiles, default domains are resolved while
forming types, including nested logical types. There is no later string rewrite
that can change emitted headers independently of the retained types.

The frontend remains C++ beside its compiler consumers. No per-analysis C++/Rust
exchange is introduced. Rust continues to own artifact/runtime/backend work; Lean
supplies independent meanings and checking/reference execution. A later frontend
may target the same coarse common boundary without sharing C++ pointers.

The relevant formal laws are `Region.denote_instantiate`,
`Region.run_instantiate` and `Region.denote_renameDefinitions`. They state
substitution and actual-callee obligations, including complete execution behavior.
They do not verify this native frontend implementation. Differential tests compare
emission with explicitly authored expansions and send concrete source/participants
to the independent reference and native runtime.

The remaining syntax study also proposes ordinary type parameters, clean
identifier/operator lexing, domain aliases, site attributes and richer loop/result
sugar. These are not claimed implemented by the present foundation.

Package distribution, separately serialized abstract interface artifacts, generic runtime protocol
carriers, generic runtime preparation packages, general dependent inference, macros and
a full editor are later extensions. The retained model provides a place for their
source obligations; it does not report those features as already implemented.

Construction descriptor binding takes a `CheckedModule`, so it cannot pair the
resolved names of one project with the emitted source of another. Resolution
retains the name graph; selector paths and their additional work limits are
computed only for construction. Ordinary source analysis neither traverses that
selector graph nor acquires its limits. No project is reloaded or re-resolved
when binding a descriptor.
