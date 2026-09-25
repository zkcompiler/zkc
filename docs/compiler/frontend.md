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
   static constants / protocol selections
                │
   interfaces / abstract component checking
                │
     coherent linking / typed layouts
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

`lower()` emits structurally checked common records from resolved signatures and
ordered body plans. It refuses incomplete/failed analysis. Source formation is
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

## Engineering boundaries and assurance

| Component | Responsibility |
|---|---|
| `Syntax/` | Tokens, parser tree, spans, formatting and bounded recovery; no retained semantic model |
| `Model/` | Owned types, domains, declarations, lexical bindings/scopes, resolved calls and ordered body plans; no parser tree or MLIR pointers |
| `Resolution/` | Exact project names, public exports, captured dependencies and lexical lookup |
| `Library/` | Checked interface/component formation, conformance and static linking |
| `Static/` | Pure bounded natural evaluation and domain-term formation rules |
| `Semantics/` | Source typing, requirements, nominal construction, local SSA/control and participant ownership |
| `Instantiation/` | Closed selection, substitution, child/helper generation and provenance |
| `Lowering/` | Common headers and bodies from checked types and resolved declaration references; downstream admission integration |
| `Tooling/` | Inspection and presentation of syntax or immutable semantic snapshots; no independent inference engine |
| `Input.cpp`, `Compile.cpp` | Immutable input and public phase orchestration |
| Common source / MLIR | Independent admission, transformations, construction and realization |

Abstract families and concrete protocols share one source checker. Its typed
environments produce concrete protocol body plans directly. Each selected
protocol interface is also compared with typed substitution of its family
interface before emission, including nominal record identity. Local algorithms
reuse the existing bounded inference and SSA-construction algorithms, with leaf
signatures projected from retained authored types. This is one pipeline; it is
not a claim that every useful parsing or inference algorithm was rewritten.

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
