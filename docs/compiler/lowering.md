# Selective lowering and evidence

Expand a logical operation only where its
remaining consumers can use the replacement and its actual semantic obligations
are covered. Keep the original source independently, check the resulting
candidate, and separate compiler analyses from runtime facts and reusable
evidence. These boundaries sit inside the
[logical-call representation](calls.md).

The [refinement specification](../spec/verification/refinement.md) owns the
preservation judgments; this page chooses implementation responsibilities.
Neither a rewrite log nor an MLIR legality result establishes those judgments.

## 1. What an expansion must retain

A logical operation has a selected signature and meaning. Its expansion supplies
a body, actual operand/result correspondence and applicable law. The surrounding
protocol can remain at a higher level: lowering one polynomial evaluation need
not lower a second evaluation, select a transcript construction, inline a
component or choose storage.

Before removing information, account for every remaining consumer:

| Consumer | What permits the expansion |
|---|---|
| A terminal check or connector | Retain the original object, ordered residuals and actual input mapping, or provide the specified exact consumer correspondence |
| An optional optimization | Retain enough structure, or use a sound summary; insufficient precision disables the optimization |
| Source/endpoint admission | Establish admission on the original source before rewriting and supply any required target admission or all-reply transport |
| Complete execution | Preserve the selected returned/stopped behavior, related post-state and observations |
| Native resources or acceptance target | Supply that target's representation, capacity, domain and input/output obligations |

The [summary laws](../spec/verification/analysis.md#summaries-and-exact-consumers)
allow conservative information loss. They do not recover an erased fact or
authorize removing a required check. A representation that preserves a value
may lose its factor decomposition, original coordinates or materialization cost.
Keep a logical descriptor or finish its required consumer before that loss.

## 2. MLIR implementation

Use `OpConversionPattern` for supported local expansions and `ConversionTarget`
to select which occurrences must change. Use remapped operands supplied by the
conversion adaptor. Add a `TypeConverter` when types change; same-type expansion
does not need one. A partial conversion is an intermediate operation, not an
export gate. [MLIR conversion](https://mlir.llvm.org/docs/DialectConversion/).

Keep semantic export and rule checking separate from pattern registration.
Patterns may use heuristic profitability or search. A checker resolves the
selected rule and meanings independently, using the actual source and candidate.
The first implementation can support a small set of fixed expansions rather
than a general arithmetic solver. Unsupported but equivalent candidates may be
declined. [Translation validation](https://xavierleroy.org/publi/validation-regalloc.pdf)
provides this separation; that work's verified validator is not imported here.

Admit the original source before running an optimizing or conversion driver.
A driver can simplify operations beyond the authored pattern: for example,
removing an unsupported same-type cast could hide a source-formation error.
Validate the logical grammar on the retained original, then check the transformed
candidate. Checking only a simplified clone does not establish original admission.

After transformations, check the supported export grammar recursively and
reject unresolved casts or unsupported operations. Do not mark a containing
function or protocol recursively legal merely to preserve its outer form.
Record edits through the rewriter API for correct driver behavior; an edit
listener remains provenance rather than a proof. [Pattern rewriting](https://mlir.llvm.org/docs/PatternRewriter/).

For the initial C++ library, keep three responsibilities distinct:

- Domain libraries define registered operations, signature/meaning references
  and semantic export. An unknown interpretation prevents admitted export.
- Conversion passes register patterns and legality, then preserve only analyses
  whose results their actual edits leave valid.
- The checking boundary consumes immutable source/candidate exports and
  caller-resolved contracts. A producer cannot install a rule by naming it.

These stay in C++/MLIR. Rust consumes the checked artifact and runtime contract;
it does not participate in per-operation rewrite or analysis round trips.

## 3. Three invalidation mechanisms

| Mechanism | Trigger | Initial policy |
|---|---|---|
| Compiler analysis cache | IR, configuration or referenced dependency changes | Rebuild affected analyses unless a pass explicitly establishes preservation |
| Runtime semantic facts | An actual operation changes state, availability or observations | Apply the selected outcome-specific transfer law, including failed calls |
| Accepted-subject/evidence cache | Source, candidate, meanings, input domain, observer, rule or target changes | Match the immutable complete subject; otherwise check the new subject |

MLIR's pass manager manages the first mechanism and trusts preservation
declarations. It does not prove them. A pass that removes two operations must
invalidate an analysis counting them, even if it preserves an ordered-callee
summary. That summary says nothing about call operands' semantic correctness.
[Pass management](https://mlir.llvm.org/docs/PassManagement/).

The second mechanism uses the existing
[module contracts](../spec/core/contracts.md) and fact/availability rules. A
pure compiler rewrite does not itself consume a challenge or establish a live
runtime fact.

For the third, freeze the checked subject rather than retaining mutable aliases
to caller objects. A digest can index a record; it does not authenticate a
portable certificate. The admission-to-use join must bind the object actually
loaded or executed under the consumer's selected policy.

## 4. Meaning versus artifact identity

A transformation check and artifact identity answer different questions:

1. A semantic projection retains the declarations, bindings, actual control and
   expressions needed by the selected preservation relation.
2. Artifact identity binds the executable subject, including representation and
   implementation choices required by its consumer.

A fixed-rule comparator may normalize a supported expansion, allowing CSE to
change instruction sharing while preserving the selected value/state/event
observation. That does not establish unchanged cost or physical representation.
Reusing a narrower semantic lemma across representations needs an adequate
connection to each actual artifact. The
[artifact identity reference](../runtime/artifact-identity.md) owns implemented
identity policies; a rewrite comparator does not replace them.

Exporters and native comparators remain implementation trust boundaries unless
a separate theorem covers them. JSON claiming to be an admitted export is not
a certificate. The [correspondence policy](../assurance.md#6-implementation-correspondence-policy)
separates checking results, differential evidence and mechanized propositions.

## 5. Evidence and next boundary

A selective-expansion test should retain one high-level operation while lowering
another, then compare complete executions before and after full expansion and
eligible CSE. Include stops, independent selected instances, unrelated effectful
calls and mutations of original subject, point and provider binding.
An algebraic identity proves neither its machine arithmetic nor its exporter.

Maintained bounded examples are the
[checked interpolation pass](targets.md#checked-logical-folding) and
[local helper expansion](local-composition.md). Each states its own supported
source, checking relation and limits. Physical planning additionally needs
storage/kernel selection, ownership, cleanup on stops and scheduling contracts;
those are documented in the [protocol pipeline](protocol-pipeline.md) and
[original-source validation](library-design/validation.md). Local expansion
remains independent of component binding; neither introduces a new normative
semantic layer.
