# Numerical units and schedules

Closed numerical computations use named `builtin.module` owners, standard
`func.func` entries and the existing mathematical dialects. The
`exec.computation` unit attribute requests zkc's closed-computation profile.
The ordered invocation is `exec.compute` inside a scoped standard function.
This boundary introduces no runtime instruction, frame, artifact format or
alternative evaluator.

## Unit and call

```mlir
module @square attributes {exec.computation} {
  func.func @evaluate(%x: !algebra.field<"bls12-381.fr">)
      -> !algebra.field<"bls12-381.fr"> {
    %r = "algebra.field_multiply"(%x, %x)
      : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        -> !algebra.field<"bls12-381.fr">
    func.return %r : !algebra.field<"bls12-381.fr">
  }
}
```

The standard module provides an isolated symbol table. An admitted computation
unit has exactly one public, defined standard
function. Private standard functions and `data.domain` declarations supply its
dependencies. References resolve within that owner; implicit captures, external
functions, recursive closures and arbitrary operations are refused. Admission
checks every retained definition, including unused ones.

Ordinary MLIR verification checks the module, functions, symbol uses and marker
placement; the marker must be a unit attribute on a named module. It does not
establish closed-computation admission. The enclosing Protocol stage calls
`verifyComputationUnit` after nested MLIR invariants have passed, for every
nested module, including unreferenced modules and modules missing the marker.
Standalone clients must perform both checks. Only the symbol name and profile
marker are admitted module attributes. Entry lookup and profile classification
are inspection helpers, not admission evidence.

The entry has total, non-affine native data ports. Its explicit
`data.preconditions` remain part of its mathematical contract; public visibility
selects the entry and does not assert that its premises hold universally. A scoped
`exec.compute` invocation must discharge those premises using its actual data
operands. Closing or normalizing a helper retains the conditions verbatim.
Formal polynomials and quotient elements may occur internally but cannot cross
the selected unit's entry boundary. Private helper conditions are checked against their actual
arguments. The shared `TotalClosure` analysis checks the mathematical vocabulary,
dependency closure, bounded access and polynomial observations. An installed
backend implementation alone does not establish these properties.

`exec.compute` supplies a borrowed `!runtime.scope`, exact positional data
operands, a `callee = @square::@evaluate` symbol reference, and a nonempty `site`.
Its result is `!exec.outcome` carrying the entry's data results. The enclosing
standard function handles success and failure explicitly through
`exec.dispatch`. The scope is the owning function's first entry argument.
The qualified reference resolves to the public entry of a sibling computation
unit; a flat reference instead selects a private mathematical function in the
same symbol table.

The invocation is ordered. It cannot be speculated, merged or moved across
guards, effects or stops merely because its callee denotes total mathematics.
It implements `SymbolUserOpInterface`, so ordinary MLIR symbol rewrites update
its actual target. It does not implement `CallOpInterface`: the scope/outcome
adapter has a different signature from its mathematical callee. Ordinary call
argument/result attribute dictionaries and arbitrary assumptions are refused.
Callee resolution and operation verification establish formation; consumers
must also check the complete mathematical closure, actual premises, and
source-to-realization correspondence.

## Formation and preservation

Scoped source emission and participant demand lowering use the same unit
formation mechanism. Source execution references total mathematics through
`exec.compute`; participant demand lowering extracts mathematics at an ordered
action cut, retaining captures and escaped results.

Guards and partial operations remain in scoped execution. Relation formulas do
not become executable roots. The compiler checks copied helper and domain bodies,
actual SSA operands and returned aliases. Units retain original helper bodies
and polynomial DAGs until numerical realization; an origin label is not evidence
of equivalence. Preparation and projection freeze and compare the complete units
alongside their scoped callers.

The `protocol`, `participant` and `exec` profiles may retain logical units.
Physical admission and executable publication refuse every residual unit or
call, including unused definitions. The compiler's internal logical admission
view uses numerical signatures only; it cannot be encoded as `zkc.program/0`.

## Realization

`zkc-realize-computations` transactionally realizes invocations at their existing ordered
positions and removes the units. Physical planning uses the same proposal and
independent reader while retaining the original mathematical subject. Its
checked plan owns the selected scoped candidate and the binding, port and
conversion decisions for that candidate. Materialization applies those decisions
without rerunning numerical selection. The [physical plan](../../compiler/representation.md#checked-physical-decisions)
checks both correspondence edges before publishing the physical result.
The same late transaction handles retained pointwise maps and mixed map/computation
subjects. Each occurrence has bounded legal alternatives; a missing implementation,
unavailable conversion or attributable program-capacity refusal can advance that
occurrence before publication. Semantic mismatches and malformed bindings remain
terminal. Optional attempts keep cumulative work accounts and a separate reserve
for required construction. The final reader checks the original source and actual
selected body; a record of the selection is not semantic evidence.

Normalization and native recipes use
the existing bounded mechanisms and independent readers; they do not define a
second mathematical semantics. An optional call `policy` records the selected
`[finiteBulk, vectorReductionFusion, collectFoldFusion]` compile-time choices.
Omitted policy uses the lowering request's defaults.

Normalization produces another profiled standard module and retains checked polynomial
origins in that owned subject. Recipe conversion consumes its standard entry
and uses a private builtin module for ordinary MLIR conversion. The completed
scoped function and bindings use the existing executable Protocol owner for
closed admission before the body is inserted at the ordered call. This
temporary storage is not another public IR stage. Source helpers resolve
against the numerical owner, while generated bindings belong to the executable
candidate. The independent numerical reader compares the original entry with
actual output and never invokes the recipe producer.

A closed recipe fragment has one builtin module containing
one executable Protocol owner. Neither owner has operands, results or block
arguments. Its declarations are resolved runtime bindings and scoped standard
functions, with one root interface and any required outlined control bodies.
The independent reader checks this entire fragment, including dormant
declarations and scope/outcome associations, before comparing its actual data
coordinates and ordered instructions with the mathematical entry.

Structural analysis retains numerical call occurrences independently of their
selection policy. An enclosing finite optimization must still honor every
retained call's replacement restrictions. Analysis views borrow immutable source
operations and must be rebuilt after body or interface edits.

Numerical instruction sites derive deterministically from the ordered call site
and normalized operation position. Authored execution sites and protocol event
identities are preserved. No per-operation provenance list is stored in a call.

Inside a total closure, normalization folds static dimensions and exact array
projections and removes unused total arithmetic. Finite computations are not
removed by this cleanup. The independent helper-meaning reader checks the
simplified return coordinates. This is a mathematical realization choice before
executable accounting, not permission to remove an existing ordered instruction.

Each authored invocation expands at its ordered position. Compiler-generated
calculation wrappers may expose additional concrete ports to retain numerical
results across action cuts. Only independently identified polynomial-generated
work can reuse an exact earlier producer in the same participant block. A
generated projection may also forward the exact element of a retained concrete
pack. The subsequent port-sharing step keeps concrete operations distinct and
ordered, including unused work in its normalized input. Independent readers
check normalization, actual port wiring, original
return coordinates and unchanged surrounding guards and effects.

These cuts are actual `protocol.local_call`
actions into generated `func.func` definitions containing `exec.compute`.
Original data arguments and return payloads remain exact prefixes. A new
coefficient result extends the computation's outcome and its unique dispatch
success block, then the wrapper's returned payload and participant call. A
new input extends the consumer's data arguments after its borrowed scope.
Root failure packaging keeps the same stop value and adopts the wrapper's
extended outcome type. Guard bodies, scope transfers, control successors and
all other block interfaces stay unchanged. The independent frontier reader
checks these distinctions; an outcome result is never treated as a numerical
data result, and the scope is never an exported coefficient.

Expansion adds no native local frame,
entry/return charge or destruction point. Installed implementation restrictions,
native failure behavior and the [canonical execution accounting](execution.md)
contract remain applicable. Compile-time work is bounded independently of
runtime capacity. Total mathematical meaning does not promise execution under
arbitrary work or memory limits.

Numerical substitution charges its complete input scan before recursive
admission to the shared context-checking allowance. It reconstructs scoped
execution from logical steps rather than cloning the input physical CFG.
Actual declaration clones and logical operation/data-port expansion spend the
construction allowance. Inspection and independent correspondence checks remain
cumulative across attempts; inspection exhaustion is a required refusal, even
when the proposed construction is optional.

Preparation charges actual source/frontier snapshots and normalization emission
as construction. Its independent normalization-context and frontier readers use
the cumulative context-checking account; exhausted checking is a required
refusal, including during speculative preparation. Standalone preparation checks
before returning. A containing physical transaction may defer an unchanged
scoped-context comparison to its complete independent actual-body reader. A
polynomial frontier rewrite still requires both immediate independent context
readers and checked origins.

When independent normalization finds no polynomial frontier, numerical readback
borrows the immutable original scoped context and constructs only the checked
mathematical units needed by its actual calls. The reader owns this entry mapping;
producer choices and occurrence maps do not supply it. This avoids cloning a
complete context solely to reconstruct its mathematical entries and then compare
that clone with the context just copied. Original and actual complete subjects
still receive admission, including dormant declarations, and actual scoped bodies
remain independently compared. If a frontier can change, readback retains the
complete checked normalization/frontier subject instead. All performed work,
including work before choosing that subject, remains charged.

The unit remains the logical source. Numerical realization emits a private
scoped schedule directly from immutable mathematical expressions, before its
selected scoped CFG and physical conversions. The physical plan also checks
optional binding-lifetime decisions before publication.
[Native numerical calls](../runtime/numerical.md) use checked typed storage views
and private destinations inside existing installed handlers. This does not turn
nominal scheduled values into addressable buffers. Compiler buffer lowering and
target-specific vectorization remain separate work. Participant scheduling,
transcript state, transport and capability authority retain their own owners.

## Numerical loop schedule

The private schedule uses scoped `func.func`, Exec and Runtime operations, with
`scf.while` and `scf.execute_region` carrying loop continuation and transfer
outcomes. The numerical producer emits this form directly, including scalar
branches and normalized finite callbacks. The schedule is an internal compiler carrier;
its dedicated reader admits it, and executable admission still requires flat
scoped CFG. A scheduled owner is not a publishable executable artifact.

A scheduled loop has unsigned signless `i64` comparison and unit increment. Its
three SCF iterates carry the coordinate, continuation bit and transfer outcome.
An explicit `exec.range` retains reached lower/upper admission before any seed
transfer, including empty and reversed intervals. Each iteration checks its
coordinate, enters a scope, invokes an outlined body with explicit state and
captures, exits that scope, and transfers the resulting state. Stopped paths
release the previous transfer exactly once. Conditional continuation consumes
its new condition tuple separately. Final output publication accepts the final
transfer only after successful outcome dispatch.

The bounded schedule reader checks actual SCF/CFG edges, outlined calls,
cleanup, failure propagation, occurrence sites and output ports. Ownership
analysis follows region entry, yield, continuation and backedges; every join
must agree on the live owned resources. These checks grant no general SCF or
native nested-region admission. General SCF canonicalization requires its own
preservation argument for this profile.

The mathematical reader independently compares the original domains, callbacks
and state with the actual scoped schedule. The CFG consumer then uses only the
schedule's admitted SSA association. A separate comparator reads the emitted
CFG against logical definitions reconstructed from that immutable schedule,
checking its full binding and function inventory. Neither comparison replays
recipe emission or substitutes the earlier mathematical candidate for the
actual schedule. Required construction and checking allowances remain shared
across nested callbacks and optional retries. Generated traversal site bytes
spend the same construction account as root site bytes; discarded alternatives
retain their own actual debit without reducing the selected ordered allowance.

## Collect–fold composition

`--fuse-collect-fold` enables checked streaming composition of an unfiltered total
field-vector or field-sequence collect and its adjacent total fold. It defaults
to false and is independent of finite bulk selection and vector reduction fusion.

The collected vector must be used only by that fold. The consumer domain is
exactly its elements or indices. Element callbacks cannot observe the whole
vector; indexed callbacks may read it only at their current position through
bounded access. Duplicate argument/capture aliases are checked at every use.
The composition retains the producer's complete domain admission and enumeration,
then executes its body followed by the fold step for each item. Original seeds
and ordered state coordinates are preserved, including mixed or empty state
tuples; no associativity law is required.

Shared or escaping collections, filtering, nested finite callback computations
and unsupported whole-vector observations retain the materialized path.
The independent reader compares both original callbacks with the actual composed
traversal. A fusion label or synthetic source fold is not correspondence evidence.
Fixed implementation restrictions and ordered call boundaries remain applicable.

Removing a collection can reduce storage and traversal work, but scalar streaming
may be slower than native bulk kernels. This is an explicit compilation choice
with the usual sufficient-capacity mathematical contract; it does not promise
identical resource exhaustion or faster execution for every workload.

## Selected endpoint closure

After complete source construction and paired-role checks, including counts of
communication-free loops, closed participant formation performs one scoped
expansion and forms nominal mathematical Exec computations. Selecting an
endpoint is a subsequent common compiler operation; it performs no CPU recipe,
resident representation or physical implementation selection.

The source must be a completely admitted closed Exec module. The selected role
has exactly one participant. Retain that participant, entries restricted to its
role, and the transitive executable symbol dependencies resolved from actual
uses, including nested symbol references. A nested reference retains the exact
symbol-table shells and demanded leaves; a reference to a symbol table itself
conservatively retains its entire body. Bodies, attributes, contracts, order and
SSA of retained definitions remain exact, ignoring locations. Unknown or
unresolved references refuse. Closure traversal and comparison are bounded.

The checked owner retains an immutable complete source snapshot separately from
its executable candidate. Full projection correspondence records stay with that
source; they are not executable target support obligations. The selected
candidate retains its module/symbol contracts but excludes full paired-role
projection records and unreachable definitions. Target support admission reads
the actual selected candidate. The independent endpoint reader re-admits both
subjects and compares the selected source definitions, entry targets, nested
shells and exact dependency inventory against the supplied candidate. Generic
symbol DCE, caller-provided hashes and edited snapshots grant no correspondence.

This structural crossing assumes earlier source/construction checks. It does
not prove target lowering, cryptographic soundness or equal resource behavior
between execution targets.
