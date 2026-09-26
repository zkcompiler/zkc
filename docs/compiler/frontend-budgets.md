# Frontend compiler work budgets

`frontend::WorkLimits` supplies four independent limits to `analyzeProtocol`,
`analyzeProject`, and `compileProject`. Existing overloads use defaults. Each
analysis invocation owns one `WorkBudget`, shared by constant evaluation,
static selection, library formation and every link request, generated source,
and final common-source emission. `Analysis::workUsage()` returns the four
consumed logical counts in `WorkAccount` order, including on failure.

```cpp
zkc::frontend::WorkLimits limits;
limits.libraryFormation = 1000;
auto analysis = zkc::frontend::analyzeProject(project, limits);
```

Every default is 262144. The authored/static and library source work defaults
retain their existing numeric values; generated source and output use that same
initial value as separate accounts. Combining work within an invocation and
adding previously uncharged operations can stop inputs that formerly passed
independent local counters. This narrowing is an intentional policy change, not
a promise to preserve the former worst-case accepted inputs. These defaults have
not been calibrated against a performance corpus. No environment variable
changes them. Internal phase calls require the invocation's explicit budget;
they have no overload that silently starts a new account.

## Logical accounting

These are deterministic operation and structural-slot counts, not elapsed
time, allocated bytes, serialized bytes, or claims of comprehensive compiler
cost. A debit checks the remaining allowance before addition. Bulk copy counts
are checked before multiplication or allocation. Failed debits do not wrap or
consume the rejected amount. Failure ends the phase; no alternate compilation
strategy is selected with the remaining allowance.

| Account | Covered logical charges |
|---|---|
| `AuthoredStatic` | Syntax snapshot/specialization declarations, nested type and body/expression nodes, copied call operand/attribute/static-argument/atom slots and static-term member slots, invocation input/output/result-name slots; existing static substitution visits and specialized protocol header slots; natural declarations and each written expression occurrence |
| `LibraryFormation` | Captured declarations, interface members and signatures, library root/type/expression visits, each requested link/binding/helper, checked body copies, traversal instructions/iterations and transfer generation, type/layout visits and repeated child copies, resource adapter visits, copied leaf slots, and fresh values |
| `GeneratedSource` | Linked function emission, logical binding requests, generated type spellings, value/operand leaf slots, linked instruction visits, aggregate entry headers and shapes, forwarding slots, each scalar or internal function alias copy |
| `Output` | Common module/construction root, carrier metadata declarations and vector slots, emitted declarations and selected header/flattened port slots, nested body instructions and vector operands, construction public bindings and draws |

A declared aggregate or field has a cost even when its physical layout is empty.
Repeated copies of empty array elements still cost work. Each requested link
uses the same account, including aliases of a previously linked body. Generated
entry forwarding does not spend authored constant-evaluation work; its generation
and its final output are charged in their respective accounts. Imported module
declarations are selected in the invocation's resolved source snapshot without
resetting the budget.

Natural evaluation charges its written declaration/expression graph before
evaluation, so memoized dependency values and declaration ordering do not change
that charge. Cached component selections and helper specializations replay the
covered logical cost of constructing the cached result. Generated binding
requests are charged before interning lookup; function requests are charged
before emitted-function deduplication. These counts do not report cache misses
or actual allocation savings.

The public direct library API remains independent of source files:
`library::link(request, budget)` borrows an invocation account for that call.
Its ordinary `link(request)` overload creates a local default account. A caller
grouping multiple requests must pass the same `WorkBudget` explicitly. Neither
`Environment`, `CheckedBody`, nor `LinkedProgram` retains a borrowed budget,
callback, project pointer, or mutable accounting state.

## Refusal and artifact behavior

An exhausted authored/output account reports `source-staging-limit`; exhausted
library/generated work reports `library-source-limit`. Detail names the account:
`authored-static`, `library-formation`, `generated-source`, or `output`.
The analysis has `ResourceLimit` state and cannot yield a `CheckedModule` or
lowered artifact. Earlier completed library judgments remain queryable. Failure
during final emission also retains the checked source judgments. Recovery/query
metadata allocation is outside these accounts.

Limits and usage never enter source content, library identities, environment
fingerprints, or protocol transcripts. For fixed input and compilation choices,
increasing limits componentwise cannot change the selected algorithm or emitted
artifact. Focused tests compare encoded artifacts at exact sufficient limits
and larger limits, and refuse at one unit below each account. This is regression
evidence for the implemented schedule, not a monotonicity theorem.

The budget regression suite also checks a fixed default-policy workload: 1024
specializations of one protocol with eight field inputs and eight field outputs.
It requires successful analysis and emission using the public defaults, without
deriving a limit from measured usage. Together with exact/one-less injected
ceilings, this protects a concrete accepted workload and the refusal boundary.
It does not establish compatibility with the old worst-case input envelope or
calibrate a universal default. Independent structural admission still applies.

## Separate bounds and remaining coverage

`Environment::expansionLimit` remains the existing library admission/profile
limit, including its numeric default and identity encoding. Generic requirement
replay limits, source/carrier structural bounds, Rust/Lean limits, static depth
and specialization-count limits, and runtime resources are unchanged. Raising
a compiler budget cannot bypass any of them.

Uncharged work includes parsing, resolution, dependency discovery and loading,
most ordinary semantic checking and local elaboration, library environment
validation/merging and finite requirement checking, selection identities and
canonical serialization/hashing, several resource-path comparisons and scans,
string/descriptor byte size, relation descriptor payload internals, and query/recovery
bookkeeping. Direct interface/body formation APIs still use their existing
admission checks without caller-injected work budgets. This implementation does
not provide a whole-compiler CPU/memory bound, a wall-clock deadline, or an
allocation quota. Timing, memory measurements, and cache-hit statistics require
separate instrumentation.
