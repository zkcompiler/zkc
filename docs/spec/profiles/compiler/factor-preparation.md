# Factor facts and preparation

This profile combines reusable factor evaluations with stateful module calls.
A fact describes a current view; availability permits a query; an immutable
cache retains a separately keyed prepared value. Each has its own validity law.
The profile uses the common [contracts](../../core/contracts.md) and
[complete execution](../../core/execution.md).

## Factor state and facts

For an arbitrary value type `K`, define:

```text
Key   = (origin : Nat, axes : List Nat)
Fact  = (key : Key, handle : Nat, applied : List Nat, remaining : Nat)
Query = (key : Key, point : List Nat)

State K = (base : Key → List K → K,
           view : Nat → List K → K,
           challenge : Nat → K)
World K = (values : State K, known : List Nat).
```

The key retains an origin and ordered axes. Coordinate identifiers in `applied`
and `point` refer to the state's challenge map. These natural identifiers are
not field elements or evidence authenticating the source. Total maps give
mathematical meanings at every input; they do not establish availability or
the correctness of a physical materialization.

A fact describes the actual view for all tails of its declared size:

```text
Means s f ⇔ ∀ tail : List K, length tail = f.remaining →
  s.view f.handle tail = s.base f.key (map s.challenge f.applied ++ tail)

Valid s facts ⇔ ∀ f ∈ facts, Means s f
Known w available ⇔ ∀ i ∈ available, i ∈ w.known.
```

`Known` is operational availability, not adversarial knowledge. Abstract lists
can omit facts or available coordinates that actually hold. `Means` alone
neither checks query dimensions nor establishes that any query is ready.
It freezes the values of the applied prefix through the actual state, while
quantifying over every correctly sized suffix.

Overwriting view `h` replaces exactly `s.view h`. Define `kill h facts` by
removing every fact whose handle is `h`. If the old facts are valid, the
remaining facts are valid after this overwrite. Retaining fact `f` installs
`tail ↦ s.base f.key (map s.challenge f.applied ++ tail)` at its handle;
`f :: kill f.handle facts` is then valid in the resulting state. A native
producer needs the corresponding actual post-state law.

## Query plans and readiness

The pure query plan is `direct` or `reuse(f : Fact, suffix : List Nat)`:

```text
runQuery s q = s.base q.key (map s.challenge q.point)
runPlan s q direct = runQuery s q
runPlan s q (reuse f suffix) = s.view f.handle (map s.challenge suffix).
```

Let `tail(q,f) = drop (length f.applied) q.point`. The Boolean eligibility
test decides the conjunction:

```text
f.key = q.key
f.applied ++ tail(q,f) = q.point
f.remaining = length tail(q,f)
length q.point = length q.key.axes
∀ i ∈ q.point, i ∈ available.
```

The value checker accepts `direct` unconditionally. It accepts `reuse f suffix`
exactly when `f ∈ facts`, eligibility succeeds and `suffix = tail(q,f)`.
For valid facts, either accepted plan has value `runQuery s q`. Repeated
coordinate occurrences retain their positions; neither set equality of points
nor equal numeric coordinate values can replace the ordered-prefix condition.

Readiness is a separate predicate:

```text
Ready available q ⇔
  length q.point = length q.key.axes ∧ ∀ i ∈ q.point, i ∈ available

checkPlan facts available q p =
  decide (Ready available q) && valueCheck facts available q p.
```

Successful `checkPlan` establishes readiness in its supplied availability list
and value equality under `Valid`. With `Known w available`, that readiness
implies `Ready w.known q`. The direct value-check case alone supplies no such
premise. An empty point is ready exactly at arity zero.

Inference selects the first eligible fact in list order and its exact tail;
if none is eligible it selects `direct`. The inferred plan always passes the
value checker and has the reference value under valid facts. It passes
`checkPlan` only with the additional readiness premise. This selection is a
sufficient search policy, with no optimality or completeness claim.

## Semantic writes and framing

A footprint is `Writes = (bases : List Key, views : List Nat,
challenges : List Nat)`. Its frame relation is:

```text
Frames writes s t ⇔
  (∀ k ∉ writes.bases, t.base k = s.base k) ∧
  (∀ h ∉ writes.views, t.view h = s.view h) ∧
  (∀ i ∉ writes.challenges, t.challenge i = s.challenge i).
```

These equations concern semantic referents and whole base/view functions.
A native adapter MUST include every interpreted alias affected by its actual
writes. The frame is not a heap-separation assertion inferred from different
nominal handles. Sequential frames compose by concatenating each write list.

The sufficient unaffectedness test for fact `f` is:

```text
f.key ∉ writes.bases ∧ f.handle ∉ writes.views ∧
∀ i ∈ f.applied, i ∉ writes.challenges.
```

`Means s f`, the frame, and this test imply `Means t f`. Only the applied
coordinate identifiers are protected by this test: the fact quantifies over
all suffix values, so it need not freeze every future query coordinate.
Filtering a valid fact list by unaffectedness therefore preserves validity.

Optional writes represent unknown effects with `none`:

```text
EffectFrame none s t        = True
EffectFrame (some w) s t    = Frames w s t
survivors none facts        = []
survivors (some w) facts    = filter (unaffected w) facts.
```

Unknown effects preserve no old facts through this summary. Separately proved
exports can establish new facts. Writes before failure count as actual writes;
there is no generic rollback assumption.

## Outcome-specific summaries

A summary is `(writes : Option Writes, exports : List Fact,
revoke : List Nat, reveal : List Nat)`. Its transfer functions are:

```text
keptKnown c available =
  match c.writes with
  | none   => []
  | some w => filter (fun i => i ∉ w.challenges ∧ i ∉ c.revoke) available

nextKnown c available = c.reveal ++ keptKnown c available
nextFacts c facts     = c.exports ++ survivors c.writes facts.
```

List order and duplicates are retained by these concatenations and filters.
Revocation removes old availability, while a simultaneous explicit reveal can
reintroduce it. Revocation alone does not change a coordinate's value or kill
a factor fact; readiness still prevents unavailable queries. Unknown writes
retain neither old facts nor old availability, but allow justified exports
and reveals.

`Justifies c s t`, on actual worlds, requires all four conditions:

```text
EffectFrame c.writes s.values t.values
Valid t.values c.exports
Known t (keptKnown c s.known)
Known t c.reveal.
```

The retained-availability condition applies to the actual old `s.known`, not
just the analysis's current subset. From this judgment, `Valid s.values facts`
and `Known s available`, transfer gives valid `nextFacts` and sound `nextKnown`
in `t`. A summary record alone is not evidence of `Justifies`.

A module specification is `(pre : World K → Prop, post : Bool → Summary)`.
Its implementation returns `(success : Bool, world : World K, events : List E)`.
Satisfaction means:

```text
∀ s, pre s →
  Justifies (post (impl s).success) s (impl s).world.
```

The actual returned Boolean selects the summary. Both branches need their
laws, including failed calls that mutate the world. This unary judgment does
not constrain events or prove replacement of one implementation by another.
The common adapter returns the Boolean as data and retains the actual world
and events. A returned `false` is distinct from an outer stopped execution.
Other result and stop behaviors use a separately specified complete-result
contract.

## Source-derived views and namespaces

The small source for a retained factor is:

```text
Source = base(key : Key) | fix(Source, coordinate : Nat)
key(base k) = k                 key(fix e i) = key(e)
prefix(base k) = []             prefix(fix e i) = prefix(e) ++ [i]
eval s (base k) tail = s.base k tail
eval s (fix e i) tail = eval s e (s.challenge i :: tail).
```

Thus `eval s e tail = s.base (key e) (map s.challenge (prefix e) ++ tail)`.
Source admission requires `length (prefix e) ≤ length (key e).axes` and every
prefix coordinate in the supplied availability list. Its fact at handle `h`
has this key, applied prefix, and remaining arity equal to their length
difference. Installing `eval s e` at `h` establishes that fact's meaning;
admission additionally rules out over-applied or unavailable sources. The
intrinsic form starts with the key's full arity and each `fix` consumes one
remaining axis and a membership proof. Erasing it yields exactly the admitted
source forms.

A namespace is `(instanceId : Nat, incarnation : Nat)`. The selected structural
pairing is `pair a b = if a < b then b*b+a else a*a+a+b`, with inverse
`unpair`. Define:

```text
tag n    = pair n.instanceId n.incarnation
addr n i = pair (tag n) i
keyIn n k = (addr n k.origin, k.axes).
```

`addr n i = addr m j` exactly when `n = m` and `i = j`. Namespacing a fact
maps its key origin, handle and applied coordinates through these functions;
it preserves axes and remaining arity. Namespacing a query maps its key origin
and ordered point. An interpretation between a local and global state equates
every corresponding base, view and coordinate value. That relation transports
source evaluation, fact meaning and query values. Address injectivity by itself
supplies none of those value equations or native ownership laws.

## Reserved-name installation

An installation request contains a namespace `n`, source `e`, local handle
`h`, actual base function `b : List K → K`, fallback `z : K`, and captured
list `xs : List K`. Let:

```text
ids = map (addr n) (range (length xs))
local.challenge i = xs[i]?.getD z
local.base k = b
local.view h tail = z.
```

The request is admitted when `e` passes source admission against
`range (length xs)`. A successful patch of world `s`:

- sets the base at `keyIn n (key e)` to `b`;
- sets the view at `addr n h` to `eval local e`;
- sets each coordinate `addr n i`, for `i < length xs`, to the actual `xs[i]`;
- sets known coordinates to `ids ++ filter (fun i => i ∉ ids) s.known`.

All other entries retain their old meanings. The footprint is exactly the
selected base key, view handle and `ids`. The exported fact is the namespaced
source fact. Admission ensures that every prefix read is in range, so the
fallback cannot substitute for a missing admitted capture.

With natural capacity `cap`, execution succeeds exactly when the request is
admitted and `length xs ≤ cap`. It returns `true`, the patch, and event
`initialized n`. Failure returns `false`, the unchanged world and `rejected n`.
Success summarizes the footprint, exported fact and revealed `ids`; failure
has known empty writes and empty exports, revocations and reveals. These
summaries satisfy the preceding contract with precondition `True`.

This operation can replace an existing reserved name. It is not an allocator
and does not frame an external allocation registry. A fact in a different
namespace survives under its old meaning and the disjoint-address law. In the
same namespace, actual unaffectedness or a new meaning law is required.

## Monotone allocation and registration

The selected pool is `(next : Nat, issued : List Nat)` with:

```text
Good p ⇔ ∀ i ∈ p.issued, i < p.next
emptyPool = (0, [])
chosen p = (p.next, 0)
advance p = (p.next + 1, p.next :: p.issued).
```

Allocation first requires `length p.issued < quota`, then performs reserved-name
installation after replacing the request's namespace by `chosen p`. Successful
installation advances the pool and returns that allocated namespace. Failed
installation retains the pool and returns no name. Quota failure returns no
name, unchanged pool and world, and event `rejected (chosen p)`.

Every failure consumes no name in this mathematical allocator. `Good` is
preserved; at a good pool, `chosen p` differs from every issued incarnation-zero
namespace. There is no deallocation, natural-number wraparound or inferred
occupancy check against arbitrary imported worlds. A fresh empty pool can
therefore overwrite an unregistered name already present in a world.

Caller-visible names use `Names = Nat → Option Namespace`, with a new binding
pushed at position zero. Let `Facts = Nat → Option Fact`. Their soundness is:

```text
Sound facts names s ⇔ ∀ i f n,
  facts i = some f → names i = some n → Means s.values (factIn n f)

Registered p names ⇔ ∀ i n, names i = some n →
  n.incarnation = 0 ∧ n.instanceId ∈ p.issued.
```

Here `factIn` is the namespacing operation above. After successful allocation,
placing the new local fact at index zero and discarding older analysis facts
is sound without a global-freshness premise. Keeping the shifted older facts
additionally requires `Good p`, `Registered p names` and their prior `Sound`
relation. Registration and soundness are preserved for that successful push.
An imported name needs actual registry reconciliation to use this stronger law.

## Guarded caller compilation

The finite caller fragment has `end`, `demand q next`, and `call id yes no`.
Its compiled code adds a pure query plan to each demand. Here `end` denotes
normal return of `[]`. Module identifiers select the actual
implementation and specification. Queries collect values in order and do not
choose the next source command in this fragment; module results choose the
yes or no continuation.

The direct compiler selects the direct plan at every demand. The analyzed
compiler selects the inferred plan using current facts and abstract availability.
A demand leaves those contexts unchanged. Each module branch is compiled under
`nextFacts` and `nextKnown` for that branch's summary. Both source branches are
compiled; only the branch selected by the actual returned Boolean executes.

The interface operations are `demand(q,plan)` returning `K` and `external(id)`
returning `Bool`. A demand handler returns `runPlan` with unchanged world and
no event. An external handler returns the implementation's actual Boolean,
world and events. The caller embeds into common bodies as:

```text
embed end = done []
embed (demand q p next) = call (demand q p) (fun v =>
  (embed next).bind (fun values => done (v :: values)))
embed (call id yes no) = call (external id) (fun b =>
  if b then embed yes else embed no).
```

Guarded execution tests `Ready w.known q` at each actual demand before invoking
its underlying handler. A failed guard gives `(stopped refused, w, [])` at
that call; prior execution effects remain. External calls are passed through.
Both direct and inferred plans retain this same source-position guard. It
checks readiness, not arbitrary module preconditions or source authenticity.

For actual specifications `spec` and implementations `impl`, define applicability
recursively on the source and its actual world:

```text
CallsBeforeRefusal end s = True
CallsBeforeRefusal (demand q next) s =
  (Ready s.known q → CallsBeforeRefusal next s)
CallsBeforeRefusal (call id yes no) s =
  (spec id).pre s ∧
  let out = impl id s;
  CallsBeforeRefusal (if out.success then yes else no) out.world.
```

If every implementation satisfies its specification, initial facts are valid,
abstract availability is sound, and this applicability predicate holds, then
analyzed and direct guarded execution are exactly equal. No precondition is
imposed on a suffix never reached because of readiness refusal. This is a
semantic applicability predicate. Establishing it by a checker additionally
requires that checker's soundness law.

The stronger `Legal` predicate requires each reached demand to be ready in the
analysis's availability list and each reached module to satisfy its precondition,
updating availability through its actual result summary. `Legal` alone implies
the preceding applicability predicate. It implies actual enabledness when the
initial availability satisfies `Known` and every implementation satisfies its
specification. These premises connect analyzed availability to actual worlds;
validity of the initial factor facts is not required for enabledness.
Enabledness can justify guard erasure; its theorem does not cover an actually
refused caller.

### Typed factor rule

The typed transformation instantiates the
[common program](../../language/programs.md#language-signatures) with sorts
`scalar` and `boolean`, interpreted as `K` and `Bool`, respectively. The value
type `K` has decidable equality; the condition sort is `boolean`, interpreted
by the identity function. Source and target operations have these signatures:

| Source operation | Target operation | Lexical operand sorts | Result sort |
|---|---|---|---|
| `evaluate(q : Query)` | `evaluate(q : Query, p : Plan)` | `[]` | `scalar` |
| `external(id : Nat)` | `external(id : Nat)` | `[]` | `boolean` |
| `equal` | `equal` | `[scalar, scalar]` | `boolean` |

Here `Plan` is the pure query plan defined above. A query and module identifier
are operation descriptors, not lexical operands. Source evaluation invokes
`demand(q,direct)`; target evaluation invokes `demand(q,p)`. An external
operation invokes the named module. Equality returns the Boolean decision of
equality of its two operands without a state change or event. Both models use
the guarded handler defined above.

Fix module implementations `impl`, summaries `summaries : Nat → Bool → Summary`,
and an invariant `Inv : World K → Prop`. For every module identifier `id` and
state `s` satisfying `Inv s`, let `out = impl id s`. The rule requires:

```text
Justifies (summaries id out.success) s out.world
Inv out.world.
```

These laws concern each implementation's actual returned Boolean and world.
Let `rewrite(summaries,facts,available,source)` denote the typed rewrite.
Returns and stops retain their operands; equality retains its operands and
rewrites its suffix. A branch retains its condition and rewrites both arms
from the incoming facts and availability. Each evaluation selects
`infer facts available q` and rewrites its suffix under those same lists.
Demands retain their source-position readiness guards. External calls transfer
facts and availability separately for success and failure. Equal transfers
share one rewritten continuation; differing transfers produce a branch with the two
rewritten continuations. Loop bodies remain direct, and the suffix starts
with empty analysis facts and availability.

The rule has certificate type `Unit` and applies as:

```text
apply(source, ()) = some(lower(rewrite(summaries, [], [], source))).
```

Here `lower` is [direct logical-plan lowering](direct-plan.md#direct-lowering)
over the target language. The rule starts with empty analysis lists and
returns a plan for every well-typed source in this selected language.

Under the displayed module laws, the rule preserves complete execution from
equal source and target environments and states satisfying `Inv`. Empty
analysis facts do not require empty input storage. This invariant-based
applicability discipline differs from `CallsBeforeRefusal`; a readiness guard
does not establish the module laws. The resulting plan and actual candidate
are bound through [transformation checking](../../verification/refinement.md#checking-the-actual-candidate).

### Conservative typed factor rule

The conservative variant uses the same source/target languages, guarded handler,
module laws and invariant. It changes only the analysis after an external call.
Define `common(left,right)` by filtering `left` for members of `right`, retaining
the left list's order and multiplicity. For a call to `id`, its single suffix uses:

```text
facts' = common(nextFacts (summaries id true) facts,
                nextFacts (summaries id false) facts)
available' = common(nextKnown (summaries id true) available,
                    nextKnown (summaries id false) available).
```

If either incoming fact list is valid in a world, their common list is valid
there; the same implication holds for availability. Thus the actual outcome's
`Justifies` law establishes the merged assertions in the actual post-state.
The rule does not require the other outcome's summary to hold in that state.
These lists describe conjunctions of guaranteed assertions, so union would be
unsound. This merge is distinct from a union of possible phases.

The external call's actual Boolean, world and events are retained. No branch is
inserted to specialize its suffix. Original branches keep their conditions and
both arms; this variant does not recover outcome-specific assertions inside an
arm. Other cases follow the typed rule above, including direct loop bodies and
empty analysis lists at loop exit. Its `Unit` rule starts with empty lists and
binds the actual candidate through the same transformation checker. Under the
same module laws, it preserves complete execution for every admitted initial
environment and world, including source stops and readiness refusal.

For this rule, the erased output plan has exactly the input source's structural
node count. Count each return, stop, call, branch and loop constructor once,
including both branch arms and a loop's body and suffix without unrolling.
This measure excludes operand lists, operation descriptors, fact lists, numeric
encodings, certificate bytes and checking time. The result is not a total
compiler complexity bound. Losing an assertion selects direct evaluation when
no retained fact is eligible; semantic soundness does not establish usefulness.

## Immutable preparation and prices

Select an immutable total provider `p : KeyP → (V × Nat)` and decidable key
equality. The natural component is the declared preparation work. A cache maps
keys to optional value/work pairs and obeys the
[common validity law](../../core/contracts.md#immutable-cache-validity) for this
whole pair. Price functions `lookup(c,k)` and `insert(c,k)` are natural-valued
functions of the actual cache and key.

Acquisition has the following exact behavior, with `p k = (v,w)`:

| Mode and entry | Value | Resulting cache | Work | Saved work | Overhead |
|---|---|---|---|---|---|
| Direct | `v` | `c` | `w` | `0` | `0` |
| Memo, valid hit `(v,w)` | `v` | `c` | `0` | `w` | `lookup(c,k)` |
| Memo, miss | `v` | insert `(v,w)` at `k` | `w` | `0` | `lookup(c,k) + insert(c,k)` |

The returned value equals the provider's value, the resulting cache is valid,
and work plus saved work equals provider work. These laws require a valid
initial cache. They apply to immutable total acquisition; correlated-resource
consumption or effectful preparation needs a different operation contract.

A total preparation client is a well-founded tree of `done a`, `emit e next`
and `request k continuation`, whose continuation receives only the returned
value. Running it sequences acquisition and adds the three charges componentwise;
`done` has zero charges and `emit` only prefixes the visible event. The reference
evaluates the provider at each request, without cache bookkeeping. For a valid
cache, execution has the reference value and ordered visible trace and retains
cache validity. Starting both runs with an empty cache gives:

```text
memoWork + savedWork = directWork
memoWork + overhead ≤ directWork ⇔ overhead ≤ savedWork.
```

An embedded preparation handler records `visible e` or `charge(work,saved,overhead)`.
The protocol projection maps `visible e` to `[e]` and every charge to `[]`;
three separate charge projections sum the respective natural components.
Related caches are independently valid for the same provider; they need not
have equal contents. Common handler replacement then covers clients of this
interface, including adaptive requests and outer stops. The displayed exact
price theorem uses the total preparation client profile. Neither hiding charges
nor counting arithmetic establishes a native time or constant-time theorem.

## Concrete table preparation

The table provider uses immutable natural registers and syntax:

```text
TableExpr = lit Nat | reg Nat | add TableExpr TableExpr
          | mul TableExpr TableExpr | mod TableExpr Nat.
```

A literal or register read costs zero; a missing register has the explicitly
specified value zero. Addition and multiplication evaluate both children and
add one unit to their summed work. Remainder adds one unit to its child's
work and uses natural remainder, including `v % 0 = v`. Each instruction in
an ordered code list appends its evaluated value to the register list, and
execution sums instruction work. The result contains initial registers and
appended cells. This total internal interpreter differs from the
[partial input reader](../source/expressions.md#positional-inputs); its defaults do not
admit missing inputs in that reader or in a guarded factor demand.

A preparation key is `(version, origin, captures, code)`, with exact structural
equality. The provider executes `code` starting with the actual ordered
`captures`. Version and origin distinguish keys even where this reference
interpreter does not consult them to compute values. They do not dynamically
resolve a different provider meaning. The selected lookup and insertion prices
are one unit each.

For the bilinear natural instance, the key has version `1`, origin `o`, captures
`[a,b,c,d,x]` and two instructions computing `a+b*x` and `c+d*x` from those
registers. The exact provider result is:

```text
([a,b,c,d,x,a+b*x,c+d*x], 4).
```

Consumption at suffix `y` reads cells five and six and returns
`a+b*x+(c+d*x)*y = a+b*x+c*y+d*x*y`. The installed source fixes coordinate zero
of key `(o,[0,1])`, at local handle zero. Its installation captures are `[x,y]`,
and its base is the displayed polynomial on the first two input-list values,
using zero for absent positions in this total reference function.

The prepared table depends on the captured coefficients and `x`; it does not
depend on `y` or the runtime namespace. Installing that table under a selected
namespace gives the same view as the source-derived patch. Excluding `y` and
the namespace from this preparation key is justified by this equality, not
by treating all identities as interchangeable.

## Joined execution and observer

The joined instance has state `(world, cache)` and calls selecting either an
actual reserved-name bilinear installation or an ordinary contracted module.
Both direct and memo modes perform installation first. On success they acquire
the same immutable table key and install the resulting table view. On failure
they retain the installation's actual world/events, leave the cache unchanged
and charge no preparation, saved work or overhead. Ordinary module calls also
leave the cache unchanged and charge zero through this preparation interface.
The reference for logical equality is the source-derived installation or actual
ordinary module; the cost comparison's direct mode really materializes tables.

The visible event type distinguishes installation events from ordinary module
events. A joined external call emits its ordered visible events followed by a
charge event, including the zero charge on failure or an ordinary call. Pure
demands emit no preparation charge. The protocol observer erases charge events.
The comparison relation is:

```text
SameWorld (w,c) (v,d) ⇔ w = v ∧ ValidCache p c ∧ ValidCache p d.
```

For the same retained caller, call selection, captures and module interpretations,
the guarded analyzed memo execution is related to the guarded direct execution
under this relation and the protocol projection. The premises are the actual
module laws, valid initial cache and facts, sound abstract availability and
`CallsBeforeRefusal` for the reference calls. The initial comparison uses the
same actual world and valid cache; the final caches may differ. The relation
preserves complete outcomes, worlds and visible failure prefixes, including
refusal at an unready demand.

Fresh allocation with preparation is a separate adapter: acquisition follows
successful allocation and preserves its complete allocation result under the
table law. Admission, quota or capacity failure performs no preparation.
This adapter retains the allocator's registration and lifetime premises; a
reserved-name call in the joined interface does not reset or update a pool.

A client or observer inspecting hits, addresses, cache contents, timing or
charges requires a relation preserving those observations. Native memory and
performance claims additionally need their actual realization or measurements.
