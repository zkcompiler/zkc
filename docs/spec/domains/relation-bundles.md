# Relation bundles

A relation bundle is a deterministic, multi-table relation
`R_config(instance, witness)`. It extends the
[finite arithmetic trace](constraints.md#finite-arithmetic-traces) with several
tables, explicit presence and height policies, column authority, signed finite
and cyclic windows and interaction records. Its expressions are
[shared ring expressions](ring-expressions.md) with closed input bindings. The
relation has no protocol randomness; challenge-dependent reductions are a
separate [staged program](#staged-challenge-dependent-programs).

A bundle defines a [relation family](../relations.md#relation-families-and-instances).
It does not select a domain, selector convention, quotient, commitment or proof
protocol; a [polynomial view](#polynomial-view-of-one-table) of one table
derives degree bounds under selected parameters without changing the relation.
Importing a bundle from an external system is a separate adequacy claim;
structural identity is not semantic equivalence.

## Compiler-visible table evaluation

Source captures a Bundle with `domain R = bundle(asset relation)` and can pass
it through generic `B: Bundle` parameters. A closed
`kernel<F, Table>("relation.table_rows", witness, configuration, public_data,
height; B)` evaluates one **present table's assertions**. `F` and `Table` are
installed field and natural binding arguments; the static asset parameter is
the Bundle's canonical SHA-256. The compiler retains the Bundle in the
[Entry package](../formats/entry.md). The Host independently admits its body
and preflights every reachable reference, including untaken branches.

All public slots and the selected table's groups and assertion results must
have field `F`. Needed arena nodes may also use its base field through explicit
embedding. This view does not promote base-field trace columns to extension
values. The native provider supports KoalaBear and Ext8; the relation carrier
itself remains independent of that provider.

Each vector concatenates groups of its authority in declaration order, with
each group stored row-major. `public_data` starts with all Bundle public slots,
followed by the selected table's public groups. If their aggregate widths are
`W`, `C`, `P`, and there are `S` public slots, the exact element counts at
height `h` are `h*W`, `h*C`, `S+h*P`. The result contains `h*A` elements,
row-major over the table's `A` assertions. An inactive assertion slot is zero;
an active slot evaluates its expression using the Bundle's closed bindings.
Reads and scopes are checked before arithmetic, including reads multiplied
by zero. Only active assertions' subexpressions are evaluated.

The height must meet the table's fixed or variable policy. The calling
protocol supplies a configured or instance height from the corresponding
authority, just as it supplies the three vectors. This kernel checks no
interaction records and does not decide optional presence or whole-Bundle
satisfaction. Those obligations remain with its consumer.

Refusals include `relation-table-index`, `relation-table-carrier`,
`relation-table-witness-shape`, `relation-table-configuration-shape`, and
`relation-table-public-shape`. The ordinary Bundle height, data, window and
scope bounds apply. Reference work `h*(nodes+inputs+assertions+1)` is at most
`2^26` for a nonempty assertion set; results are at most `2^20` elements and
`2^22` base coordinates. Native execution additionally checks its value/output
policy and charges `(h+1)*(nodes+inputs+assertions+1)` to the shared ring work
budget. Only one selected arena is retained during evaluation.

The immutable Host registry verifies the declared content identity and rejects
missing, duplicate or mismatched assets (`relation-asset-missing`,
`relation-asset-duplicate`, `relation-asset-identity`). Canonical text and
decoded metadata, including derived per-output read facts, share a 32 MiB
registry allowance (`relation-assets-bytes`). Named Entries combine this
allowance with their Ring assets.

## Polynomial view of one table

A polynomial view interprets one **present table** of an admitted Bundle under
the [finite-scope law](constraints.md#polynomial-interpretation-of-finite-scopes)
of the finite AIR: every column of every group denotes an interpolation
polynomial `T` of degree at most `trace_degree` over distinct domain points for
the rows, a read at signed offset `k` denotes `T(g^k X)`, and an assertion on
scope `S` requires its numerator to be divisible by the vanishing polynomial
`Z_S` of the scope's rows. Degrees weigh every read one and every public slot
zero, whatever the group's authority, exactly as the Bundle's facts do. For a
cyclic table the view adds a native wrap rule, stated below, that the finite
law and its formal model do not cover. The
native analysis is `analyzeBundlePolynomials` in
[`Relation/BundlePolynomial.h`](../../../compiler/include/zkc/Relation/BundlePolynomial.h).
Its parameters `height`, `domain_size` and `trace_degree` and their law
`1 <= height <= domain_size <= 2^24` and `domain_size - 1 <= trace_degree <=
2^24` are shared with the finite AIR analysis (`air-polynomial-height`,
`air-polynomial-domain-size`, `air-polynomial-trace-degree`).

From the Bundle's retained facts, without materializing any row, the view
derives:

- every group's exact width, authority and field, with the sorted distinct
  offsets its active assertions read;
- the ordered binding list of the table arena, one entry per arena input.
  Evaluating only active outputs requests exactly the bindings whose read or
  public slot appears in the subject lists below; the others are never read;
- the sorted distinct `(group, offset, column)` reads and the sorted public
  slots of active assertions: the opening subjects, with their signed shifts;
- per assertion its output, scope, read degree `d`, active rows `[begin, end)`
  at the height, selector degree `domain_size - |S|`, numerator degree
  `d * trace_degree`, and quotient degree `d * trace_degree - |S|` exactly
  when the numerator degree reaches `|S|`; otherwise an exactly divisible
  numerator must be zero. An empty scope is inactive: it imposes no quotient
  and contributes no subject. The complement form
  `numerator + selector - domain_size` agrees with the quotient degree;
- the largest quotient degree over active assertions and the number of
  coefficient blocks of length `domain_size` sufficient for each individual
  active quotient, `floor(quotient_degree / domain_size) + 1`, and hence for
  any linear combination of them. The count is zero when no active assertion
  has a quotient. This is not a soundness claim about random assertion
  batching;
- the identity of the table arena. The arena itself stays borrowed from the
  admitted Bundle: `bundlePolynomialArena` re-derives it and refuses a view of
  another bundle or table (`bundle-polynomial-relation`).

The **carrier admission** (`admitBundlePolynomialCarrier`) requires every
Bundle public slot, every group of the table and every arena node an assertion
needs to have the carrier field or, for an extension carrier, its base field,
which is then interpreted in the extension (`relation-table-index`,
`relation-table-carrier`). An extension field is never narrowed, and outputs
used only by interactions are not visited. The analysis admits any presented
field; unlike the actual-row view of `relation.table_rows`, which keeps exact
declared fields, it lets a KoalaBear table be analyzed in Ext8. A view records
the carrier and its base coordinates; each group keeps its declared field.

Checks run in this order: the carrier admission, the parameter law, the
table's height policy (`bundle-height`), the domain rule, and every assertion
window at the height (`bundle-scope-height`, `bundle-window`). A finite read is defined only on its scope, so the shifted
polynomial realizes it only there; a finite table may pad its domain beyond
its height, which never adds active rows. A cyclic read wraps in the height
domain, which `T(g^k X)` realizes on every row only when the row points are
the whole subgroup of order `height`. A cyclic table therefore requires
`domain_size = height`, a power of two at least 2 that the carrier's prime
subfield admits as the order of a two-adic root (`bundle-polynomial-domain`).
An unsupported domain or embedding refuses; nothing is reinterpreted silently.

The selected initial profile is **two-adic natural**: `height = domain_size =
n` for a power of two `n >= 2`, `trace_degree = n - 1`, and row `i` at the
`i`-th power of the installed two-adic root of order `n`
(`twoAdicPolynomialParameters`, `bundle-polynomial-two-adic`). A view has this
profile only when its carrier installs that root. Under it the
selectors of `first`, `last` and `interior(0, 1)` have degrees `n - 1`,
`n - 1` and `1`, the unnormalized complementary vanishing polynomials. Any
other checked parameters are the general profile, which a later library may
restrict; `interval` scopes are analyzed, but a verifier's evaluation of their
vanishing polynomial is linear in the scope.

The deterministic `zkc.relation-bundle-polynomial-analysis/0` encoding records
these facts for adapters and source clients. A view of an optional table
applies only when the instance makes it present. The view establishes no
whole-Bundle interaction, presence, satisfaction, commitment, batching or
proof claim. On a finite table, per-assertion divisibility is the
[per-constraint law](constraints.md#polynomial-interpretation-of-finite-scopes)
with its formal model. The cyclic wrap rule has no Lean model; its evidence is
the bounded coefficient check of the recurrence fixture recorded in the
[native validation map](../../../tests/native.md).

## Compiler-visible polynomial view

Five kernels describe one present table to a source library that constructs
its own polynomial protocol. Each has roots `<F, Table>` like
`relation.table_rows`, the same Bundle asset parameter, and the installed
KoalaBear or Ext8 provider. They derive facts from the admitted Bundle and
substitute its existing arena. They select no domain shift, challenge,
quotient combination, commitment or proof, and they check no interaction.

| Contract | Data operands | Results |
|---|---|---|
| `relation.table_shape<F, Table>` | `height` | `(witness_width, config_width, public_width, public_slots, inputs, assertions, quotient_chunks)` |
| `relation.table_input<F, Table>` | `height`, `input` | `(kind, column, rotation)` |
| `relation.table_scope<F, Table>` | `height`, `assertion` | `(begin, end)` |
| `relation.table_point<F, Table>` | one value per arena input | one value per assertion, in assertion order |
| `relation.table_points<F, Table>` | `rows` row-major assignments, `rows` | `rows` row-major results, one column per assertion |

**Domain.** A table of height `h` is interpreted on the multiplicative
subgroup of order `h`: row `r` is `g^r` for a generator `g`, and each column
polynomial has degree at most `h - 1`. The height must be a power of two of
at least 2 (`bundle-polynomial-two-adic`) and must meet the table's policy
(`bundle-height`). As for `relation.table_rows`, the calling protocol supplies
a configured or instance height from that authority. A read at signed offset
`o` is the shifted polynomial `T(g^o X)`. Because `g` has order `h`, this is
exactly a cyclic read. A finite read agrees with it on every row where its
window is defined. Every assertion's window is checked at the height
(`bundle-scope-height`, `bundle-window`). A domain larger than the height is
not this view.

**Shape.** Widths sum the element widths of each authority's groups.
Each authority forms one combined matrix, row-major over the sum of its group
widths in declaration order. Column `c` of group `g` is combined column
`offset_g + c`, where `offset_g` sums the widths of earlier groups of the same
authority. This layout deliberately differs from `relation.table_rows`, whose
operands concatenate each group's own row-major array. A source adapter owns
any packing between the two. `public_slots` counts every Bundle public slot;
`inputs` and `assertions` count the arena inputs and the table's assertions.

`quotient_chunks` counts chunks of length `h`. Suppose an assertion has derived
degree `d` and a nonempty set `A` of active rows. Its interpretation has degree
at most `d(h-1)`. When `d(h-1) >= |A|`, its quotient by `Z_A` has degree at
most `d(h-1) - |A|` and fits in `floor((d(h-1) - |A|) / h) + 1` chunks.
Otherwise exact divisibility forces the interpretation to be zero
([finite scopes](constraints.md#polynomial-interpretation-of-finite-scopes)).
The result is the maximum over assertions and at least 1, including for a
table without assertions: exactly `max(1, quotient_chunks)` of the
[analysis](#polynomial-view-of-one-table) at `twoAdicPolynomialParameters(h)`,
whose zero means that no active assertion has a quotient. A fixture shared by
the native analysis and backend tests pins this relation. It bounds each
quotient and therefore any fixed linear combination; it is not a claim about
random batching.

The shape also bounds three quantities. The table's declared data at this
height, together with every public slot, is at most `2^22` base coordinates
(`bundle-data-limit`). When there are assertions,
`h * (nodes + inputs + assertions + 1)` is at most `2^26`
(`bundle-work-limit`). `quotient_chunks * h` is at most `2^24`
(`bundle-polynomial-limit`). The checks run in this order: two-adic height,
height policy, windows, data, work and quotient size.
`relation.table_input` and `relation.table_scope` apply the same checks at
their height before they read an index.

**Inputs.** There is one descriptor per ordered arena input
(`relation-table-input-index`). Kind 0 is a Bundle public slot, with `column`
equal to the slot and `rotation` 0. Kinds 1, 2 and 3 are witness,
configuration and public-group reads. A read's `column` is in the combined
matrix of its authority, and `rotation` is its signed offset reduced modulo
`h`: offset `-1` at height 8 is rotation 7.

**Scopes.** `relation.table_scope` returns the active rows `[begin, end)` of
an assertion's scope, as in [rows and windows](#rows-and-windows). An empty
interior scope is `(0, 0)`; an empty interval keeps its start
(`relation-table-assertion-index`).

**Points.** `relation.table_point` takes exactly one value per arena input
(`relation-table-point-shape`). It substitutes them through the shared ring
substitution and returns the assertion outputs in assertion order, repeating
an output that two assertions share. It applies no row mask, selector,
vanishing polynomial or division, and it claims no satisfaction. Under an
Ext8 carrier a KoalaBear table is interpreted in Ext8: inputs, constants and
operations lift to the extension, substitution points may be any extension
values and results keep every coordinate. An Ext8 table admits only its Ext8
carrier; nothing is narrowed or coerced from another field.

`relation.table_points` applies the same substitution to `rows` assignments
at once. Its first operand is row-major with one column per arena input; its
result is row-major with one column per assertion, in assertion order. One row
is exactly `relation.table_point`. Rows, inputs and assertions may each be
zero; a length other than `rows * inputs` is `relation-table-point-shape`.
Like `relation.table_point`, it selects no domain: the caller chooses the
points, for example a coset of a larger domain, and applies any selector or
division itself.

**Carrier and interactions.** The analysis's carrier admission applies with
carrier `F` (`relation-table-carrier`). An output used only by interactions is
neither checked nor evaluated. An input it alone uses keeps its descriptor
and its column; the point substitutions ignore its value. The kernels claim
nothing about interactions, presence or whole-Bundle satisfaction; a consumer
must exclude or separately discharge them.

When a body closes, the compiler checks the carrier admission and that the
height policy admits a power of two `n >= 2` whose root of order `n` the
carrier installs. Table and height failures report `source.asset-table`;
carrier failures report `source.asset-carrier`. This rule names a capability,
not a provider: only the installed KoalaBear and Ext8 providers implement the
kernels. The Host independently checks the same premises once per reachable
asset, table and carrier before execution, without allocating.
Height-dependent checks happen during execution.

Every invocation first repeats the allocation-free static check, which visits
at most the public slots, groups and assertions it charges for. Shape, input
and scope then charge
`W = nodes + inputs + groups + public slots + assertions + assertion reads + 1`
units to the shared ring work budget before their height profile, where
assertion reads count the derived read facts of each assertion's output.
`relation.table_point` charges `W + U` with
`U = nodes + inputs + assertions + 1`, and `relation.table_points` charges
`W + rows * U`, as one charge. Before it, a point substitution checks its shape, its result against the element and
value policy and the invocation's output allowance, and the result together
with node scratch and the prepared assertion sub-DAG against the value policy.
The sub-DAG is bounded by its arena's admission charge plus 32 bytes per
assertion. It is prepared only after the charge, once per invocation and
shared by every row; nothing is retained between invocations. No charge or
allocation grows with the height. The result and scratch elements of one batch share the
[element ceiling](../runtime/capacity.md), 65,536 by default, so a large
evaluation domain may need several calls.

## Carrier

The exact array form is:

```text
["zkc.relation-bundle/0", publics, channels, tables]
publics  = [[name, field], ...]
channels = [[name, kind, [tuple_field, ...], count_field], ...]
kind     = "field-balance" | "multiset"
table    = [name, presence, height, read_model, groups, arena, inputs,
            assertions, interactions]
presence = "required" | "optional"
height   = ["fixed", h] | ["config", min, max, power_of_two]
         | ["instance", min, max, power_of_two]
read_model = "finite" | "cyclic"
group    = [name, authority, field, width]
authority = "witness" | "config" | "public"
arena    = a zkc.ring/0 expression
input    = ["public", public_index] | ["read", group_index, signed_offset, column]
assertion = [output_position, scope]
scope    = ["all"] | ["first"] | ["last"] | ["interior", left, right]
         | ["interval", start, stop]
interaction =
    ["field-balance", channel, locality, scope, [tuple_position, ...],
     count_position, declared_count_bound_or_null]
  | ["multiset", channel, locality, scope, side, [tuple_position, ...],
     multiplicity_position, bound]
locality = ["global"] | ["local", key]
side     = "push" | "pull"
```

Every reference is a position: public slots, channels, groups, columns, arena
outputs and local keys. Names identify objects in diagnostics and must be unique
within publics, channels, tables and the groups of one table; they are 1–128
bytes without control characters. A signed offset is a canonical signed decimal
string such as `"0"`, `"1"` or `"-1"`, with magnitude at most 65,536. Every
other number is a canonical JSON natural. Unknown tags, wrong arities and any
other input kind, including a challenge, received claim or selector, are
refused. The structural identity is SHA-256 of the canonical compact encoding.

## Formation

Fields must be installed. Public slots and groups additionally need an element
encoding: a prime field element is one canonical decimal residue; an element of
`koala-bear.ext8-binomial3` is eight base residues in the ascending basis of its
[presentation](values.md#nominal-field-extensions).

Each table has one arena whose ordered outputs are its checks' expressions. The
table's `inputs` list binds every arena input, in order, to a public slot or to a
same-table read; the binding's field must equal the ring input's field. Reads in
another table do not exist: cross-table equality is expressed by interactions,
so tables of different heights never read each other's rows. Every binding is
used by some output, no two inputs have the same binding, and every output is
referenced by an assertion or interaction.

Heights satisfy `1 <= min <= max <= 2^20`; a fixed height `h` is `min = max = h`;
`power_of_two` requires a power of two in `[min, max]`. A table with a `config`
group has a `fixed` or `config` height, because its configuration data has a
known height. Width is between 1 and 65,536.

An interaction's record kind equals its channel's kind. Its tuple has the
channel's arity, each tuple output has the channel's tuple field, and its count
or multiplicity output has the channel's count field. A multiset count field is
a prime field, and its `bound` satisfies `1 <= bound < characteristic` and
`bound <= 2^32 - 1`. A field-balance record may carry a declared count bound
from its source; it is a recorded premise, part of the structural identity and
not part of satisfaction.

Analysis facts per output are its field, its read set `(group, offset, column)`,
its public slots and its degree under weights 0 for public slots and 1 for every
read. Configuration and public columns are not degree zero: their polynomial
interpretations are not constants.

## Supplied data

Three carriers supply the data, each naming the bundle identity:

```text
["zkc.relation-configuration/0", relation, [[height_or_null, [config_group, ...]], ...]]
["zkc.relation-instance/0", relation, [public_value, ...],
  [["absent"] | ["present", height_or_null, [public_group, ...]], ...]]
["zkc.relation-witness/0", relation, [null | [witness_group, ...], ...]]
```

Group values are row-major element lists of length `height * width`. A height
appears exactly where its table's height authority names that carrier. Each
carrier lists only the groups it has authority over, in group order: the
witness cannot supply configuration or public columns, the instance cannot
override a fixed or configured height or configuration column, and the
configuration cannot choose an instance height.

Presence is chosen by the instance. A required table cannot be absent. An
absent optional table has no height, no public or witness data, and the value
`null` in the witness; a present table has witness data. Configuration data of
an absent table is still admitted but contributes no rows.

## Rows and windows

A present table of height `h` has rows `0 .. h-1`. Each scope is a contiguous
row range:

| Scope | Rows |
|---|---|
| `all` | `[0, h)` |
| `first` | `{0}` |
| `last` | `{h-1}` |
| `interior(l, r)` | `[l, h-r)`, empty when `l + r >= h` |
| `interval(s, e)` | `[s, e)` with `s <= e`; defined only when `e <= h` |

A read at offset `o` on row `i` denotes row `i+o` in a finite table, which must
satisfy `0 <= i+o < h`, and row `(i+o) mod h` in a cyclic table. Definedness is
a property of the syntax: every read used by a check's outputs must be defined
on every row of its scope. Admission checks it before evaluating anything, so an
algebraic cancellation such as `0 * read` cannot hide an undefined read.

A finite window that is undefined at every height refuses at formation: an
`all` read with nonzero offset, a `first` read with negative offset, a `last`
read with positive offset, an `interior(l, r)` read with `l + o < 0` or `o > r`,
and an `interval(s, e)` read with `s + o < 0`. The remaining conditions depend
on the instance's height and refuse at admission. An interval beyond the table
also refuses at admission.

## Satisfaction

The relation holds for a configuration, instance and witness exactly when:

1. the data are admitted as above;
2. every assertion's output is zero on every row of its scope;
3. every field-weighted balance holds;
4. every multiplicity is in range and every multiset balance holds.

Assertions and interactions of an absent table impose nothing.

### Field-weighted balance

Each active row of a field-balance interaction contributes its count value at
the key `(channel, scope_key, tuple)`, where `scope_key` is global or the pair
`(table, local key)`. The balance holds when, for every key, the sum of its
counts is zero in the count field. Local keys of different tables or keys never
cancel each other. Counts are field elements: `p-1` and `1` cancel. No sign,
direction or natural interpretation is assigned to a count.

### Natural multiset equality

Each active row of a multiset interaction contributes its multiplicity value
`v` to its side at the same kind of key. The multiplicity denotes the canonical
natural representative `n` of `v`, and the row requires `n <= bound`. An
out-of-range multiplicity makes the relation false; it is not reinterpreted, so
`p-1` is never `-1`. The balance holds when, for every key, the natural sum of
pushes equals the natural sum of pulls.

A field-weighted balance does not imply a multiset equality. Deriving one
requires a separately justified count-lifting argument with its own bounds and
role evidence. An exclusive group of interactions denotes its expanded
contributions; a compressed challenge-dependent form belongs in a staged
program, with its Boolean and at-most-one premises recorded.

## Staged challenge-dependent programs

A staged program references a bundle and denotes a separate challenge-indexed
predicate over the bundle's data:

```text
["zkc.relation-staged/0", relation, phases, global, premises]
phase    = [challenges, claims, tables]
challenges, claims = [[name, field], ...]
table    = [groups, arena, inputs, assertions]       (one per bundle table)
groups   = [[name, field, width], ...]
input    = ["public", i] | ["read", phase, group, signed_offset, column]
         | ["challenge", phase, index] | ["claim", phase, index]
global   = [arena, inputs, [output_position, ...]]
premise  = ["boolean", phase, table, output, scope]
         | ["at-most-one", phase, table, [output, ...], scope]
         | ["nonzero", phase, table, output, scope]
         | ["characteristic-exceeds", field, natural]
```

Phases are numbered from 1; read phase 0 is the bundle's own groups. In phase
`j` the verifier's challenges are drawn first, then the prover commits the
phase's groups and sends its claims. A table or global input of phase `j` uses
only challenges, claims and groups of phases `<= j`. Global checks use public
slots, challenges and claims, never reads. Formation, windows, unused bindings
and outputs follow the bundle rules; an output may also be the subject of a
premise. Its assignment carrier is:

```text
["zkc.relation-staged-assignment/0", program_identity,
  [[challenge_values, claim_values, [null | [group_values, ...], ...]], ...]]
```

Each phase entry has one value per challenge and claim slot and, per table,
`null` exactly when the base table is absent, otherwise the phase's groups at
the table's admitted height. Staged reads use the base table's read model.

The staged predicate holds when the base data are admitted, every staged
assertion is zero on its scope and every global output is zero, for the
supplied actual challenge and claim values. It contains none of the bundle's own
assertions or interactions and does not change their meaning. Premises are
recorded assumptions: they are not part of the predicate, and no relation
between the staged predicate and the bundle follows from a program alone. Such a
relation requires a separately stated reduction with its premises, challenge
distribution and error bound.

Formation checks premise references and their shape, but does not establish
their truth or read definedness. This includes characteristic inequalities
against installed fields and the scope of a premise-only output. A reduction
consumer must discharge these obligations explicitly before using them.

## Finite AIR embedding

A [finite AIR](constraints.md#finite-arithmetic-traces) over field `F` with `c`
columns and `p` public values is the bundle with public slots `0 .. p-1`, no
channels, and one required finite table: height chosen by the instance in
`[1, 65536]`, one witness group of width `c` (none when `c = 0`), and one
assertion per constraint in order. Scopes map as every → `all`, first →
`first`, last → `last` and transition `k` → `interior(0, k)`; a public input
becomes a public binding, `read(o, c)` becomes `["read", 0, "o", c]`, and
negation remains ring negation. For every height in that range, the embedded
bundle holds exactly when the AIR relation holds. An AIR whose window is
undefined at every height has no satisfying trace; its embedding refuses at
formation.

## Limits

Formation bounds analysis before building output facts or checking each finite
window (`bundle-analysis-limit`). For an arena with `N` nodes, `I` inputs,
`O` outputs, and `R` output references in assertions and interactions, a base
table charges `(O + R + 1) * (N + I + 1)` work and `O * I` retained input facts.
The totals across the bundle must not exceed 2^26 work and 2^22 input facts.
Staged tables and the global arena have a separate cumulative work budget of
2^26, charging `(R + 1) * (N + I + 1)` each; staged `R` includes valid output
references from recorded premises. They do not retain per-output input facts.
These conservative shape bounds apply even to cyclic reads and repeated roots;
they prevent compact schemas from expanding into unbounded analysis metadata.

A bundle or staged program is at most 8 MiB of canonical text with at most 256
tables, 256 groups per table, 65,536 public slots, 4,096 channels, tuple arity
64, local keys in [0,4096], and 4,096 checks per table. Each supplied data carrier
is at most 256 MiB of text. The base data have a combined budget of 2^22 base
coordinates, including public slots; the staged assignment has a separate
budget of 2^22 across all phases, including challenges and claims. Admission
computes these totals from declared slots, heights, widths and element degrees
before comparing group lengths.
Before any value is parsed, admission also bounds
the reference evaluation work, `height * (arena nodes + inputs + checks + 1)`
summed over tables with checks, by 2^26, and the number of interaction
contributions by 2^22. Staged programs have at most 16 phases and 4,096
challenge and claim slots per phase and at most 4,096 recorded premises.
Challenge and claim names are unique across all phases. For each table, staged
group names are unique across all phases and against its base group names.

Before reference evaluation, admission also bounds materialized results by
2^20 records and 2^22 base coordinates (`bundle-result-limit`). Each scoped
assertion row contributes one residual record and its output field degree in
coordinates. Each scoped interaction row is conservatively counted as one
distinct balance record, with all tuple coordinates and its count field's
degree; equal keys and zero weights do not reduce this preflight charge.
Staged evaluation counts assertion rows across all phases and global assertions
against one such budget. These bounds apply separately to the deterministic
and staged predicates. At each table, the existing work and contribution
limits are checked before the result limits.

Embedded arenas retain the `ring-*` refusal identifiers of the
[ring contract](ring-expressions.md), including `ring-degree` for a bundle's
weighted degree. Staged assignments reuse bundle value, group, window, scope
and resource identifiers; challenge/claim list shape uses `staged-slot-shape`
in both the reader and evaluator.

[`Zkc.Relation.Bundle`](../../../formal/Zkc/Relation/Bundle.lean) is the
independent formal denotation. The
[correspondence map](../../../formal/docs/correspondence/domains.md#relation-domain-foundation)
states its theorem scope; it is not a proof of the native admission or
evaluation code.
