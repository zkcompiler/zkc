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
protocol. Importing a bundle from an external system is a separate adequacy
claim; structural identity is not semantic equivalence.

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
