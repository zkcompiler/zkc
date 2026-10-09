# Accumulator-machine relation adapter

This directory holds a small external machine, an imperative reference
interpreter for it, an exporter of its executions as
[relation-bundle](../../../docs/spec/domains/relation-bundles.md) carriers,
and two challenge-dependent interaction reductions emitted as
[staged programs](../../../docs/spec/domains/relation-bundles.md#staged-challenge-dependent-programs).
It is Python using only the standard library. The compiler and runtime neither
build nor recognize it: the Bundle is ordinary generic data, the reductions
read only its channel and interaction descriptors, and no protocol, opcode or
table name is special anywhere in zkc.

This is a narrow example of a multi-table machine relation. It is not a
general ISA, a RISC-V or Ethereum VM, or a VM proof. The checks below evaluate
reference semantics; they do not prove anything succinctly.

| File | Content |
|---|---|
| [`accumulator_machine.py`](accumulator_machine.py) | Instruction set, program validation, reference interpreter, row layout, Bundle and carrier builders |
| [`interaction_reductions.py`](interaction_reductions.py) | LogUp and grand-product staged transformations and their honest assignment builder |
| [`ring_arena.py`](ring_arena.py) | KoalaBear and Ext8 arithmetic, a `zkc.ring/0` builder and a reference arena evaluator |
| [`regenerate.py`](regenerate.py) | Fixture writer and byte-for-byte checker |
| [`fixtures/`](fixtures) | The Bundle, four staged programs and three executions |

## Use

From the repository root, with any Python 3.12 interpreter:

```sh
python3 compiler/adapters/accumulator-machine/regenerate.py check compiler/adapters/accumulator-machine/fixtures
python3 compiler/adapters/accumulator-machine/regenerate.py write NEW_DIRECTORY
```

`check` exits nonzero and names each file that is missing, extra or different;
`write` refuses an existing directory. The independent evaluation lives in
[`tests/protocol/test_machine_relations.py`](../../../tests/protocol/test_machine_relations.py),
part of `just test-integration`. It needs the compiler's
`test/zkc-relation_bundle_conformance-test` and the Rust
`relation_bundle_conformance` driver, and runs every carrier through both.

## The machine

The state is one KoalaBear accumulator, two memory cells, a pc and a clock.
Execution starts with the public initial accumulator, both cells zero and
`pc = clock = 0`. Each step executes the instruction at `pc` and advances `pc`
and `clock` by one; execution ends at the first Halt, whose accumulator is the
public result. All arithmetic is in KoalaBear, so AddImmediate wraps modulo
`p = 2^31 - 2^24 + 1`.

| Instruction | Opcode | Effect | Memory event `(clock, address, value, write)` |
|---|---|---|---|
| SetImmediate `k` | 1 | `acc' = k` | none |
| AddImmediate `k` | 2 | `acc' = acc + k` | none |
| Load `a` | 3 | `acc' = M[a]` | `(clock, a, M[a], 0)` |
| Store `a` | 4 | `M[a] = acc`, `acc' = acc` | `(clock, a, acc, 1)` |
| Halt | 5 | `acc' = acc`, stop | none |

A program is a list of 4, 8 or 16 instructions with operands below `p` and
Load/Store addresses in `{0, 1}`. Its first Halt must end an execution of
exactly 4, 8 or 16 steps. These are the CPU heights, so an execution is never
padded with rows the relation must ignore. A shorter computation is padded by
authored instructions, such as AddImmediate 0, which execute and are checked
like any other. Instructions after the first Halt are configured but
unreachable. The interpreter refuses other programs with `machine-program-length`,
`machine-program-halt`, `machine-execution-length`, `machine-opcode`,
`machine-operand` or `machine-address`.

The interpreter never evaluates the relation. The exporter lays its step
records out as rows; the Bundle is checked against them only by the two native
evaluators.

## The relation

The Bundle has public slots `initial-accumulator` and `final-result`, two
multiset channels with Boolean bounds, `program (pc, opcode, operand)` and
`memory (clock, address, value, write)`, and three finite tables over
KoalaBear:

| Table | Presence and height | Groups |
|---|---|---|
| `cpu` | required; instance height, power of two in [4, 16] | witness `state`: `pc, clock, opcode, operand, accumulator_before, accumulator_after, select_set, select_add, select_load, select_store, select_halt` |
| `program` | required; configured height, power of two in [4, 16] | configuration `instructions`: `pc, opcode, operand`; witness `use` |
| `memory` | optional; configured height, power of two in [8, 32] | configuration `schedule`: `clock, address`; witness `cells`: `before, after, event, write, value` |

Below, `x'` reads the next row, `transition` is the scope `interior(0, 1)`, and
an expression is asserted to be zero.

| `cpu` assertion | Scope | Expression |
|---|---|---|
| pc starts at zero | first | `pc` |
| clock starts at zero | first | `clock` |
| accumulator starts at the public initial value | first | `accumulator_before - initial` |
| pc advances | transition | `pc' - pc - 1` |
| clock advances | transition | `clock' - clock - 1` |
| accumulator carries to the next step | transition | `accumulator_before' - accumulator_after` |
| set, add, load and store selectors are Boolean | all | `s * (s - 1)`, four assertions |
| exactly one selector is active | all | sum of the five selectors `- 1` |
| opcode decodes the selectors | all | `opcode - sum(code * selector)` |
| set-immediate replaces the accumulator | all | `select_set * (after - operand)` |
| add-immediate adds the operand | all | `select_add * (after - before - operand)` |
| store keeps the accumulator | all | `select_store * (after - before)` |
| halt keeps the accumulator | all | `select_halt * (after - before)` |
| no halt before the last step | transition | `select_halt` |
| last step halts | last | `select_halt - 1` |
| final accumulator is the public result | last | `accumulator_after - final` |

The CPU pulls `(pc, opcode, operand)` from `program` with multiplicity 1 and
pushes `(clock, operand, select_load * after + select_store * before,
select_store)` to `memory` with multiplicity `select_load + select_store`.
Load has no CPU arithmetic rule: its result is the value of its memory event.

| `program` assertion | Scope | Expression |
|---|---|---|
| configured pc starts at zero | first | `pc` |
| configured pc advances | transition | `pc' - pc - 1` |
| use is Boolean | all | `use * (use - 1)` |

The program table pushes `(pc, opcode, operand)` with multiplicity `use`.

| `memory` assertion | Scope | Expression |
|---|---|---|
| schedule starts at clock zero | first | `clock` |
| schedule starts at address zero | first | `address` |
| schedule alternates addresses | transition | `address' + address - 1` |
| schedule advances the clock after address one | transition | `clock' - clock - address` |
| address zero starts at zero | first | `before` |
| address one starts at zero | first | `before` at offset 1 |
| cell state carries to the next clock | `interior(0, 2)` | `before` at offset 2 `- after` |
| event is Boolean | all | `event * (event - 1)` |
| write requires an event | all | `write * (1 - event)` |
| no write keeps the cell | all | `(1 - write) * (after - before)` |
| read returns the cell | all | `event * (1 - write) * (value - before)` |
| write stores the value | all | `write * (after - value)` |

The memory table pulls `(clock, address, value, write)` with multiplicity
`event`. The largest assertion degree is 3; interaction tuples have degree at
most 2.

### Choices

- **Program authority.** The configured `(pc, opcode, operand)` rows are the
  program. The pc assertions on configuration columns make pcs distinct and
  ordered, so a configuration cannot offer two instructions for one pc. The
  witness `use` is Boolean because this linear ISA visits each pc at most once.
- **Unused rows.** A configured row with `use = 0` contributes nothing. With
  an exact program only rows after the first Halt can be unused. The relation
  admits that slack: the statement concerns the execution through the first
  Halt.
- **Dense memory.** Row `2 * clock + address` holds one cell at one clock,
  before and after that clock's step. Each memory obligation has an explicit
  discharge. Ordering comes from the configured schedule, which is
  verifier-known data whose shape is asserted, so any other schedule is
  unsatisfiable rather than meaning something else; each cell carries its state
  to row `+2`. Initialization is the two first-row zero assertions. Address and
  clock ranges hold because events match only configured `(clock, address)`
  keys. The matching itself is the Bundle's Boolean multiset equality, which
  pairs each CPU event with the one row at its clock and address. A proof that
  replaces this equality with a staged reduction inherits that reduction's
  premises and error.
- **Heights.** The CPU height `n` is the instance's; the memory height is
  configured, normally `2n`. No Bundle relates two tables' heights. A longer
  schedule adds idle rows that keep state; a shorter one leaves later CPU events
  unmatched. Program length does not fix `n` either. The CPU must start at pc 0,
  advance by one and halt only on its last row. Together with the program
  lookup, this makes `n` the position of the first configured Halt plus one.
- **Presence.** The memory table may be absent. The whole-Bundle multiset
  equality then requires the CPU to have no memory events. A present table
  without events is also satisfiable.
- **Addresses.** No CPU assertion limits Load and Store addresses. A memory
  event matches only a row whose configured address is 0 or 1, so the range
  holds only together with the memory channel and schedule. The CPU table alone
  does not establish it.
- **pc and clock.** They are equal in this linear ISA. Both are kept because
  they play different roles: pc indexes the program channel and clock orders
  memory events. Both start at the constant 0 rather than at public slots; a
  machine split into segments would expose its starting pc and clock publicly.
- **Implied Booleans.** `select_halt` is pinned to 0 or 1 on every row by its
  transition and last-row assertions. A memory `write` flag is zero without an
  event and, with one, must equal the CPU's Boolean `select_store` through the
  memory channel. Neither has its own Boolean assertion. When a staged
  reduction replaces the memory channel, the write flag's Booleanity therefore
  holds only up to that reduction's error.
- **Multiplicity Booleans.** In the Bundle's own semantics, `use is Boolean`,
  `event is Boolean` and the CPU selector assertions coincide with the bound-1
  multiplicity range check. They exist because a proof of the assertions plus a
  staged reduction never checks that range. They discharge the reductions'
  Boolean premises; see below.

### Evidence

The integration test runs every carrier through both evaluators and requires
identical reports. Honest fixtures, slack and presence cases must hold. More
than forty mutations each name their exact failing assertion rows, unbalanced
channel tuples, range failures or refusal. Most are internally consistent
forgeries that only one assertion family catches. Examples are a Load decoded
from non-Boolean selectors without a memory read, an elided Store, execution
from the program's middle, past a Halt or jumping to it, a read from a later
clock, a cell aliased by a swapped schedule, and a repeated configured pc. The
test also requires every assertion and both channels to detect some mutation.
Height, authority and presence refusals use the native identifiers
`bundle-height`, `bundle-group-shape`, `bundle-height-authority`,
`bundle-table-missing` and `bundle-witness-presence`.

## Staged interaction reductions

`Reduction(kind, bundle, presence, challenge_field)` emits a one-phase staged
program that reduces every channel's interactions on present tables. Each
declared channel has two challenge slots in this order: the shift `gamma` and
the compression `delta`, both in `koala-bear.ext8-binomial3` unless the base
field is selected for a small example. A tuple of arity `k` has fingerprint

```text
fp(t) = t_0 + delta * t_1 + ... + delta^(k-1) * t_(k-1)
```

and each record's denominator or factor is `gamma - fp(t)`. Tuple and count
expressions are copied from the Bundle's arena, with reads rebound to phase 0
and explicitly embedded into the challenge field.

**LogUp** gives each record an inverse column `h` and each (table, channel) a
running sum `S`. With `m` a record's count and `s = +1` for push or
field-balance records and `-1` for pull records:

| Check | Scope | Expression |
|---|---|---|
| record inverts its denominator | the record's scope | `m * (h * (gamma - fp(t)) - 1)` |
| sum starts with the first row | first | `S - sum(s * m * h)` |
| sum accumulates each row | `interior(1, 0)` | `S - S_previous - sum(s * m * h)` |
| sum ends at its claim | last | `S - claim` |
| sums close (global) | | sum of the channel's claims |

The inverse check is gated by `m`. An active record must therefore have a
nonzero denominator, while an inactive row's free tuple values cannot cause a
spurious refusal. The ungated form `h * (gamma - fp(t)) - m` has one degree
less but leaves `h` free on an inactive row whose denominator is zero. Counting
each column read as degree 1 and challenges and claims as row constants, the
highest staged degree is 4. The CPU memory record reaches it in both
reductions, because its value coordinate has degree 2.

The **grand product** applies only to multiset channels. Each (table, channel,
side) has a running product `Z` of the factors `m * (gamma - fp(t)) + 1 - m`.
The checks are a first-row factor, an `interior(1, 0)` recurrence
`Z - Z_previous * factor`, and a last-row claim. Globally, the product of push
claims must equal the product of pull claims, and that push product times a
prover-sent inverse claim must equal 1. A zero factor makes the closing product
zero, so no inverse claim satisfies the predicate.

The honest builder refuses a zero active denominator or factor
(`reduction-zero-denominator`, `reduction-zero-factor`), a false Boolean count
premise (`reduction-boolean-count`), an instance whose presence differs from
the program's (`reduction-presence`), and a wrong number of challenges
(`reduction-challenge-count`). Tests turn off the zero and Boolean-count
refusals (`refuse_zero`, `check_premises`) to build the assignment a prover
would have to supply anyway, then show what the predicate decides.

### Premises and what the predicate does not establish

The [staged predicate](../../../docs/spec/domains/relation-bundles.md#staged-challenge-dependent-programs)
is a separate challenge-indexed predicate. No reduction theorem, challenge
distribution or error bound is stated or proved here. A satisfied staged
predicate for some challenges does not imply the Bundle's interactions hold.
Tuple compression can collide, and equality of sums or products at one point is
not an identity. The test shows this with memory compression `delta = 1`: a
forged Load at clock 3 returns 5, and memory records a read of 3 at clock 5.
The tuples `(3,1,5,0)` and `(5,1,3,0)` both have fingerprint 9. Both staged
predicates hold, while the Bundle's memory multiset fails. At the fixture
challenges, the same witness fails each predicate's global closure.

A field-weighted balance is not a natural multiset equality. LogUp checks a
field sum of counts, so it reaches the Bundle's multiset meaning only when every
multiplicity is a Boolean natural and each side's total count is below the
characteristic. The program records both conditions as premises:
`["boolean", 0, table, count, scope]` per record and
`["characteristic-exceeds", count_field, N]` per channel. `N` is the larger
side's sum over present records of maximum table height times bound. The
transformation refuses `N >= p` (`reduction-characteristic`). The grand product
records only the Boolean premises. Its factors are linear in the count, so
exponents are natural counts only for Boolean counts. The test's malformed
counts `2` and `p - 1` against one pull show the difference: they balance the
LogUp field sum while the Bundle reports range failures, and they fail the
grand product. Field-balance channels need no count premise for LogUp, and the
grand product refuses them (`reduction-channel-kind`).

Formation records premises but does not establish them. Here the Bundle's own
assertions discharge the Boolean premises: `use is Boolean`, `event is
Boolean`, and the constant CPU program count. The CPU memory count
`select_load + select_store` is Boolean from the selector Booleans and the
one-hot sum. A consumer composing a proof must keep those assertions and check
the characteristic bound; this adapter does not compose a proof.

### Presence, refusals and gaps

The program is instantiated for one presence vector: absent tables contribute
no columns and no claims. Staged global checks cannot observe presence. The
verifier must therefore select the program that matches the instance's
presence; this is a consumer obligation. The test evaluates the with-memory
program against an instance whose memory table is absent. The memory claim is
then free, the forged claim closes the sum, and the Bundle fails. The matching
without-memory program rejects the same CPU events.

| Refusal | Cause |
|---|---|
| `reduction-scope`, `reduction-locality` | An interaction whose scope is not `all`, or whose locality is local |
| `reduction-multiplicity-bound` | A multiset bound other than 1 |
| `reduction-channel-kind` | A grand product of a field-balance channel |
| `reduction-characteristic` | Count totals that could reach the characteristic |
| `reduction-presence`, `reduction-kind`, `reduction-field` | A required table marked absent, an unknown reduction or an unsupported challenge field |

A multiset bound above 1 is refused because a natural count `n <= B` needs an
in-relation range check and a premise stating that an output's canonical
representative is at most `B` over a scope. The staged format has no such
premise kind. That kind is the minimal missing piece. With it and a range
argument in the base relation, LogUp could reduce bounded natural
multiplicities. A machine with loops or branches could then use one program
row per pc with multiplicity up to its CPU height instead of Boolean `use`. The
grand product would instead need repeated rows or exponentiation of factors.

## Fixtures

[`fixtures/bundle.json`](fixtures/bundle.json) is the relation. The staged
programs `logup-with-memory.json`, `logup-without-memory.json`,
`grand-product-with-memory.json` and `grand-product-without-memory.json` are
instantiated per memory presence. Each execution directory holds:

| File | Content |
|---|---|
| `run.json` | `["zkc.accumulator-machine-run/0", [[mnemonic, operand], ...], initial_accumulator]`, decimals as strings |
| `bundle-configuration.json`, `bundle-instance.json`, `bundle-witness.json` | Bundle carriers of the reference execution |
| `logup-assignment.json`, `grand-product-assignment.json` | Staged assignments at fixed test challenges |

The fixed challenges come from `fixture_challenges`, which hashes the
directory and reduction names. They are reproducible test values, not
challenges drawn by any protocol transcript. The executions are:

| Directory | Steps | Memory | Initial, result |
|---|---|---|---|
| `store-load` | 16 | interleaved stores and loads, a read of an unwritten cell, a read after write, wraparound | 0, 108 |
| `store-load-initial-seven` | 16 | the same program | 7, 115 |
| `arithmetic-only` | 4 | none; the table is absent | 3, 12 |

## Limits

The machine has no branching, no word or overflow semantics beyond KoalaBear
arithmetic, two cells, no input or output beyond the two public slots, and no
segments, continuations, system calls or precompiles. The relation covers
these executions only. The reductions support global `all`-scope interactions
with Boolean multiset bounds or field-balance counts. Integrating this relation
and either reduction with a commitment, quotient and low-degree test, and
stating that protocol's security, are separate work.
