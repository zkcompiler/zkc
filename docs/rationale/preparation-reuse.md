# A repeated preparation is removed by ordinary elimination before a table is considered

When the same immutable preparation is computed more than once, the compiler
first makes the repetition visible, for example by expanding the call that
hides it, and removes it as an ordinary repeated computation. The
[preparation law](../spec/core/contracts.md) permits every implementation below,
so the choice among them is a cost question.

## Alternatives

- **Pass the prepared value as an argument, or specialize on it.** Used where
  separate compilation would hide the repetition, keeping readiness, lifetime
  and the caller's binding.
- **A table keyed at execution time.** Used only when reuse depends on values
  not known until then and the preparation is expensive enough to pay for the
  table. A table has obligations of its own: its key contains every input the
  prepared value depends on, and its storage size, lifetime and any cost visible
  to an observer become part of the contract.

When repeated inputs are statically identical, ordinary elimination avoids the
additional storage, key comparison and lookup required by a runtime table.

## Reopen when

Reuse can only be discovered at execution time in a measured case, or the
storage cost of a table is repaid by the work it saves.
