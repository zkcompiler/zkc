# Gap Ledger

This ledger records every known gap between what [the specification](spec/)
describes and what the checkout builds. The specification is never weakened to
close a gap: either the build closes it, or the specification changes through
its own change process, and in both cases the entry is removed.
[Current Status](status.md) states what the checkout claims today; this page
states where that claim falls short of the specification.

An entry names the specification section, the current behaviour, the check or
note that measures the difference, and the change that closes it. The research
program's open items, the findings a package could not answer and the
reopening records of the design notes, are indexed by the `checks.open-items`
control-plane check and are not specification gaps until a specification
section adopts the design they concern.

| Specification | Current behaviour | Measured by | Closes with |
|---|---|---|---|

No entry is recorded at this checkout.
