# Design rationale

These records explain consequential choices in the current implementation:
the alternatives, the reason for choosing, and the cost that remains.
[Architecture](../architecture.md) describes the system;
[specification](../spec/README.md) owns its contracts.

| Question | Record |
|---|---|
| Why separate the MLIR compiler, Rust runtime and Lean models? | [System boundaries](architecture.md) |
| Why keep mathematics in ordinary SSA? | [Mathematical IR](mathematical-ir.md) |
| Why check actual transformation results? | [Validation](validation.md) |
| Why must projection preserve explicit communication? | [Participant generation](participant-generation.md) |
| Why use sequences alongside numeric tensors? | [Nested data](nested-sequences.md) |
| Why distinguish artifact identity, live resources and authority? | [Identity](identity-purposes.md) |

## Keep a record only when it helps

A separate record is useful when a reader could reasonably choose differently
and the reason needs more than a paragraph beside the definition. Combine choices
that answer the same question. Keep short reasons with their owning guide or
specification; independent Lean model choices belong with
[formal design](../../formal/docs/README.md#design-and-tools).

Explain the actual tradeoff with an example or a concrete cost. Link to the
owning contract and from the page where readers encounter the choice. Use only
the headings the explanation needs. There is no fixed length or mandatory
reopening section; include a condition for revisiting a choice when it is useful.

Keep normative definitions, support inventories and plans in their owners.
Review history, internal work labels and superseded reasoning stay outside the
public reference. Rewrite or remove a record when the choice changes.

The [documentation checker](../../tests/check_docs.py) checks links to and from
the owner and flags common process metadata. Editorial review checks whether a
record adds an explanation rather than repeating the contract. Follow the
[documentation guide](../development/documentation.md) when consolidating pages.
