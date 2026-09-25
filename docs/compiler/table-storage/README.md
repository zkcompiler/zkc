# Table source and storage design

This package selects the first concrete field-table language, its direct execution plan and native storage/API obligations. It
instantiates the common source and execution model without changing their
definitions. [Source operations](source.md) specify actual values and complete
behavior; [storage and APIs](storage.md) specify the native representation and
admission boundary.

The central choice is an immutable original table and a residual carrying an
ordered prefix. A residual's type retains its **original** dimension; its value
tracks how many coordinates have been fixed. This permits ordinary bounded
loops to grow a prefix while retaining one accumulator type. Shape violations
have explicit logical refusal behavior. Native capacity refusal occurs before
execution and has a separate result.

This is a selected engineering instance under the existing
[domain specification](../../spec/domains/polynomials.md),
[typed program specification](../../spec/language/programs.md) and
[realization specification](../../spec/realization/representations.md).
It is not a new common calculus. Operation names in this package are local
semantic constructors; the [native table path](../table-execution.md) implements
registered spellings and validates them with its consumer.

## Pages and clients

| Page | Concrete content |
|---|---|
| [Source design](source.md) | Sorts, public specialization, exact input formation, restriction/evaluation, ordered non-field kernel, mutable calls, loops and direct checking |
| [Protocol traces](protocols.md) | Complete one-variable Sumcheck trace, actual original-table terminal and ordered two-level Merkle path |
| [Storage design](storage.md) | Ownership, value/state relation, immutable alias frame, capacity recurrence, failure layers and API transitions |
| [Model.lean](Model.lean) | Actual generic source/plan client over `ZMod 2` and `ZMod 7`; original-cell and ordered-prefix laws; complete failure controls |
| [Storage.lean](Storage.lean) | Abstract live, stale and foreign handle resolution, with a law preserving surviving aliases |

Run the two Lean clients from the repository root with the maintained Formal
dependencies installed:

```sh
cd formal
lake env lean ../docs/compiler/table-storage/Model.lean
lake env lean ../docs/compiler/table-storage/Storage.lean
```

Both clients audit their locally elaborated declarations and transitive
axioms. They allow only `propext`, `Classical.choice` and `Quot.sound`; a missing
proof or an evaluation oracle cannot establish their results. These standalone
clients stay in this package so their design evidence does not silently become
an exported Formal or native API; reusable definitions move to their maintained
homes as an actual consumer needs them.

Direct execution connects the same operations and values through decoding, MLIR,
checking and owned Rust execution. This package supplies design and Lean
evidence, not that native correspondence or the shared optimization.
