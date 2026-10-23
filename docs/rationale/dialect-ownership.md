# Dialect ownership

A dialect groups meanings and their invariants. A compilation profile selects
which combinations of operations and types are admitted; it need not give every
operation a new name. The [physical selection contract](../compiler/representation.md)
and [executable format](../spec/formats/program.md) apply that distinction.

## Reuse structure and retain meaning

MLIR supports [mixed dialects](https://mlir.llvm.org/docs/LangRef/#dialects),
[interfaces](https://mlir.llvm.org/docs/Interfaces/) and explicit
[conversion legality](https://mlir.llvm.org/docs/DialectConversion/).
zkc already uses standard functions, scalar arithmetic and structured control
inside mathematical regions. A new namespace is not needed to reserve a backend
or reproduce an upstream operation. Interfaces describe an operation's existing
meaning; they do not grant a new meaning to an upstream operation.

The current ownership boundaries are:

| Owner | Meaning retained by zkc |
|---|---|
| Entry | Application selection, data binding and invocation |
| Protocol | Roles, messages, observations and ordered participant behavior |
| Relation | Relation declarations and constraints |
| Data | Nominal data, finite domains, checked observations and structured values |
| Algebra | Nominal field/group mathematics and admitted numerical expressions |
| Polynomial | Formal polynomials, multilinear tables and domain operations |
| Crypto | Cryptographic construction and encoding contracts |
| Oracle | Oracle and query contracts |
| PCS | Commitment contracts and their nominal values |
| Kernel | Closed mathematical subjects and ordered invocation |
| Local | Reached execution, early stopping, checked control and resources |
| Plan | Selected physical representations, installed calls and releases |

A coefficient array does not make a formal polynomial, a multilinear table and
a quotient-ring element interchangeable. Similarly, a `local.for` has checked
bounds, iteration limits and early termination in addition to loop structure.
Replacing it with `scf.for` requires representing those obligations explicitly;
renaming it would not establish preservation. A [Kernel call](../spec/ir/kernel.md)
remains ordered even when the enclosed function denotes total mathematics.

## One operation across representations

Boolean literals illustrate an actual overlap. A reached literal materializes a
runtime value and charges execution; both logical and physical profiles have
that same meaning. They therefore share `local.bool_constant`. Physical selection
changes its result from `i1` to the native Boolean representation in place. The
operation verifier admits those two representations and the enclosing profile
independently enforces which one is legal. The artifact has one Boolean record.

Keeping two operation classes would duplicate producer and reader cases without
adding a semantic boundary. Using `arith.constant` instead would grant purity
and transformations that may remove or move reached work. MLIR distinguishes
[effects and speculation](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/);
zkc's ordered execution operations deliberately do not grant those freedoms.

This consolidation preserves independent validation. The physical reader checks
the actual operation, value, site, operands and selected result types. Export
checks the actual executable body against the serialized program. Neither reader
accepts a removed spelling as a compatibility alias.

## Implementation and physical decisions

A retained `ImplementationPlan` owns the meaning-to-realization edge. Physical
binding and storage decisions refer to that owned subject rather than owning a
second copy of numerical semantics. Source identity and actual selected payload
remain separate from the decisions that select ports and installed operations.
The independent checker still reads the payload; an implementation record is not
proof that its contents preserve the source.

Current native providers already exercise the managed invocation boundary.
Another generic invocation layer or speculative C ABI would duplicate that
responsibility. The current cost is maintaining the supported numerical readers
and provider realization rules. Generated-code deployment would require its own
representation, authority, resource and target qualification; dialect composition
alone does not establish those contracts.
