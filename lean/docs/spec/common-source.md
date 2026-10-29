# Derived Common scalar views

The independent Common frontend is retired: there is no `zkc.common-source/0`
admission, flat Common program AST, `common-source` executable or
`protocol-lean` native export. Their former admission and lowering claims have
been removed; a renamed claim does not stand in for them.

Maintained Common scalar source clients consume the [Structured source
model](structured-source.md). Strict constructor serialization preserves the
actual original-stage export. Lean-owned phased admission checks the complete
unit, its typed participant bodies, role visibility and input/output rows.

`Zkc.Source.Common.Vocabulary` and `Scalar` supply mathematical contract
vocabulary, not an independently admitted source. `Structured.CommonAdapter`
projects typed participant actions to that vocabulary. It refuses unsupported
message sorts, and its embedding/projection law preserves every continuation and
stop. Concrete source clients prove equations for their actual Structured
participant followed by this projection.

Lean's present-input printer emits a literal normal form, its checked complete
returned-row equation and actual input constructors. It covers the explicit
availability pattern, not arbitrary optional input rows. Separate input controls
retain absent-input behavior. The mathematical Schnorr, Sumcheck and
factor-opening properties retain their existing honest/adversarial experiments,
causality and algebraic premises. No native correctness or security follows from
source admission alone.

[The bridge guide](../../bridges/common/README.md) specifies request generation,
fresh expected subjects, relation selection, transitive axiom checks and bounded
native-reference comparisons.
