# Native contract conformance

`coverage.json` assigns the installed declarations and type constructors to
bounded closed-argument probe families. An added or retired declaration must
update this inventory explicitly. `facet-policy.json` records each consumer's
observable fields and the subset that can be compared.

The root conformance suite queries C++ Contracts, Rust admission and the native
backend independently. Registry discovery is local to each executable. It
compares logical/physical signatures, default representations, structural
permissions, implementation alternatives and malformed requests. Independent
signature witnesses and deliberate `field.add` resolver drift controls guard
against agreement caused only by a shared inventory mistake.

There is no Lean driver, source program, table executor or compatibility reader
in this suite. A logical polynomial table value remains a native numerical
type; checking its kernel signature does not retain the retired table executor.
These checks establish bounded signature observations, not kernel arithmetic
correctness or cryptographic security.
