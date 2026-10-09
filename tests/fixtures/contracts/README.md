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

`attribute-admission.json` is an independently authored set of 81 input/outcome
witnesses. It is not generated from TableGen, either registry, or a production
validator. The C++ driver calls the binding overload of `checkParameters`; the
Rust tools example constructs one retained local operation in Program/2 and
calls `admit_supplied` with the installed native backend. Positive controls
ensure an unrelated carrier or backend refusal cannot satisfy a negative case.
Operation attributes are positional strings; keyed objects, duplicate request
keys and extra request keys are separate transport refusals. Cases cover empty
and extra attributes, four prime-field p-1/p boundaries, canonical naturals,
u64 limits, vector/index extents, matrix dimensions, transpose and digest syntax.
An index equal to a field-array length is admitted statically: actual value/index
bounds are a separate execution check.

Origin templates are independently framed from literal string/array trees in
the Python suite. Both semantic readers see the same bytes. Oversized origin
strings hit Program's independent string ceiling before attribute validation;
the test preserves that distinction. Drift controls perturb a value passed to
the real C++ checker and a real backend AttributeRule while preserving ports.
The latter must refuse with the runtime's Backend admission category.

Share witnesses compare actual C++ `nativeTypePolicy` against actual Rust Entry
`Package::capture` / `Interface::read` admission. The test constructs input
metadata, nested records/sequences/variant arms, setup selectors, nominal custody
and role placement. It supplies no shared normative permission or custody enum.
Native formation, Share and Entry schema availability are separate observations:
fixed vectors can have Copy while lacking Share, and a bare fixed vector is not
an Entry builtin schema. Custody permits single-role metadata without conferring
Copy or multi-role placement. A deliberate native Share drift must disagree with
the unchanged Entry reader.

The Rust example lives in zkc-tools solely to access the existing Entry admission
API; no test-only validator is exposed as a production API. Its inert authenticated
package establishes metadata admission only. Source correspondence, actual input
decoding, setup authority and runtime value/capability checks are outside this
suite. The minimal operation programs are admitted, not executed.

There is no Lean driver, source program, table executor or compatibility reader
in this suite. A logical polynomial table value remains a native numerical
type; checking its kernel signature does not retain the retired table executor.
These checks establish bounded signature observations, not kernel arithmetic
correctness or cryptographic security.
