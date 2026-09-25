# Inputs and captures

Input binding constructs a program's ordered environment from actual supplied
values. An access interpretation additionally determines which values the
executing role may read. Binding includes every declared argument and capture,
even when a particular execution does not use it.

## Capture lifetime

A mathematical environment binds values. Marking a [named declaration](../profiles/source/named-inputs.md#declarations-and-supplied-values) `capture` does
not make a mutable native pointer an immutable value. A realization of an
immutable capture MUST preserve the captured value for its declared use period.
A realization using a live reference instead supplies an explicit interpretation
and state/lifetime contract for that reference.

The pure expression profile's [issuance rule](../profiles/source/expressions.md#issuance-and-actor-admission)
retains a body and its evaluated capture values. Invocation uses those retained
values. That profile rule does not require every domain value to be copied;
other representations establish their own value and lifetime correspondence.

## Source selection and release

[Equal-view laws](../profiles/source/named-inputs.md#equal-permitted-views) fix the source. They do not constrain an external
generator that selects different syntax from a secret. A source-selection
claim binds the same source or establishes the actual selection tree's input
and view law, including guards and all declared branch captures under that
frontend's admission policy.

An actor's permitted view may include its private input. Equality under that
view does not authorize public release of outputs, code, captures, diagnostics,
digests or receipts. Released artifacts and runtime observations are interpreted
jointly under the selected [release relation](../properties/disclosure.md) and property
experiment.
