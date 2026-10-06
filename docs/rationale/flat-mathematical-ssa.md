# Mathematical computations use flat SSA

The [closed mathematical protocol profile](../spec/profiles/compiler/mathematical-protocols.md)
represents total computation directly in ordinary SSA. Declared role sets live
on protocol interfaces and explicit restrictions. Availability is derived from
the current operations and operands.

## Alternatives and reason

An isolated `compute` region places ordinary algebra inside an explicit
capture/result boundary. It can be useful when a consumer needs an independently
replaceable region. It also hides outer facts from generic inner-body passes
unless a pattern propagates them through captures. Projection must map captures
and yields when slicing individual results.

A transparent region can use dominating outer SSA values, so isolation's
optimization cost is not a property of regions in general. Structured regions
remain suitable for loops, branches and other meaningful boundaries. MLIR's
[region semantics](https://mlir.llvm.org/docs/LangRef/#regions) support both forms.

Named functions already provide reusable mathematical definitions and multiple
results. For closed straight-line protocols, flat SSA avoids a mandatory
wrapper operation and capture/yield machinery without losing an established
consumer requirement. This is a simplicity choice; it does not establish that
flat SSA is optimal for every future client. Native folding and helper
optimization support are recorded separately in [status](../status.md).

Ordinary data types plus role interfaces describe the current pointwise value
families. Located types could encode role restrictions, but still need role
binding, substitution and communication semantics. Explicit restrictions are
checked formation boundaries and introduce no runtime state transition.
Availability establishes computability, not public agreement or secrecy.

A separate persistent mathematical graph would duplicate MLIR's ownership and
require synchronization of operands, symbols, locations and transformations.
Transient dependency and demand maps contain derived facts without that second
representation. Participant programs remain a distinct execution IR.

## Reopen when

Reconsider region granularity when pure loops, replacement interfaces or
protocol composition require a boundary with a concrete consumer. Compare the
same client in the plausible forms, including transparent regions. Reconsider
role representation if availability becomes an information-flow or placement
policy. Reconsider a located common stage if an important analysis needs to
rewrite selected role components before participant projection; a fact true at
one role cannot justify replacing a whole common SSA family.
