# Generic libraries and compilation choices

The compiler accepts constrained generic `.pir` definitions, partial
configurations and selected instances. Start with
[types, bounds and inference](reference.md#types-bounds-and-static-inference)
for syntax and [source projects](projects.md) for library use.
[Specialization](../compiler/specialization.md) and
[independent validation](../compiler/library-design/validation.md) describe the
compiler and checking boundaries.

zkc supports **constrained generic definitions, explicit semantic instances,
and independently selectable physical implementations**. A completely fixed
definition is the zero-parameter case. A partially configured definition is still
a family; an executable artifact must identify the choices on which its meaning
and execution depend. “Generic by default” means retaining unresolved parameters
under explicit requirements, not accepting every field, PCS, or machine.

Definitions, selected instances and runtime invocations have distinct roles.
A library need not commit its users to one backend profile. These features do
not introduce a second protocol language, a universal backend or an alternative
execution semantics.

## Selected rules

Static instantiation can remove generic dispatch, at real cost: requirement
checking, specialization and code growth, representation conversions, incomplete
search, and explicit proof or trust obligations. Replacing a field or PCS can
select a different protocol instance; replacing an arithmetic kernel can preserve
an existing instance. These are different operations even when both were
previously chosen by the same profile string.

| Question | Rule |
|---|---|
| Where do requirements live? | At exported definitions and deliberately parameterized modules; implementation variants add their own conditions |
| What does inference establish? | A conservative body requirement, checked against the public signature; it does not discover cryptographic truth |
| Which choices are interchangeable? | Those related under the selected semantic observation and resource contract |
| How are manual and automatic choices combined? | They restrict and rank the same admissible candidate graph |
| Does genericity require runtime overhead? | No inherent dictionary dispatch after closed specialization; equal total performance is not promised |
| What changes in the formal model? | New source and static semantics and instantiation obligations; the process and execution core is retained |

## Generic definitions and closed selections

Ordinary `module { ... }` authoring supports generic definitions and explicit
semantic and implementation bindings. The two supported BLS module headings
are notation conveniences: [interactive carrier admission](../compiler/carrier-consolidation.md#authoring-and-admission)
resolves their defaults before common admission. They are not a second runtime
profile interpreter. The same common carrier holds their explicit selected
contracts and fully qualified logical and physical ports.

The [frontend checker](../../compiler/lib/Frontend/Semantics/Check.cpp) resolves
source profiles and static requirements. The
[installed kernel catalog](../../compiler/lib/Contracts/Kernels.cpp) supplies
operation implementation selection. Rust checks original-source maps and actual
bindings; the independent source reference executes its supported typed regions.
Constructed artifacts have separate producer and validator processes. Automatic
selection search is outside the implemented carrier.

The finite direct route's
[`SourceLibraryInterface`](../../compiler/include/zkc/Interfaces/SourceLibrary.h)
registers closed families for that reference profile. It is an independent
extension boundary, not the API for source-level component libraries or open
parameterized interactive definitions. See [closed libraries](../compiler/libraries.md)
for its consumers and [projects](projects.md) for authored libraries. Further
extensions should reconcile shared contracts across these routes rather than
introduce a third unrelated registry. That is a design obligation, not a claim
that the current interfaces are interchangeable.

## The resulting architecture

```text
reusable definition + public signature
             |
   infer/check requirements
             v
generic typed library ---- explicit semantic bindings
             |            and admitted constructions
             v
selected protocol instance + residual runtime parameters
             |
     construction / participant projection
             v
participant algorithms + implementation candidates
             |
     fixed choices / rules / bounded search
             v
physical plan + exact implementation and codec bindings
             |
      executable admission
             v
Rust orchestration and external cryptographic implementations
```

This is a dependency order, not a demand to expand every body at each arrow.
Domains remain orthogonal to abstraction stages. Logical operations can survive
through participant IR until a justified implementation is selected. A compiler
may explore later choices early, but cannot erase semantic distinctions before
their consumers have checked them.

## Boundary

The architecture requires no general-purpose solver, full DSL, native autotuner,
or formal verification of external libraries. Those are separate capabilities with
their own acceptance criteria. Implementation extends the source carrier, artifact
formats and native admission while retaining the common process and execution
semantics.
