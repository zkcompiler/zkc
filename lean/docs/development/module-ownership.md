# Module ownership and reusable installations

Choose a module by the facts it depends on, not by the first protocol that used
it. The [architecture](../architecture.md) defines the four package boundaries
and six security responsibilities. These boundaries are enforced by
`ZkcTools.DeclarationAudit`; Lean and Python consume the same dependency policy.
No dependency exception is needed for the module layout.

## Three units of reuse

1. **Family mathematics.** A theorem quantifies over a field, abstract verifier,
   relation or reference calculation. Put deterministic mathematics in
   `Zkc.Protocols`; probability and family security contracts belong in
   `ZkcSecurity.Families`. For example,
   `ZkcSecurity.Families.Sumcheck.Contract` imports no concrete source artifact.
2. **Source-template installation.** A theorem accepts checked definitions, a
   body-membership law, domain interpretation, representation relation or layout.
   It installs the mathematical result on that source template. Deterministic
   Sumcheck helper equations live in `Zkc.Protocols.Sumcheck.Source`; security
   installations live in `ZkcSecurity.Bindings.Sumcheck`. Reusable GKR encodings,
   layout relations and round installations live in `ZkcSecurity.Bindings.Gkr`.
3. **Concrete application.** A proof selects an exact exported payload, Entry,
   model or claim. Put it in `ZkcExamples` or `ZkcSecurityExamples`. Generated
   payloads, catalogue selections and receipts are applications too.

A familiar algorithm is not automatically an application. A helper equation
that accepts an arbitrary checked helper table is reusable; a theorem fixing
the same algorithm to one generated table is a concrete application. Split a
mixed file at that boundary. Application modules may use installations; an
installation cannot import the application to obtain a convenient helper law.

For a new protocol, first reuse the family contract and any matching source
installation. Supply only the new mathematics, representation laws and actual
body associations they require. The component builders consume those facts and
produce checked derivations. They do not establish new mathematical invariants
merely because a source template has been recognized. The
[component authoring guide](component-authoring.md) describes these obligations.

## Tools and import phases

Place elaborators, tactics, printers and certificate builders in `ZkcTools` or
`ZkcSecurityTools`. Their proof output is checked against ordinary definitions
and theorems owned by the reusable libraries. An ordinary law needed by both
execution and a tactic belongs in the reusable library, not inside the tactic
module.

Lean's `public import`, `public meta import` and `import all` have distinct
purposes. Export ordinary theorem APIs with `public import`; export tactic
implementations with `public meta import`. An audit traversing stored private
proof bodies must load each owning module with `import all`. A public import
of a facade does not replace this requirement. The header audit records all
three modifiers using Lean's own parser.

`ZkcSecurity.Families.Sumcheck` is a small theorem facade.
`ZkcSecurityTools.Components` exports the component tactics. Standalone Lake
consumers in `lean/clients/` check both phases through real path dependencies.
These facades expose current owners; they do not retain retired import paths.

## Module identity and declaration identity

A Lean declaration's namespace and its owning module are independent. For
example, declarations in `ZkcSecurity.Bindings.Models.PrimeField` keep their
`ZkcSecurity.Domains.PrimeField` namespace. Existing theorem identities and
statements therefore remain unchanged without aliases.

Generators carry import identities and declaration identities separately:
`moduleName` selects the output module and imports; `namespaceName` selects the
Lean namespace. Subject, ABI and model selections follow the same rule. A
consumer imports the current module and refers to the existing declaration.
There is no forwarding file under the retired module path.

Ownership, declaration-record coverage and author-cost classification use the
module recorded by Lean, not the declaration namespace. This matters for helper
laws originally proved under an example namespace but now owned by a reusable
source installation.

Lean can store equivalent, lazily generated equation proofs in several modules.
The audit inspects every stored version. If the merged environment attributes
a dependency to a forbidden owner, the audit checks its stored owners in the
consumer's actual import closure before deciding the edge. This avoids assigning
a library's equation proof to an unrelated test that realized the same equation;
every recovered owner must still satisfy the dependency policy.

## Extending the framework

- Add family mathematics without changing claim resolution or concrete roots.
- Add a source installation without selecting a closed Entry.
- Add a tactic or generator without granting it authority over the security
  meaning; its checked output supplies a proof of that meaning.
- Add an endpoint method above the fixed claim and operational interfaces.
  A knowledge method may justify the request's registered recovery function;
  it cannot replace that function with one chosen by evidence.
- Add an optional library adapter in its integration package. Core and security
  stay usable without ArkLib or Clean.

Update the package's exhaustive audit imports with
`python3 lean/checks/audit_imports.py --write`. Run the changed modules and
focused controls first. Package builds, dependency/axiom audits, statement-lock
comparison and affected reports provide the landing evidence. Moving a module
changes lock ownership metadata, never the protected statement or its hash.
