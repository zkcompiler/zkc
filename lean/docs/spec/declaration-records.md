# Stored declaration records

`zkc.declarations/0` is a checking artifact emitted by the maintained
[Lean tool](../../ir/Zkc/Tools/IR/DeclarationRecords.lean), not a program format or
security receipt. The first JSON line identifies selected module families,
module/declaration counts and provenance; each following line describes one
actual stored declaration. Public names, private constants, statements, body
references and axiom dependencies are inspected in the owning package environment.

The Python driver partitions incompatible executable roots into separate environments
and joins only the assigned modules. Every current owned source is enumerated; a
missing source or ambiguous stored provider fails. A fresh incremental build precedes
inspection. The optional `--records` input requires an exact source, dependency,
toolchain and checker receipt, rather than trusting an old success filename.

The emitter retains structural and explicit statement hashes, kind, owning module,
tags, dependencies and allowed-axiom information. Optional details describe the
actual statement, binders and premises generically. They do not infer protocol meaning
from binder names, reconstruct concrete receipts or decide source association.
Requested missing detail fails. Registry metadata may describe supported logical
schemas, but its endpoint list is empty until actual implementations are installed.

`claims.toml` states maintained published claims and their theorem citations.
`claims.lock.json` locks their package, module and statement hashes. The checker
rejects disappeared/private citations, changed statements, forbidden axioms and
stale generated documentation. These are regression controls; equal hashes do not
establish semantic equivalence when referenced definitions change.

## Change from the previous version-0 schema

The version remains zero under the repository policy. The emitter no longer produces
protocol-specific model-binder or receipt reconstructions. Details now have one
generic binder/premise form. The subject/report join, receipt-status command,
`zkc.subject/0`, `zkc.subject-evidence/0`, `zkc.assurance-report/0` and
`zkc.consumer-requirements/0` pipeline have been retired with their implementations.
No reader silently accepts an old report as a current native connection.

Native `zkc.source-claims/0` and its fixed request semantics remain unchanged.
Their native transport controls are independent of declaration extraction. No
compiled or executable security conclusion follows from a declaration record.
