# F0-V2B1 bounded normalized owner-view grammar

This gate compiles one finite candidate source contract for the six normalized
PIR owner views and derives their values from the exact admitted F1-R1B Core
and Fresh Protocol handles. Its aggregate result is
`Affirmative/F0V2B1-A-BOUNDED-NORMALIZED-DERIVATION`.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-view-bodies-f0v2b1/run.py --check
```

The frozen 63-case result contains twelve affirmative bounded findings, five
`CannotAnswer` obligations, and forty-six refused mutations. The positive
fixture has:

- six source-compiled schemas and six owner-derived values;
- 329 active atomic leaves with exact complete manifests;
- two Prover decision points and seven guaranteed reads;
- one retained 21-node, 27-edge `PCGraph`, including its unique topological
  order, 7 `StaticPublic` and 14 `PublicHistory` classes, nine sinks, two
  acceptance sinks, and affirmative bounded eligibility;
- six occurrences, five values, exact Message/Check/Terminal backlinks, and
  direct Check-output predecessors; and
- one Fresh resolver plus completed-record descriptions for all six
  occurrence arities and two terminals.

`normalized-schema.json` is a bounded candidate source, not target PIR source.
It uses only Record, Variant, Sequence, and closed atomic leaves. Unsupported
B2 families are represented by maximum-zero sequences rather than permissive
placeholders.

The reference path recursively expands that source and algorithmically derives
the views. The clean-room path uses a worklist source compiler and a separately
written finite fixture oracle. The two paths separately load and admit the
F1-R1B owner model and agree exactly on the complete package and evidence.
They deliberately share the owner's canonical primitive body compilers; this
is owner-derivation diversity, not an independent K1 or Core encoder.

Mutations cover source/schema/catalog substitution, manifest omission and
aliasing, IDs, scope paths, binding types, decision backlinks and guards,
guaranteed reads, legal moves, graph edges/order/classes/sinks/eligibility,
Challenge fields, occurrence types, value predecessors, Message/Check/Terminal
backlinks, Fresh resolver and runtime typing, fixed laws, attempted B2-family
insertion, retained-Core mutation, and Protocol/Core handle substitution.

This package does not establish constructor-complete grammar or derivation,
general `PCGraph` transfers, target publication or migration, live zkc
implementation correspondence, proper-subset read closure, Q1 source
correspondence, compiler verification, or a cryptographic property.
