# Application correspondence map

`zkc.application-map/0` records compiler-known application boundaries and value
associations. It is untrusted auxiliary data. It changes neither transcript
inputs nor cryptographic commitment preimages and grants no source connection.
Consumers check the retained source, actual candidate and map together. A map
from one candidate cannot authorize another candidate with a compatible type.

The root has exactly these fields:

| Field | Shape and meaning |
|---|---|
| `format` | `zkc.application-map/0` |
| `source` | `{format, digest, entry}` identifying the retained original |
| `candidate` | `{format, digest}` identifying the actual selected output |
| `applications` | Materialized application occurrence forest in source preorder |
| `instructions` | Complete selected candidate instruction association in traversal order |

Digests use the exact byte/hash construction of the named artifact format.
They have the `sha256:` prefix and 64 lowercase hexadecimal digits. This map
does not redefine source hashing or substitute a reprinted byte string.

The foundation producer maps retained applications between the original and
prepared structured-source views, both `zkc.structured-source/0`. Each view is
derived from its actual supplied MLIR artifact under that schema's complete
admission rules, and both select the same entry. Paths below address logical
rows in those views; they are not paths through raw MLIR blocks. An unsupported
source or candidate carrier refuses instead of guessing an address projection.

Scoped Func/CF bodies can have multiple blocks. Their structured export already
checks the actual scope, outcome, stop and transfer edges before emitting a
logical block or closed region. This map consumes those checked associations;
it cannot omit an arbitrary CFG block or invent an instruction for administrative
plumbing. Independent admission and actual-candidate comparison still check the
complete native bodies, including dormant definitions. Downstream projection
and byte associations retain their owning contracts; this map alone makes no
connection from a logical row to an arbitrary native instruction.

Each application is exactly:

```text
{id, parent, source_definition, source_path, callee,
 roles, arguments, results, written}
```

`id` is its zero-based table ordinal as a canonical decimal string. A root's
parent is null; every other parent is an earlier application. `source_definition`
and `callee` resolve in the complete original declaration inventory. Each root
names an actual materialized protocol definition, with equal source definition
and callee and an empty path. Roots follow original declaration order; nested
expansions follow the source body's preorder. The selected entry must occur.

A region path alternates instruction and region ordinals, starting at the
definition's body; the empty region path is that body. An instruction path
appends its instruction ordinal. The ordinal equal to a block's instruction
count selects its terminator. These paths select actual rows, not labels or
printed SSA names. Non-root application paths select the actual source call in
the parent's callee, and its named callee must agree. Repeated expansions of a
helper have distinct parents/paths. A helper retained as a shared callable is
not falsely described as an expanded body; its call and definition remain
direct source associations below.

`roles` is the ordered list of `[callee_role, caller_role]` associations, covering
the complete callee roster. It is empty for role-free helpers. Role ordinals
are relative to their own declarations; same-spelled role names do not imply
the same role. `arguments` and `results` contain ordered `[callee_port, Value]`
rows for every logical port, including zero-storage logical ports where the
owner's layout preserves them.

At a root, roles and arguments are the identity association, and results name
the actual values returned by that definition's structured outer terminator.
For an expansion, arguments resolve to the actual source call operands and
results to that call's ordered results in its parent's lexical body. A
signature-compatible replacement is insufficient. A profile without a unique
structured outer return must first provide its owning structured correspondence;
this map does not guess a result from one CFG exit.

```text
Value = {definition, region, producer, components}
producer = ["argument", argument-ordinal]
         | ["result", instruction-ordinal, result-ordinal]
```

`region` identifies the actual lexical source region by the same path rules.
`producer` identifies a specific block argument or instruction result, rather
than a context index that changes when results are prepended. The checker
resolves the source's actual operand reference to this producer at that
occurrence. `components` is the ordered logical field/component path, empty
for a whole value. Captures must resolve through the retained source association;
an ordinal is never interpreted in an unrelated caller environment.
The checker rederives the complete type, role and custody of each association.
Swapping same-typed arguments must fail even if signature verification succeeds.

`written` is null when the original has no checked frontend association;
otherwise it is `{subject, node, instance}` using the frontend-owned written
source and closed-instance identities. This optional navigation link never
manufactures source-elaboration evidence. A diagnostic Location is not a
substitute for any semantic identity in this map.

Each instruction association is exactly:

```text
{target_definition, target_path, application, source_definition,
 source_path, purpose}
```

The target pair selects the actual candidate logical instruction or terminator.
`application` selects its containing expansion, or is null for a retained
shared/dormant definition. `source_definition` names the actual original
definition and agrees with the expansion's callee when an application is
present. `purpose` is `source` or `auxiliary`. A `source` row has its actual
source path; an `auxiliary` row has null source path and requires the owning
transformation's independent rule for that actual instruction. Calling an extra
query or guard auxiliary cannot make it legal. Every target instruction and
terminator is accounted for once, including nested regions and unused
definitions; missing, duplicate and extraneous rows refuse. A direct association
of a shared helper body makes no claim that its invocations have one occurrence.

Static application paths remain distinct from runtime loop coordinates. A loop
invocation reuses a static path with explicit dynamic coordinates supplied by
the execution occurrence contract. The map never erases those coordinates from
a random-oracle key or merges two service roots. Linear spans and reference
offsets are optional internal compression, not a wire assumption or a theorem
of arbitrary relocation.

The byte limit is 32 MiB, JSON depth at most 64, application and instruction rows
at most 100,000 each, and aggregate metadata traversal at most one million
units. Paths have at most 64 ordinals. All ordinals are canonical decimal
strings and must resolve within their owning inventory. Duplicate JSON keys,
unknown fields, forward parents, cycles, invalid paths and mismatched source or
candidate identities refuse. No acceptance bit or producer certificate field
exists. This schema makes the checking inputs explicit; independent formal
interpretation and a relocation theorem remain separate work.

## Native API and command profile

`zkc/Compiler/ApplicationMap.h` exposes `produceApplicationMap` and
`checkApplicationMap`, taking exact original bytes, exact candidate bytes, the
entry and an MLIR context. The public commands are:

```text
zkc-compile protocol-application-map ORIGINAL.mlir PREPARED.mlir --symbol=NAME
zkc-compile protocol-check-application-map ORIGINAL.mlir PREPARED.mlir MAP.json --symbol=NAME
```

The implemented edge accepts unsimplified preparation, including protocol and
pure helper expansion, retained shared helpers, actual input/output role
restrictions, nested repeats and scoped computations. `zkc-preparation-pipeline`
with `simplify=false` produces candidates for this profile. The map's independent
checker also runs native prepared-value comparison and checks retained native
bodies; equal exported rows cannot hide a changed administrative CFG.

Every association is a whole logical value (`components` is empty), and
`written` is null because these APIs receive no checked frontend association.
Role restrictions inserted at application ports are the only supported auxiliary
rows. Arithmetic folding, CSE, polynomial realization and selected construction
start insertion need explicit independently checked rules before joining this
profile. Unsupported candidates refuse, including those that another owning
native transform can validate. This limit grants no fallback or weaker check.

The source uses the `Original` structured export profile. The candidate uses
`Prepared`, which admits materialized occurrence sites up to 4096 bytes while
retaining all other original metadata bounds. This is a bounded view of the
candidate, not authority for its preparation; the map checker independently
checks each expanded occurrence and its source-relative path.
