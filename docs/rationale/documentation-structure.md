# Documents are placed by role first and by semantic subject second

Every document has one home, chosen first by what the document does and then by
its subject. The [index](../README.md) is the reading map. The
[specification](../spec/README.md) defines adopted objects, judgments,
semantics and correspondence requirements, and orders its chapters by semantic
subject and dependency. A common law is defined once, and each application
cites it with its actual premises. Review, research and planning records are
development notes and stay outside this reference; a finished study reaches it
as the design it produced, with a rationale record where a choice needs one.

The [placement guide](../development/documentation.md#choose-a-home) assigns
each kind of content its home. Project-wide orientation stays at the document
root; development instructions and conventions share one contributor entry.
Normative contracts, authoring instructions, semantic explanations and
implementation references have distinct responsibilities even when they
describe the same operation.

Authoring, compiler internals and host execution have separate reading routes.
Realization laws are explained in the semantic guides; runtime architecture
belongs beside execution. Relocations update incoming references, including
Formal documentation, without keeping a duplicate or redirect at the old path.
The entry map follows reader tasks. Component READMEs own local API and campaign
instructions; the development guide links to them instead of copying their
command lists. Long alternative comparisons belong in rationale records so the
architecture can explain the selected system directly.

## Alternatives

**Domain chapters only.** Keeping each definition beside its discussion in
`pir/`, `properties/`, `compiler/` and `realization/` avoids nesting. It leaves
the difference between a requirement, a choice and a proved result to be read
paragraph by paragraph, and it splits the shared execution, observation and
composition laws across the domains that apply them. A separate `spec/` makes
the normative scope visible and comparable with the Lean library. It is not a
second copy: the domain chapters explain and apply definitions that `spec/`
owns.

**One monolithic formal specification.** A sequence of broad chapters obscures
subjects that change independently and makes each application hard to maintain
on its own. The specification uses the smallest substantive chapters, stable
clause references and
[correspondence maps](../spec/correspondence/core.md) that distinguish
definitions, theorems and obligations.

**Create the anticipated domains in advance.** A foundation area, a relations
area or a lower-level representation could each receive an empty home. An empty
normative page has no reviewed content, and reviewed content is what
establishes a chapter's readiness. A mixed chapter moves only with its common
and profile-specific meanings preserved.

**Mirror the Lean directory tree.** Lean imports follow mathematical
dependency; prose follows subject and reading order. The correspondence maps
connect clauses to actual declarations, hypotheses and evidence without forcing
the two trees to match. A mismatch is adjudicated: neither matching text nor a
proof about a different object establishes adequacy.

## Reopen when

A subject accumulates reviewed definitions whose dependencies fit none of the
specification's parts, so that it needs a reference of its own; or one
definition has to be maintained in both `spec/` and a domain chapter to stay
readable.
