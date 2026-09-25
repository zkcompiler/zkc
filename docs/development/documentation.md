# Maintaining documentation

The [documentation index](../README.md) gives readers their entry points and states
authority. Write a document for one task or subject, and keep its definition in
one place. A second explanation should add an application, example or different
level of detail and link to the owner of the underlying rule.

## Choose a home

| Content | Home |
|---|---|
| Project purpose and reader orientation | Root README and `docs/overview.md` |
| Component responsibilities and their connections | `docs/architecture.md`; detailed designs beside their subject |
| Implemented capabilities and outstanding limits | `docs/status.md` |
| What a proof, checker, test or measurement establishes | `docs/assurance.md`; exact declarations and premises in the formal support/correspondence maps |
| Remaining engineering work and research triggers | `docs/roadmap.md` |
| Environment, commands, configuration and maintenance | `docs/development/`, starting at its `README.md` |
| Directory and dependency conventions | `docs/development/layout.md` |
| Definitions, judgments and mandatory conditions | `docs/spec/`, following its [writing rules](../spec/writing.md) |
| Authoring syntax, reusable source libraries and relation clients | `docs/language/` |
| Explanations of protocol meaning, execution, composition, properties and realization | `docs/guides/` |
| Compiler representations, analyses and lowering | `docs/compiler/` |
| Execution, backend use and concrete formats | `docs/runtime/`; exact representation laws in `docs/spec/realization/` |
| A design choice and its alternatives | `docs/rationale/`, following the [record rules](../rationale/README.md) |
| A component's API or a campaign's procedure | Its adjacent README, linked from the relevant guide |

Documentation follows reader tasks and semantic subjects; it need not mirror
the source tree. The [organization rationale](../rationale/documentation-structure.md)
explains this choice. Research notes, review logs, session history and backup
copies stay outside the public reference. Their durable results become the
appropriate definition, design, support statement or measurement summary.

## Keep claims and commands current

Distinguish implemented behavior from a selected design and from work still
needed. A statement that something is unsupported should name the missing
generality when a bounded implementation already exists. Link to current code
or a maintained guide; do not replace a mathematical condition with the
behavior of one implementation.

Keep exact tool and dependency versions in their manifests and lockfiles.
Documentation explains their ownership and records versions only when they are
part of a particular observation. A test count, elapsed time or memory figure
needs its execution scope and environment; a historical run is not a current
build result. Follow the [assurance policy](../assurance.md) and
[measurement guide](../../bench/README.md#reading-and-recording-a-measurement).

For executable instructions, state the working directory, prerequisites,
required inputs and expected result. Distinguish a development command that
builds prerequisites from a driver that requires existing outputs. Link to the
[test scope map](../../tests/README.md#execution-owners) rather than maintaining a
second list. Optional external integrations must say what makes them optional.

## Consolidate without losing a contract

Before removing a page, identify its unique definitions, assumptions, evidence
and incoming links. Move any unique content to its owner, update links and
heading fragments, then remove the duplicate. Keep a backup outside the public
tree when doing a substantial rewrite. Do not leave an archive or an empty
redirect page as another place readers must search.

Keep an exact concrete format in one reference and link its producers and
consumers to it. Directory placement does not change the meaning or authority of
a format. A relocation updates every consumer, including Formal documentation,
in the same change; a link dependency alone does not require a separate home.

Similar subject matter is not necessarily duplication. A specification clause,
a mathematical proof, an executable interface and a measurement have different
responsibilities. Preserve source coordinates and exact theorem premises when
shortening explanations. Changes to source-language or carrier contracts must
move with their implementation and formal owners.

## Validate a documentation change

From the repository root:

```sh
just test-docs
git diff --check
```

`just test-docs` includes component, benchmark and fixture guides by calling
[the checker](../../tests/check_docs.py) with `--all`. A direct call without that
option checks only the reference and root/formal guides. Both check local inline links, heading
fragments and whitespace, plus reachability of the `docs/` reference from its
index and the rationale rules. They do not verify mathematical truth, external
websites or commands inside code blocks.

Review the affected reader journey as well as the changed page. Execute changed
commands when their prerequisites are available, using a bounded relevant
scope; record any commands not exercised. A link-only edit does not require a
full compiler or Lean rebuild.
