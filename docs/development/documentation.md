# Maintaining documentation

Write for one reader task or subject. Keep each definition in one place; another
explanation should add an application, example or useful level of detail and
link to the rule's owner.

## Choose a home

| Content | Home |
|---|---|
| Purpose and reading routes | Root README and `docs/README.md` |
| Native component responsibilities | `docs/architecture.md`; compiler/runtime guides for detail |
| Implemented capabilities and limits of support | `docs/status.md` |
| Native contracts and shared mathematical laws | `docs/spec/` |
| Source authoring and library use | `docs/language/`, `libraries/`, `examples/projects/` |
| Host use, CLI and application integration | `docs/runtime/` |
| Compiler representations, checks and lowering | `docs/compiler/` |
| Evidence policy and remaining native trust | `docs/assurance.md` |
| Public sequencing and extension triggers | `docs/roadmap.md` |
| Consequential adopted choices | `docs/rationale/`; brief reasons stay beside their owner |
| Independent Lean models and definitions | `lean/docs/spec/` and its model guides |
| Exact theorem scope and clause mapping | `lean/docs/support.md` and `lean/docs/correspondence/` |
| Formal architecture and adopted choices | `lean/docs/architecture.md` and `lean/docs/design/` |
| Builds and component procedures | `docs/development/` and adjacent component READMEs |
| Test selection and bounded native evidence | `common/tests/README.md`, `common/tests/native.md` |
| Research proposals, review logs and originals | Private research repository |

The [native index](../README.md) and [formal index](../../lean/docs/README.md) state
authority. Placement follows reader tasks and semantic ownership, not every
source directory or completed implementation package. A native reference test
and an independent formal model are different evidence; name which one applies.

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
build result. Follow the [assurance policy](../assurance.md). Measurements must
record the revision, dependency locks, tool versions, machine, inputs, repetitions
and statistic. Identify the measured stages and report failures and resource
ceilings alongside successful runs. No benchmark campaign is currently maintained.

For executable instructions, state the working directory, prerequisites,
required inputs and expected result. Distinguish a development command that
builds prerequisites from a driver that requires existing outputs. Link to the
[test scope map](../../common/tests/README.md#coverage-and-ownership) rather than maintaining a
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
shortening explanations. Changes to source-language or carrier contracts must move with their actual
implementation consumers. Independently formalized models retain their own
subjects and require an explicit correspondence to support native claims.

## Writing specifications

### Structure

1. Define each object and its meaning directly. An obligation to supply a
   definition does not replace the definition of an adopted concrete profile.
   A parameterized interface is complete when its parameters and required laws
   are explicit; it need not select one implementation of those parameters.
2. Introduce a concept briefly, give its definition or rules, and add an example
   when it helps. Use descriptive titles. Do not impose the same subsection
   template on every topic or make old review IDs the reading structure.
3. State types, binding, quantifiers, assumptions and applicable domains.
   Define failure, empty cases and boundary behavior where they affect meaning.
   Reuse a named definition rather than restating it with a changed meaning.
4. Use grammar for syntax, judgments for validity, equations for mathematical
   computation, and precise algorithms for decoding or transition procedures.
   A declarative judgment need not prescribe its checking algorithm. Lean or
   MLIR syntax is not required to understand a general definition.
5. Distinguish definitions, derived properties and implementation requirements.
   Normative definitions and requirements remain normative without capitalized
   keywords. Mark examples and explanatory notes as informative; they add no
   independent requirement. A theorem statement is not its proof receipt.
6. Use `MUST`, `MUST NOT` and `MAY` for explicit implementation obligations and
   permitted choices, naming the responsible implementation or interface.
   Prefer ordinary declarative prose for mathematical definitions. Avoid
   unbounded recommendations where interoperability needs an exact rule.
7. Separate common objects and laws from selected profile parameters and
   restrictions. A profile gives its exact interpretation, accepted domain,
   format and failure behavior. An unselected extension stays outside adopted
   scope rather than receiving an invented default.
8. Keep design alternatives, research, historical decisions, proof inventories
   and implementation progress in their existing external homes. Retain semantic
   limits beside the definitions they qualify. When definitions move, update
   incoming references and Formal correspondence to their actual new homes,
   including every part of a split definition. Remove superseded files and
   navigation-only sections after checking those references. Historical receipts
   retain their original hashes and validation scope.

### Tone and notation

Write English in the present tense, using direct, neutral sentences. Prefer
"is", "consists of", "is defined by", "returns" and "evaluates to" when
describing objects and behavior. Use "if and only if" only for a definition or
an established equivalence, not for a sufficient checker condition.

Explain a symbol at its first use or cite the precise earlier definition.
Use one name consistently. Equations and their accompanying prose describe the
same model. Resolve a disagreement through review of the intended definition
and its Formal counterpart; neither implementation convenience nor a theorem
about another subject settles it automatically.

Keep paragraphs focused. Tables suit constructor signatures and parallel
constraints. Examples stay short and exercise an informative case such as a
failed continuation, ordered operand mismatch or repeated factor. Avoid repeated
status disclaimers, dense ownership preambles and a separate miniature checklist
after every definition.

## Validate a documentation change

From the repository root:

```sh
just test-docs
git diff --check
```

The [checker](../../common/tests/check_docs.py) checks local inline links, heading fragments,
whitespace, public/private boundaries and reachability from each reference's
index. `just test-docs` uses `--all` to include component and fixture guides. It
does not verify mathematical truth, external websites or commands in code blocks.

Review the reading path as well as individual pages. Run changed commands at a
bounded relevant scope when prerequisites are available, and record commands not
exercised. A prose or link change does not require a compiler or Lean rebuild.
