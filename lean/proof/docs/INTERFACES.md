# Public program and proof interfaces

## One public program, one probability interpretation

`PIR.Process I A` is the public effect tree. Its definition, terminal `Outcome`, full
`Execution S L A`, deterministic/monadic execution and substitution laws belong to
`ZkcProgram`. The shared package depends on Std only. Generic `Zkc.Source.Region`
and its dialect-parametric denotation are there too. Concrete opcodes and IR readers
remain owned by `Zkc`; this proof package does not import them.

`System E I S L` fixes normalized operation kernels returning complete executions and
an entire initial-state distribution. `System.run` returns a kernel of full executions;
`System.experiment` supplies the normalized whole experiment. `runFrom` additionally
accepts an already reached state and event prefix. Stops retain both and end execution.

`Internal.encode` maps Process into an upstream FreeM whose answers are `Outcome`s.
Only returned replies continue. `Internal.complete_execution` proves correspondence
with the shared monadic interpreter. `System.run_eq_dirac` and `runFrom_eq_dirac` prove
agreement with deterministic execution. FreeM and its backend contract calculus remain
internal implementation machinery, not a second public authoring path.

## Local-to-global proof interfaces

| Interface | Author supplies | Framework proves |
|---|---|---|
| `OperationSpec I S L` | A continuation transformer on complete outcomes and accumulated state | Common quantitative semantics |
| `UpperBound`, `LowerBound` | Local mathematics and indexed loop invariants | Bind, dependent branch, finite/nested iteration and consequence rules |
| `Installation` | Same-interface joint operation laws, state/history relation and initial coupling | Complete adaptive-execution transport |
| `Representation.contractOfMap`, `Installation.ofMap` | A total measurable representation and complete local/initial pushforward laws | Joint coupling, marginals, invariant and installation |
| `InterpretationContract` | Deterministic operation-to-Process implementation law | Contextual, nested and transitive full-execution correspondence |
| `ServiceInstallation` | Probabilistic local coupling between an operation and a fixed lower-level body | Substitution through every adaptive caller and both event-transfer directions |
| `ServiceInstallation.ofMap` | A measurable representation and local/initial law equations | The probabilistic service installation |
| `UpperEvidence`, `LowerEvidence` | Fixed subject, installation, mathematics, terminal implication and initial budget | The request's complete probability bound |
| `UpperTransfer`, `LowerTransfer` | Security reduction, admission, explicit loss and budget theorem | Property-correct transport and composition of losses |

Same-interface installation and differing-interface substitution are exact boundaries.
A security transformation can change the game and charge loss; its reduction theorem
is a separate mathematical obligation. Structural substitution does not prove such a
reduction. Shared state and challenges are retained, with no implicit independence rule.

Both loop rules quantify their invariants over returned and stopped outcomes. The bind
and loop APIs explicitly require the stopped-branch comparison. Upper and lower terminal
implications have opposite directions. Initial coupling covers the whole measure.

## Claims and evidence

The fixed property requests are in `Claims/`: promise soundness, unconditional
completeness, fixed recovery, bounded extraction, statistical/selected-observer simulation,
and explicitly custom propositions. Extraction/simulation programs use Process through
`AccessExecution`. Their request fixes the algorithm and permitted service interface.
`OperationCost` bounds weighted abstract calls uniformly over replies; it is not a CPU
cost or PPT adequacy theorem.

`Receipt claim` contains precisely `claim.Meaning`. A conditional receipt records its
actual premise and becomes closed only after that premise is proved. Provider identity,
proof search, syntax matching and attribution do not determine the meaning or status.

## Lean conventions

Semantic definitions needed for downstream conversion use `@[expose]`; mathematical
proof bodies and irrelevant implementation details do not need blanket exposure.
Type-index calculations use `@[implicit_reducible]` where needed. Modules use Lean 4.35's
module system, strict implicit arguments and warnings-as-errors. Public propositions use
capitalized names; computations and constructors use lower camel case.

Module paths identify ownership. Existing `PIR`/`Zkc.Source` declaration namespaces are
retained for the exact shared definitions, with no duplicate definitions, forwarding
modules or compatibility aliases.
