# Shared program foundation

`zkc_program` owns the deterministic, dialect-parametric program substrate used
by the concrete `zkc` IR package and the independent `protocol_proof` framework.
It depends only on the coordinated Lean/Std toolchain, currently Lean 4.35.0.

| Module | Existing declarations |
|---|---|
| `ZkcProgram.Execution` | `PIR.Process`, outcomes, complete execution, state and ordered events |
| `ZkcProgram.Interpretation` | Effect substitution and deterministic semantic equations |
| `ZkcProgram.MonadExecution` | Stateful monadic execution with explicit terminal stops |
| `ZkcProgram.Interaction` | Legal interface histories and interaction bounds |
| `ZkcProgram.Region.Context` | Typed values, references and environments in `Zkc.Source` |
| `ZkcProgram.Region.Operations` | Generic context operations in `Zkc.Source` |
| `ZkcProgram.Region.Basic` | Dialect-parametric Region syntax, denotation and renaming laws |

`ZkcProgram` exports these modules. The `PIR` and `Zkc.Source` declaration
namespaces are preserved, with one definition and no retired-path forwarding
modules or aliases. Concrete dialects, readers, operation meanings and compiler
correspondence belong to `Zkc`. Probability, security contracts and proof
construction belong above this package.

Run `lake build` in this directory to build the entire package. The downstream
core target `lake build +Tests.ProgramAudit` audits all stored shared
declarations, including private bodies, without introducing a core dependency
here. From the repository root, run
`python3 lean/checks/check_library.py --main-only` and
`python3 lean/checks/check_package_ownership.py --main-only` for import,
manifest and Lake-provider checks. `python3 lean/checks/audit_imports.py --main-only --write`
maintains the exhaustive shared audit.
