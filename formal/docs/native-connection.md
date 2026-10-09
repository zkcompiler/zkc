# Native connection boundary

The formal library and native implementation have distinct subjects. Existing
source, direct-plan, table and protocol theorems do not validate `.zkc`,
`zkc.program/0` or the Rust Runner. The
[assurance policy](../../docs/assurance.md#native-correspondence) owns requirements for
a connection; the [roadmap](../../docs/roadmap.md) owns its sequencing.

## Existing formal components

| Component | Reusable law and remaining boundary |
|---|---|
| [Execution](../Zkc/Semantics/Execution.lean) | `replacement_then` and `run_related` preserve modeled executions under their operation premises; native instances remain to be supplied |
| [Simulation](../Zkc/Realization/Simulation.lean) | Heterogeneous values related at actual final states, stops and projected events; native decoder/storage and progress obligations remain |
| [Input binding](../Zkc/Compiler/InputBinding.lean) | Actual input selection and coverage in a stated refinement domain; native source capture and parser adequacy remain |
| [Guarded compilation](../Zkc/Polynomial/Bilinear/Compilation.lean) | Preparation/analysis simulation up to readiness refusal under reached-call premises; no native pass theorem |
| [Judgments](../Zkc/Properties/Judgment.lean) | Conditional evidence and requirement composition; not a portable proof artifact for arbitrary native code |

[Support](support.md) owns the complete theorem inventory. References to these
components identify possible proof ingredients without prescribing native IR
layout, extraction tools or certificate formats.

## Checking in the current formal model

A formal transformation rule fixes source, candidate, semantic relation and
requirements. Its soundness theorem justifies accepted checks under those
requirements. The candidate cannot choose a different source merely by carrying
a source label. [Refinement](../../docs/spec/verification/refinement.md) and
[artifact binding](../../docs/spec/realization/artifacts.md) define these obligations.

The model-specific tools parse and check their own admitted formats. Kernel
replay of a conclusion, execution of a compiled checker, and native differential
tests have different trust boundaries. The current native validators perform
bounded comparisons but are not proved instances of these formal rules.

## Scope of a future claim

The first connection must fix an actual native source/artifact, input and state
relation, provider behavior, observation boundary and capacity premises. Complete
outcomes include stopped prefixes and residual state. Backend laws, parsing,
build/loader identity and downstream execution must be proved or explicitly
trusted at their stated scope. Protocol security additionally needs its own
experiment and property transport.

Implementation routes remain research choices. No generated-code, extraction or
whole-runtime verification architecture is selected by this reference.
